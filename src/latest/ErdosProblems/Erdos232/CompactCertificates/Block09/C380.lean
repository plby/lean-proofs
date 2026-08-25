/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate380 : CompactCertificate where
  left := 251
  right := 252
  center := 503 / 2
  grid := fun i =>
    match i.val with
    | 0 => 80
    | 1 => 59
    | 2 => 95
    | 3 => 17
    | 4 => 46
    | 5 => 126
    | 6 => 92
    | 7 => 158
    | 8 => 117
    | 9 => 179
    | 10 => 103
    | 11 => 183
    | 12 => 171
    | 13 => 122
    | 14 => 139
    | 15 => 116
    | 16 => 102
    | 17 => 148
    | 18 => 82
    | 19 => 69
    | 20 => 43
    | 21 => 23
    | 22 => 63
    | 23 => 87
    | 24 => 37
    | 25 => 149
    | _ => 99
  point := fun i =>
    match i.val with
    | 0 => 503 / 2
    | 1 => 741015046794203 / 4000000000000
    | 2 => 239629041018299 / 800000000000
    | 3 => 216226342536721 / 4000000000000
    | 4 => 580814370804637 / 4000000000000
    | 5 => 1577024001220329 / 4000000000000
    | 6 => 1161628741609777 / 4000000000000
    | 7 => 1990470648076021 / 4000000000000
    | 8 => 1466171670403039 / 4000000000000
    | 9 => 2249484385364497 / 4000000000000
    | 10 => 1298740415427913 / 4000000000000
    | 11 => 2304637657893917 / 4000000000000
    | 12 => 2153291449738673 / 4000000000000
    | 13 => 1536690383041409 / 4000000000000
    | 14 => 1742443112413911 / 4000000000000
    | 15 => 1452667408304359 / 4000000000000
    | 16 => 1283475710219539 / 4000000000000
    | 17 => 372001286690361 / 800000000000
    | 18 => 1028975136340667 / 4000000000000
    | 19 => 872273618663587 / 4000000000000
    | 20 => 545828329596961 / 4000000000000
    | 21 => 293548291000287 / 4000000000000
    | 22 => 797040713341861 / 4000000000000
    | 23 => 1088290952961797 / 4000000000000
    | 24 => 460171670403039 / 4000000000000
    | 25 => 1870572292221119 / 4000000000000
    | _ => 1249455601282321 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (41142488161 / 1000000000000) (41142488162 / 1000000000000), orderedInterval (28876543796 / 1000000000000) (28876543797 / 1000000000000))
    | 1 => (orderedInterval (-37066280237 / 1000000000000) (-37066280236 / 1000000000000), orderedInterval (-45315458120 / 1000000000000) (-45315458119 / 1000000000000))
    | 2 => (orderedInterval (-44053551106 / 1000000000000) (-44053546042 / 1000000000000), orderedInterval (13661520291 / 1000000000000) (13661525355 / 1000000000000))
    | 3 => (orderedInterval (-107484509366 / 1000000000000) (-107484509363 / 1000000000000), orderedInterval (-13956153660 / 1000000000000) (-13956153657 / 1000000000000))
    | 4 => (orderedInterval (65909615390 / 1000000000000) (65909615401 / 1000000000000), orderedInterval (6115151856 / 1000000000000) (6115151866 / 1000000000000))
    | 5 => (orderedInterval (-28814687498 / 1000000000000) (-28814665543 / 1000000000000), orderedInterval (28044591622 / 1000000000000) (28044613577 / 1000000000000))
    | 6 => (orderedInterval (38778677653 / 1000000000000) (38778756602 / 1000000000000), orderedInterval (-26303655915 / 1000000000000) (-26303576965 / 1000000000000))
    | 7 => (orderedInterval (32043851154 / 1000000000000) (32043912408 / 1000000000000), orderedInterval (-15923242176 / 1000000000000) (-15923180921 / 1000000000000))
    | 8 => (orderedInterval (9840129176 / 1000000000000) (9840129208 / 1000000000000), orderedInterval (-40510277189 / 1000000000000) (-40510277156 / 1000000000000))
    | 9 => (orderedInterval (-24396613017 / 1000000000000) (-24396613016 / 1000000000000), orderedInterval (-23147969337 / 1000000000000) (-23147969336 / 1000000000000))
    | 10 => (orderedInterval (-42097557829 / 1000000000000) (-42097550999 / 1000000000000), orderedInterval (13795223989 / 1000000000000) (13795230819 / 1000000000000))
    | 11 => (orderedInterval (-29750682419 / 1000000000000) (-29750594845 / 1000000000000), orderedInterval (14852642161 / 1000000000000) (14852729735 / 1000000000000))
    | 12 => (orderedInterval (-32589923264 / 1000000000000) (-32589901542 / 1000000000000), orderedInterval (11007308197 / 1000000000000) (11007329919 / 1000000000000))
    | 13 => (orderedInterval (40450065863 / 1000000000000) (40450066879 / 1000000000000), orderedInterval (-4625383739 / 1000000000000) (-4625382723 / 1000000000000))
    | 14 => (orderedInterval (10766268705 / 1000000000000) (10766268745 / 1000000000000), orderedInterval (-36693824453 / 1000000000000) (-36693824413 / 1000000000000))
    | 15 => (orderedInterval (-19067644084 / 1000000000000) (-19067643278 / 1000000000000), orderedInterval (37300822754 / 1000000000000) (37300823559 / 1000000000000))
    | 16 => (orderedInterval (41698120388 / 1000000000000) (41698120390 / 1000000000000), orderedInterval (15597534154 / 1000000000000) (15597534155 / 1000000000000))
    | 17 => (orderedInterval (27329731760 / 1000000000000) (27329731761 / 1000000000000), orderedInterval (24913663133 / 1000000000000) (24913663134 / 1000000000000))
    | 18 => (orderedInterval (20198475238 / 1000000000000) (20198475239 / 1000000000000), orderedInterval (45422779393 / 1000000000000) (45422779394 / 1000000000000))
    | 19 => (orderedInterval (-47088129825 / 1000000000000) (-47088102269 / 1000000000000), orderedInterval (26604431206 / 1000000000000) (26604458763 / 1000000000000))
    | 20 => (orderedInterval (-57047381144 / 1000000000000) (-57047345332 / 1000000000000), orderedInterval (37771408240 / 1000000000000) (37771444052 / 1000000000000))
    | 21 => (orderedInterval (-87701704214 / 1000000000000) (-87701701819 / 1000000000000), orderedInterval (31951563348 / 1000000000000) (31951565742 / 1000000000000))
    | 22 => (orderedInterval (-48074614276 / 1000000000000) (-48074577448 / 1000000000000), orderedInterval (29848476446 / 1000000000000) (29848513274 / 1000000000000))
    | 23 => (orderedInterval (21513115442 / 1000000000000) (21513116650 / 1000000000000), orderedInterval (-43364775361 / 1000000000000) (-43364774152 / 1000000000000))
    | 24 => (orderedInterval (29767967845 / 1000000000000) (29767969552 / 1000000000000), orderedInterval (-68303142889 / 1000000000000) (-68303141182 / 1000000000000))
    | 25 => (orderedInterval (-11987344139 / 1000000000000) (-11987344138 / 1000000000000), orderedInterval (-34881897697 / 1000000000000) (-34881897696 / 1000000000000))
    | _ => (orderedInterval (-38239039674 / 1000000000000) (-38238975019 / 1000000000000), orderedInterval (24058008519 / 1000000000000) (24058073175 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13376943600 / 1000000000000) (13376943915 / 1000000000000)
      | 1 => orderedInterval (5621030070 / 1000000000000) (5621031662 / 1000000000000)
      | 2 => orderedInterval (-750545966 / 1000000000000) (-750544061 / 1000000000000)
      | 3 => orderedInterval (-3013333893 / 1000000000000) (-3013320838 / 1000000000000)
      | 4 => orderedInterval (4358938917 / 1000000000000) (4358939436 / 1000000000000)
      | 5 => orderedInterval (-1906682655 / 1000000000000) (-1906682621 / 1000000000000)
      | 6 => orderedInterval (-2421591999 / 1000000000000) (-2421589210 / 1000000000000)
      | 7 => orderedInterval (1061342524 / 1000000000000) (1061343527 / 1000000000000)
      | _ => orderedInterval (8329888232 / 1000000000000) (8329900444 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (12089414647 / 1000000000000) (12089415022 / 1000000000000)
      | 1 => orderedInterval (-2963879306 / 1000000000000) (-2963876824 / 1000000000000)
      | 2 => orderedInterval (-455140613 / 1000000000000) (-455136848 / 1000000000000)
      | 3 => orderedInterval (15353714008 / 1000000000000) (15353743389 / 1000000000000)
      | 4 => orderedInterval (-771837805 / 1000000000000) (-771836769 / 1000000000000)
      | 5 => orderedInterval (662594937 / 1000000000000) (662594987 / 1000000000000)
      | 6 => orderedInterval (-8067093000 / 1000000000000) (-8067090956 / 1000000000000)
      | 7 => orderedInterval (2886614427 / 1000000000000) (2886615230 / 1000000000000)
      | _ => orderedInterval (-514952650 / 1000000000000) (-514937480 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12501186485 / 1000000000000) (-12501186038 / 1000000000000)
      | 1 => orderedInterval (-5878103336 / 1000000000000) (-5878099442 / 1000000000000)
      | 2 => orderedInterval (3365952674 / 1000000000000) (3365960131 / 1000000000000)
      | 3 => orderedInterval (5658255502 / 1000000000000) (5658322241 / 1000000000000)
      | 4 => orderedInterval (-11454185601 / 1000000000000) (-11454183494 / 1000000000000)
      | 5 => orderedInterval (1948544789 / 1000000000000) (1948544861 / 1000000000000)
      | 6 => orderedInterval (1953869013 / 1000000000000) (1953870593 / 1000000000000)
      | 7 => orderedInterval (1095513945 / 1000000000000) (1095514612 / 1000000000000)
      | _ => orderedInterval (-14476660789 / 1000000000000) (-14476641869 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-12581351414 / 1000000000000) (-12581350883 / 1000000000000)
      | 1 => orderedInterval (7659121110 / 1000000000000) (7659127209 / 1000000000000)
      | 2 => orderedInterval (-786830725 / 1000000000000) (-786815979 / 1000000000000)
      | 3 => orderedInterval (-73592980510 / 1000000000000) (-73592828510 / 1000000000000)
      | 4 => orderedInterval (2588311903 / 1000000000000) (2588316237 / 1000000000000)
      | 5 => orderedInterval (-3482791355 / 1000000000000) (-3482791247 / 1000000000000)
      | 6 => orderedInterval (8549108064 / 1000000000000) (8549109328 / 1000000000000)
      | 7 => orderedInterval (-3860404307 / 1000000000000) (-3860403742 / 1000000000000)
      | _ => orderedInterval (-9509133274 / 1000000000000) (-9509109734 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (11104156461 / 1000000000000) (11104157094 / 1000000000000)
      | 1 => orderedInterval (12579201933 / 1000000000000) (12579211516 / 1000000000000)
      | 2 => orderedInterval (-14068441138 / 1000000000000) (-14068411915 / 1000000000000)
      | 3 => orderedInterval (-16192023033 / 1000000000000) (-16191675379 / 1000000000000)
      | 4 => orderedInterval (32663914856 / 1000000000000) (32663923883 / 1000000000000)
      | 5 => orderedInterval (925378981 / 1000000000000) (925379149 / 1000000000000)
      | 6 => orderedInterval (-2257357683 / 1000000000000) (-2257356637 / 1000000000000)
      | 7 => orderedInterval (-1785875784 / 1000000000000) (-1785875294 / 1000000000000)
      | _ => orderedInterval (28819954379 / 1000000000000) (28819983789 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (24655988830 / 1000000000000) (24656022254 / 1000000000000)
    | 1 => orderedInterval (18219434645 / 1000000000000) (18219489751 / 1000000000000)
    | 2 => orderedInterval (-30288000288 / 1000000000000) (-30287898405 / 1000000000000)
    | 3 => orderedInterval (-85016950508 / 1000000000000) (-85016747321 / 1000000000000)
    | _ => orderedInterval (51788908972 / 1000000000000) (51789336206 / 1000000000000)

theorem compactCertificate380_stateChecks0 :
    compactCertificate380.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (503 / 2)) (orderedInterval (41142488161 / 1000000000000) (41142488162 / 1000000000000), orderedInterval (28876543796 / 1000000000000) (28876543797 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (741015046794203 / 4000000000000)) (orderedInterval (-37066280237 / 1000000000000) (-37066280236 / 1000000000000), orderedInterval (-45315458120 / 1000000000000) (-45315458119 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (239629041018299 / 800000000000)) (orderedInterval (-44053551106 / 1000000000000) (-44053546042 / 1000000000000), orderedInterval (13661520291 / 1000000000000) (13661525355 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_stateChecks1 :
    compactCertificate380.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (216226342536721 / 4000000000000)) (orderedInterval (-107484509366 / 1000000000000) (-107484509363 / 1000000000000), orderedInterval (-13956153660 / 1000000000000) (-13956153657 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (580814370804637 / 4000000000000)) (orderedInterval (65909615390 / 1000000000000) (65909615401 / 1000000000000), orderedInterval (6115151856 / 1000000000000) (6115151866 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1577024001220329 / 4000000000000)) (orderedInterval (-28814687498 / 1000000000000) (-28814665543 / 1000000000000), orderedInterval (28044591622 / 1000000000000) (28044613577 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_stateChecks2 :
    compactCertificate380.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1161628741609777 / 4000000000000)) (orderedInterval (38778677653 / 1000000000000) (38778756602 / 1000000000000), orderedInterval (-26303655915 / 1000000000000) (-26303576965 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1990470648076021 / 4000000000000)) (orderedInterval (32043851154 / 1000000000000) (32043912408 / 1000000000000), orderedInterval (-15923242176 / 1000000000000) (-15923180921 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1466171670403039 / 4000000000000)) (orderedInterval (9840129176 / 1000000000000) (9840129208 / 1000000000000), orderedInterval (-40510277189 / 1000000000000) (-40510277156 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_stateChecks3 :
    compactCertificate380.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2249484385364497 / 4000000000000)) (orderedInterval (-24396613017 / 1000000000000) (-24396613016 / 1000000000000), orderedInterval (-23147969337 / 1000000000000) (-23147969336 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1298740415427913 / 4000000000000)) (orderedInterval (-42097557829 / 1000000000000) (-42097550999 / 1000000000000), orderedInterval (13795223989 / 1000000000000) (13795230819 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2304637657893917 / 4000000000000)) (orderedInterval (-29750682419 / 1000000000000) (-29750594845 / 1000000000000), orderedInterval (14852642161 / 1000000000000) (14852729735 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_stateChecks4 :
    compactCertificate380.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2153291449738673 / 4000000000000)) (orderedInterval (-32589923264 / 1000000000000) (-32589901542 / 1000000000000), orderedInterval (11007308197 / 1000000000000) (11007329919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1536690383041409 / 4000000000000)) (orderedInterval (40450065863 / 1000000000000) (40450066879 / 1000000000000), orderedInterval (-4625383739 / 1000000000000) (-4625382723 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1742443112413911 / 4000000000000)) (orderedInterval (10766268705 / 1000000000000) (10766268745 / 1000000000000), orderedInterval (-36693824453 / 1000000000000) (-36693824413 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_stateChecks5 :
    compactCertificate380.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1452667408304359 / 4000000000000)) (orderedInterval (-19067644084 / 1000000000000) (-19067643278 / 1000000000000), orderedInterval (37300822754 / 1000000000000) (37300823559 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1283475710219539 / 4000000000000)) (orderedInterval (41698120388 / 1000000000000) (41698120390 / 1000000000000), orderedInterval (15597534154 / 1000000000000) (15597534155 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (372001286690361 / 800000000000)) (orderedInterval (27329731760 / 1000000000000) (27329731761 / 1000000000000), orderedInterval (24913663133 / 1000000000000) (24913663134 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_stateChecks6 :
    compactCertificate380.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1028975136340667 / 4000000000000)) (orderedInterval (20198475238 / 1000000000000) (20198475239 / 1000000000000), orderedInterval (45422779393 / 1000000000000) (45422779394 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (872273618663587 / 4000000000000)) (orderedInterval (-47088129825 / 1000000000000) (-47088102269 / 1000000000000), orderedInterval (26604431206 / 1000000000000) (26604458763 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (545828329596961 / 4000000000000)) (orderedInterval (-57047381144 / 1000000000000) (-57047345332 / 1000000000000), orderedInterval (37771408240 / 1000000000000) (37771444052 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_stateChecks7 :
    compactCertificate380.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (293548291000287 / 4000000000000)) (orderedInterval (-87701704214 / 1000000000000) (-87701701819 / 1000000000000), orderedInterval (31951563348 / 1000000000000) (31951565742 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (797040713341861 / 4000000000000)) (orderedInterval (-48074614276 / 1000000000000) (-48074577448 / 1000000000000), orderedInterval (29848476446 / 1000000000000) (29848513274 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1088290952961797 / 4000000000000)) (orderedInterval (21513115442 / 1000000000000) (21513116650 / 1000000000000), orderedInterval (-43364775361 / 1000000000000) (-43364774152 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_stateChecks8 :
    compactCertificate380.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (460171670403039 / 4000000000000)) (orderedInterval (29767967845 / 1000000000000) (29767969552 / 1000000000000), orderedInterval (-68303142889 / 1000000000000) (-68303141182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1870572292221119 / 4000000000000)) (orderedInterval (-11987344139 / 1000000000000) (-11987344138 / 1000000000000), orderedInterval (-34881897697 / 1000000000000) (-34881897696 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1249455601282321 / 4000000000000)) (orderedInterval (-38239039674 / 1000000000000) (-38238975019 / 1000000000000), orderedInterval (24058008519 / 1000000000000) (24058073175 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_states : ∀ j,
    BesselStateValid (compactCertificate380.point j) (compactCertificate380.state j) :=
  compactCertificate380.statesValid_of_checks3 compactCertificate380_stateChecks0
    compactCertificate380_stateChecks1 compactCertificate380_stateChecks2
    compactCertificate380_stateChecks3 compactCertificate380_stateChecks4
    compactCertificate380_stateChecks5 compactCertificate380_stateChecks6
    compactCertificate380_stateChecks7 compactCertificate380_stateChecks8

theorem compactCertificate380_chunkChecks0_0 :
    compactCertificate380.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (503 / 2) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41142488161 / 1000000000000) (41142488162 / 1000000000000), orderedInterval (28876543796 / 1000000000000) (28876543797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (741015046794203 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37066280237 / 1000000000000) (-37066280236 / 1000000000000), orderedInterval (-45315458120 / 1000000000000) (-45315458119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (239629041018299 / 800000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-44053551106 / 1000000000000) (-44053546042 / 1000000000000), orderedInterval (13661520291 / 1000000000000) (13661525355 / 1000000000000)))) (orderedInterval (13376943600 / 1000000000000) (13376943915 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (216226342536721 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107484509366 / 1000000000000) (-107484509363 / 1000000000000), orderedInterval (-13956153660 / 1000000000000) (-13956153657 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (580814370804637 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65909615390 / 1000000000000) (65909615401 / 1000000000000), orderedInterval (6115151856 / 1000000000000) (6115151866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1577024001220329 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28814687498 / 1000000000000) (-28814665543 / 1000000000000), orderedInterval (28044591622 / 1000000000000) (28044613577 / 1000000000000)))) (orderedInterval (5621030070 / 1000000000000) (5621031662 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1161628741609777 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38778677653 / 1000000000000) (38778756602 / 1000000000000), orderedInterval (-26303655915 / 1000000000000) (-26303576965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1990470648076021 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32043851154 / 1000000000000) (32043912408 / 1000000000000), orderedInterval (-15923242176 / 1000000000000) (-15923180921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1466171670403039 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (9840129176 / 1000000000000) (9840129208 / 1000000000000), orderedInterval (-40510277189 / 1000000000000) (-40510277156 / 1000000000000)))) (orderedInterval (-750545966 / 1000000000000) (-750544061 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_chunkChecks0_1 :
    compactCertificate380.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2249484385364497 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24396613017 / 1000000000000) (-24396613016 / 1000000000000), orderedInterval (-23147969337 / 1000000000000) (-23147969336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1298740415427913 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42097557829 / 1000000000000) (-42097550999 / 1000000000000), orderedInterval (13795223989 / 1000000000000) (13795230819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2304637657893917 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29750682419 / 1000000000000) (-29750594845 / 1000000000000), orderedInterval (14852642161 / 1000000000000) (14852729735 / 1000000000000)))) (orderedInterval (-3013333893 / 1000000000000) (-3013320838 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2153291449738673 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32589923264 / 1000000000000) (-32589901542 / 1000000000000), orderedInterval (11007308197 / 1000000000000) (11007329919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1536690383041409 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40450065863 / 1000000000000) (40450066879 / 1000000000000), orderedInterval (-4625383739 / 1000000000000) (-4625382723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1742443112413911 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10766268705 / 1000000000000) (10766268745 / 1000000000000), orderedInterval (-36693824453 / 1000000000000) (-36693824413 / 1000000000000)))) (orderedInterval (4358938917 / 1000000000000) (4358939436 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1452667408304359 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19067644084 / 1000000000000) (-19067643278 / 1000000000000), orderedInterval (37300822754 / 1000000000000) (37300823559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1283475710219539 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41698120388 / 1000000000000) (41698120390 / 1000000000000), orderedInterval (15597534154 / 1000000000000) (15597534155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (372001286690361 / 800000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27329731760 / 1000000000000) (27329731761 / 1000000000000), orderedInterval (24913663133 / 1000000000000) (24913663134 / 1000000000000)))) (orderedInterval (-1906682655 / 1000000000000) (-1906682621 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_chunkChecks0_2 :
    compactCertificate380.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1028975136340667 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20198475238 / 1000000000000) (20198475239 / 1000000000000), orderedInterval (45422779393 / 1000000000000) (45422779394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (872273618663587 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47088129825 / 1000000000000) (-47088102269 / 1000000000000), orderedInterval (26604431206 / 1000000000000) (26604458763 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (545828329596961 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57047381144 / 1000000000000) (-57047345332 / 1000000000000), orderedInterval (37771408240 / 1000000000000) (37771444052 / 1000000000000)))) (orderedInterval (-2421591999 / 1000000000000) (-2421589210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (293548291000287 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-87701704214 / 1000000000000) (-87701701819 / 1000000000000), orderedInterval (31951563348 / 1000000000000) (31951565742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (797040713341861 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48074614276 / 1000000000000) (-48074577448 / 1000000000000), orderedInterval (29848476446 / 1000000000000) (29848513274 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1088290952961797 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21513115442 / 1000000000000) (21513116650 / 1000000000000), orderedInterval (-43364775361 / 1000000000000) (-43364774152 / 1000000000000)))) (orderedInterval (1061342524 / 1000000000000) (1061343527 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (460171670403039 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29767967845 / 1000000000000) (29767969552 / 1000000000000), orderedInterval (-68303142889 / 1000000000000) (-68303141182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1870572292221119 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11987344139 / 1000000000000) (-11987344138 / 1000000000000), orderedInterval (-34881897697 / 1000000000000) (-34881897696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1249455601282321 / 4000000000000) 0 (IntervalRat.scale (503 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38239039674 / 1000000000000) (-38238975019 / 1000000000000), orderedInterval (24058008519 / 1000000000000) (24058073175 / 1000000000000)))) (orderedInterval (8329888232 / 1000000000000) (8329900444 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_chunkChecks0 :
    compactCertificate380.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate380.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate380_chunkChecks0_0
    compactCertificate380_chunkChecks0_1 compactCertificate380_chunkChecks0_2

theorem compactCertificate380_chunkChecks1_0 :
    compactCertificate380.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (503 / 2) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41142488161 / 1000000000000) (41142488162 / 1000000000000), orderedInterval (28876543796 / 1000000000000) (28876543797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (741015046794203 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37066280237 / 1000000000000) (-37066280236 / 1000000000000), orderedInterval (-45315458120 / 1000000000000) (-45315458119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (239629041018299 / 800000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-44053551106 / 1000000000000) (-44053546042 / 1000000000000), orderedInterval (13661520291 / 1000000000000) (13661525355 / 1000000000000)))) (orderedInterval (12089414647 / 1000000000000) (12089415022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (216226342536721 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107484509366 / 1000000000000) (-107484509363 / 1000000000000), orderedInterval (-13956153660 / 1000000000000) (-13956153657 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (580814370804637 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65909615390 / 1000000000000) (65909615401 / 1000000000000), orderedInterval (6115151856 / 1000000000000) (6115151866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1577024001220329 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28814687498 / 1000000000000) (-28814665543 / 1000000000000), orderedInterval (28044591622 / 1000000000000) (28044613577 / 1000000000000)))) (orderedInterval (-2963879306 / 1000000000000) (-2963876824 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1161628741609777 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38778677653 / 1000000000000) (38778756602 / 1000000000000), orderedInterval (-26303655915 / 1000000000000) (-26303576965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1990470648076021 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32043851154 / 1000000000000) (32043912408 / 1000000000000), orderedInterval (-15923242176 / 1000000000000) (-15923180921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1466171670403039 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (9840129176 / 1000000000000) (9840129208 / 1000000000000), orderedInterval (-40510277189 / 1000000000000) (-40510277156 / 1000000000000)))) (orderedInterval (-455140613 / 1000000000000) (-455136848 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_chunkChecks1_1 :
    compactCertificate380.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2249484385364497 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24396613017 / 1000000000000) (-24396613016 / 1000000000000), orderedInterval (-23147969337 / 1000000000000) (-23147969336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1298740415427913 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42097557829 / 1000000000000) (-42097550999 / 1000000000000), orderedInterval (13795223989 / 1000000000000) (13795230819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2304637657893917 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29750682419 / 1000000000000) (-29750594845 / 1000000000000), orderedInterval (14852642161 / 1000000000000) (14852729735 / 1000000000000)))) (orderedInterval (15353714008 / 1000000000000) (15353743389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2153291449738673 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32589923264 / 1000000000000) (-32589901542 / 1000000000000), orderedInterval (11007308197 / 1000000000000) (11007329919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1536690383041409 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40450065863 / 1000000000000) (40450066879 / 1000000000000), orderedInterval (-4625383739 / 1000000000000) (-4625382723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1742443112413911 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10766268705 / 1000000000000) (10766268745 / 1000000000000), orderedInterval (-36693824453 / 1000000000000) (-36693824413 / 1000000000000)))) (orderedInterval (-771837805 / 1000000000000) (-771836769 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1452667408304359 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19067644084 / 1000000000000) (-19067643278 / 1000000000000), orderedInterval (37300822754 / 1000000000000) (37300823559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1283475710219539 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41698120388 / 1000000000000) (41698120390 / 1000000000000), orderedInterval (15597534154 / 1000000000000) (15597534155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (372001286690361 / 800000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27329731760 / 1000000000000) (27329731761 / 1000000000000), orderedInterval (24913663133 / 1000000000000) (24913663134 / 1000000000000)))) (orderedInterval (662594937 / 1000000000000) (662594987 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_chunkChecks1_2 :
    compactCertificate380.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1028975136340667 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20198475238 / 1000000000000) (20198475239 / 1000000000000), orderedInterval (45422779393 / 1000000000000) (45422779394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (872273618663587 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47088129825 / 1000000000000) (-47088102269 / 1000000000000), orderedInterval (26604431206 / 1000000000000) (26604458763 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (545828329596961 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57047381144 / 1000000000000) (-57047345332 / 1000000000000), orderedInterval (37771408240 / 1000000000000) (37771444052 / 1000000000000)))) (orderedInterval (-8067093000 / 1000000000000) (-8067090956 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (293548291000287 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-87701704214 / 1000000000000) (-87701701819 / 1000000000000), orderedInterval (31951563348 / 1000000000000) (31951565742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (797040713341861 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48074614276 / 1000000000000) (-48074577448 / 1000000000000), orderedInterval (29848476446 / 1000000000000) (29848513274 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1088290952961797 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21513115442 / 1000000000000) (21513116650 / 1000000000000), orderedInterval (-43364775361 / 1000000000000) (-43364774152 / 1000000000000)))) (orderedInterval (2886614427 / 1000000000000) (2886615230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (460171670403039 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29767967845 / 1000000000000) (29767969552 / 1000000000000), orderedInterval (-68303142889 / 1000000000000) (-68303141182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1870572292221119 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11987344139 / 1000000000000) (-11987344138 / 1000000000000), orderedInterval (-34881897697 / 1000000000000) (-34881897696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1249455601282321 / 4000000000000) 1 (IntervalRat.scale (503 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38239039674 / 1000000000000) (-38238975019 / 1000000000000), orderedInterval (24058008519 / 1000000000000) (24058073175 / 1000000000000)))) (orderedInterval (-514952650 / 1000000000000) (-514937480 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_chunkChecks1 :
    compactCertificate380.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate380.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate380_chunkChecks1_0
    compactCertificate380_chunkChecks1_1 compactCertificate380_chunkChecks1_2

theorem compactCertificate380_chunkChecks2_0 :
    compactCertificate380.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (503 / 2) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41142488161 / 1000000000000) (41142488162 / 1000000000000), orderedInterval (28876543796 / 1000000000000) (28876543797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (741015046794203 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37066280237 / 1000000000000) (-37066280236 / 1000000000000), orderedInterval (-45315458120 / 1000000000000) (-45315458119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (239629041018299 / 800000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-44053551106 / 1000000000000) (-44053546042 / 1000000000000), orderedInterval (13661520291 / 1000000000000) (13661525355 / 1000000000000)))) (orderedInterval (-12501186485 / 1000000000000) (-12501186038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (216226342536721 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107484509366 / 1000000000000) (-107484509363 / 1000000000000), orderedInterval (-13956153660 / 1000000000000) (-13956153657 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (580814370804637 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65909615390 / 1000000000000) (65909615401 / 1000000000000), orderedInterval (6115151856 / 1000000000000) (6115151866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1577024001220329 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28814687498 / 1000000000000) (-28814665543 / 1000000000000), orderedInterval (28044591622 / 1000000000000) (28044613577 / 1000000000000)))) (orderedInterval (-5878103336 / 1000000000000) (-5878099442 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1161628741609777 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38778677653 / 1000000000000) (38778756602 / 1000000000000), orderedInterval (-26303655915 / 1000000000000) (-26303576965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1990470648076021 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32043851154 / 1000000000000) (32043912408 / 1000000000000), orderedInterval (-15923242176 / 1000000000000) (-15923180921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1466171670403039 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (9840129176 / 1000000000000) (9840129208 / 1000000000000), orderedInterval (-40510277189 / 1000000000000) (-40510277156 / 1000000000000)))) (orderedInterval (3365952674 / 1000000000000) (3365960131 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_chunkChecks2_1 :
    compactCertificate380.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2249484385364497 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24396613017 / 1000000000000) (-24396613016 / 1000000000000), orderedInterval (-23147969337 / 1000000000000) (-23147969336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1298740415427913 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42097557829 / 1000000000000) (-42097550999 / 1000000000000), orderedInterval (13795223989 / 1000000000000) (13795230819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2304637657893917 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29750682419 / 1000000000000) (-29750594845 / 1000000000000), orderedInterval (14852642161 / 1000000000000) (14852729735 / 1000000000000)))) (orderedInterval (5658255502 / 1000000000000) (5658322241 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2153291449738673 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32589923264 / 1000000000000) (-32589901542 / 1000000000000), orderedInterval (11007308197 / 1000000000000) (11007329919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1536690383041409 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40450065863 / 1000000000000) (40450066879 / 1000000000000), orderedInterval (-4625383739 / 1000000000000) (-4625382723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1742443112413911 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10766268705 / 1000000000000) (10766268745 / 1000000000000), orderedInterval (-36693824453 / 1000000000000) (-36693824413 / 1000000000000)))) (orderedInterval (-11454185601 / 1000000000000) (-11454183494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1452667408304359 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19067644084 / 1000000000000) (-19067643278 / 1000000000000), orderedInterval (37300822754 / 1000000000000) (37300823559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1283475710219539 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41698120388 / 1000000000000) (41698120390 / 1000000000000), orderedInterval (15597534154 / 1000000000000) (15597534155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (372001286690361 / 800000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27329731760 / 1000000000000) (27329731761 / 1000000000000), orderedInterval (24913663133 / 1000000000000) (24913663134 / 1000000000000)))) (orderedInterval (1948544789 / 1000000000000) (1948544861 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_chunkChecks2_2 :
    compactCertificate380.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1028975136340667 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20198475238 / 1000000000000) (20198475239 / 1000000000000), orderedInterval (45422779393 / 1000000000000) (45422779394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (872273618663587 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47088129825 / 1000000000000) (-47088102269 / 1000000000000), orderedInterval (26604431206 / 1000000000000) (26604458763 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (545828329596961 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57047381144 / 1000000000000) (-57047345332 / 1000000000000), orderedInterval (37771408240 / 1000000000000) (37771444052 / 1000000000000)))) (orderedInterval (1953869013 / 1000000000000) (1953870593 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (293548291000287 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-87701704214 / 1000000000000) (-87701701819 / 1000000000000), orderedInterval (31951563348 / 1000000000000) (31951565742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (797040713341861 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48074614276 / 1000000000000) (-48074577448 / 1000000000000), orderedInterval (29848476446 / 1000000000000) (29848513274 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1088290952961797 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21513115442 / 1000000000000) (21513116650 / 1000000000000), orderedInterval (-43364775361 / 1000000000000) (-43364774152 / 1000000000000)))) (orderedInterval (1095513945 / 1000000000000) (1095514612 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (460171670403039 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29767967845 / 1000000000000) (29767969552 / 1000000000000), orderedInterval (-68303142889 / 1000000000000) (-68303141182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1870572292221119 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11987344139 / 1000000000000) (-11987344138 / 1000000000000), orderedInterval (-34881897697 / 1000000000000) (-34881897696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1249455601282321 / 4000000000000) 2 (IntervalRat.scale (503 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38239039674 / 1000000000000) (-38238975019 / 1000000000000), orderedInterval (24058008519 / 1000000000000) (24058073175 / 1000000000000)))) (orderedInterval (-14476660789 / 1000000000000) (-14476641869 / 1000000000000))) = true
  rfl'

theorem compactCertificate380_chunkChecks2 :
    compactCertificate380.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate380.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate380_chunkChecks2_0
    compactCertificate380_chunkChecks2_1 compactCertificate380_chunkChecks2_2

theorem compactCertificate380_chunkChecks3_0 :
    compactCertificate380.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (503 / 2) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41142488161 / 1000000000000) (41142488162 / 1000000000000), orderedInterval (28876543796 / 1000000000000) (28876543797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (741015046794203 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37066280237 / 1000000000000) (-37066280236 / 1000000000000), orderedInterval (-45315458120 / 1000000000000) (-45315458119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (239629041018299 / 800000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-44053551106 / 1000000000000) (-44053546042 / 1000000000000), orderedInterval (13661520291 / 1000000000000) (13661525355 / 1000000000000)))) (orderedInterval (-12581351414 / 1000000000000) (-12581350883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (216226342536721 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107484509366 / 1000000000000) (-107484509363 / 1000000000000), orderedInterval (-13956153660 / 1000000000000) (-13956153657 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (580814370804637 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65909615390 / 1000000000000) (65909615401 / 1000000000000), orderedInterval (6115151856 / 1000000000000) (6115151866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1577024001220329 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28814687498 / 1000000000000) (-28814665543 / 1000000000000), orderedInterval (28044591622 / 1000000000000) (28044613577 / 1000000000000)))) (orderedInterval (7659121110 / 1000000000000) (7659127209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1161628741609777 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38778677653 / 1000000000000) (38778756602 / 1000000000000), orderedInterval (-26303655915 / 1000000000000) (-26303576965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1990470648076021 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32043851154 / 1000000000000) (32043912408 / 1000000000000), orderedInterval (-15923242176 / 1000000000000) (-15923180921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1466171670403039 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (9840129176 / 1000000000000) (9840129208 / 1000000000000), orderedInterval (-40510277189 / 1000000000000) (-40510277156 / 1000000000000)))) (orderedInterval (-786830725 / 1000000000000) (-786815979 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate380_chunkChecks3_1 :
    compactCertificate380.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2249484385364497 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24396613017 / 1000000000000) (-24396613016 / 1000000000000), orderedInterval (-23147969337 / 1000000000000) (-23147969336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1298740415427913 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42097557829 / 1000000000000) (-42097550999 / 1000000000000), orderedInterval (13795223989 / 1000000000000) (13795230819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2304637657893917 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29750682419 / 1000000000000) (-29750594845 / 1000000000000), orderedInterval (14852642161 / 1000000000000) (14852729735 / 1000000000000)))) (orderedInterval (-73592980510 / 1000000000000) (-73592828510 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2153291449738673 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32589923264 / 1000000000000) (-32589901542 / 1000000000000), orderedInterval (11007308197 / 1000000000000) (11007329919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1536690383041409 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40450065863 / 1000000000000) (40450066879 / 1000000000000), orderedInterval (-4625383739 / 1000000000000) (-4625382723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1742443112413911 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10766268705 / 1000000000000) (10766268745 / 1000000000000), orderedInterval (-36693824453 / 1000000000000) (-36693824413 / 1000000000000)))) (orderedInterval (2588311903 / 1000000000000) (2588316237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1452667408304359 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19067644084 / 1000000000000) (-19067643278 / 1000000000000), orderedInterval (37300822754 / 1000000000000) (37300823559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1283475710219539 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41698120388 / 1000000000000) (41698120390 / 1000000000000), orderedInterval (15597534154 / 1000000000000) (15597534155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (372001286690361 / 800000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27329731760 / 1000000000000) (27329731761 / 1000000000000), orderedInterval (24913663133 / 1000000000000) (24913663134 / 1000000000000)))) (orderedInterval (-3482791355 / 1000000000000) (-3482791247 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate380_chunkChecks3_2 :
    compactCertificate380.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1028975136340667 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20198475238 / 1000000000000) (20198475239 / 1000000000000), orderedInterval (45422779393 / 1000000000000) (45422779394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (872273618663587 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47088129825 / 1000000000000) (-47088102269 / 1000000000000), orderedInterval (26604431206 / 1000000000000) (26604458763 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (545828329596961 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57047381144 / 1000000000000) (-57047345332 / 1000000000000), orderedInterval (37771408240 / 1000000000000) (37771444052 / 1000000000000)))) (orderedInterval (8549108064 / 1000000000000) (8549109328 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (293548291000287 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-87701704214 / 1000000000000) (-87701701819 / 1000000000000), orderedInterval (31951563348 / 1000000000000) (31951565742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (797040713341861 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48074614276 / 1000000000000) (-48074577448 / 1000000000000), orderedInterval (29848476446 / 1000000000000) (29848513274 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1088290952961797 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21513115442 / 1000000000000) (21513116650 / 1000000000000), orderedInterval (-43364775361 / 1000000000000) (-43364774152 / 1000000000000)))) (orderedInterval (-3860404307 / 1000000000000) (-3860403742 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (460171670403039 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29767967845 / 1000000000000) (29767969552 / 1000000000000), orderedInterval (-68303142889 / 1000000000000) (-68303141182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1870572292221119 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11987344139 / 1000000000000) (-11987344138 / 1000000000000), orderedInterval (-34881897697 / 1000000000000) (-34881897696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1249455601282321 / 4000000000000) 3 (IntervalRat.scale (503 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38239039674 / 1000000000000) (-38238975019 / 1000000000000), orderedInterval (24058008519 / 1000000000000) (24058073175 / 1000000000000)))) (orderedInterval (-9509133274 / 1000000000000) (-9509109734 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate380_chunkChecks3 :
    compactCertificate380.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate380.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate380_chunkChecks3_0
    compactCertificate380_chunkChecks3_1 compactCertificate380_chunkChecks3_2

theorem compactCertificate380_chunkChecks4_0 :
    compactCertificate380.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (503 / 2) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41142488161 / 1000000000000) (41142488162 / 1000000000000), orderedInterval (28876543796 / 1000000000000) (28876543797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (741015046794203 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-37066280237 / 1000000000000) (-37066280236 / 1000000000000), orderedInterval (-45315458120 / 1000000000000) (-45315458119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (239629041018299 / 800000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-44053551106 / 1000000000000) (-44053546042 / 1000000000000), orderedInterval (13661520291 / 1000000000000) (13661525355 / 1000000000000)))) (orderedInterval (11104156461 / 1000000000000) (11104157094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (216226342536721 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107484509366 / 1000000000000) (-107484509363 / 1000000000000), orderedInterval (-13956153660 / 1000000000000) (-13956153657 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (580814370804637 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65909615390 / 1000000000000) (65909615401 / 1000000000000), orderedInterval (6115151856 / 1000000000000) (6115151866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1577024001220329 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28814687498 / 1000000000000) (-28814665543 / 1000000000000), orderedInterval (28044591622 / 1000000000000) (28044613577 / 1000000000000)))) (orderedInterval (12579201933 / 1000000000000) (12579211516 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1161628741609777 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38778677653 / 1000000000000) (38778756602 / 1000000000000), orderedInterval (-26303655915 / 1000000000000) (-26303576965 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1990470648076021 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32043851154 / 1000000000000) (32043912408 / 1000000000000), orderedInterval (-15923242176 / 1000000000000) (-15923180921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1466171670403039 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (9840129176 / 1000000000000) (9840129208 / 1000000000000), orderedInterval (-40510277189 / 1000000000000) (-40510277156 / 1000000000000)))) (orderedInterval (-14068441138 / 1000000000000) (-14068411915 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate380_chunkChecks4_1 :
    compactCertificate380.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2249484385364497 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24396613017 / 1000000000000) (-24396613016 / 1000000000000), orderedInterval (-23147969337 / 1000000000000) (-23147969336 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1298740415427913 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-42097557829 / 1000000000000) (-42097550999 / 1000000000000), orderedInterval (13795223989 / 1000000000000) (13795230819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2304637657893917 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29750682419 / 1000000000000) (-29750594845 / 1000000000000), orderedInterval (14852642161 / 1000000000000) (14852729735 / 1000000000000)))) (orderedInterval (-16192023033 / 1000000000000) (-16191675379 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2153291449738673 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-32589923264 / 1000000000000) (-32589901542 / 1000000000000), orderedInterval (11007308197 / 1000000000000) (11007329919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1536690383041409 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40450065863 / 1000000000000) (40450066879 / 1000000000000), orderedInterval (-4625383739 / 1000000000000) (-4625382723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1742443112413911 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10766268705 / 1000000000000) (10766268745 / 1000000000000), orderedInterval (-36693824453 / 1000000000000) (-36693824413 / 1000000000000)))) (orderedInterval (32663914856 / 1000000000000) (32663923883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1452667408304359 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19067644084 / 1000000000000) (-19067643278 / 1000000000000), orderedInterval (37300822754 / 1000000000000) (37300823559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1283475710219539 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41698120388 / 1000000000000) (41698120390 / 1000000000000), orderedInterval (15597534154 / 1000000000000) (15597534155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (372001286690361 / 800000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27329731760 / 1000000000000) (27329731761 / 1000000000000), orderedInterval (24913663133 / 1000000000000) (24913663134 / 1000000000000)))) (orderedInterval (925378981 / 1000000000000) (925379149 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate380_chunkChecks4_2 :
    compactCertificate380.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1028975136340667 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20198475238 / 1000000000000) (20198475239 / 1000000000000), orderedInterval (45422779393 / 1000000000000) (45422779394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (872273618663587 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47088129825 / 1000000000000) (-47088102269 / 1000000000000), orderedInterval (26604431206 / 1000000000000) (26604458763 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (545828329596961 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57047381144 / 1000000000000) (-57047345332 / 1000000000000), orderedInterval (37771408240 / 1000000000000) (37771444052 / 1000000000000)))) (orderedInterval (-2257357683 / 1000000000000) (-2257356637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (293548291000287 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-87701704214 / 1000000000000) (-87701701819 / 1000000000000), orderedInterval (31951563348 / 1000000000000) (31951565742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (797040713341861 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-48074614276 / 1000000000000) (-48074577448 / 1000000000000), orderedInterval (29848476446 / 1000000000000) (29848513274 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1088290952961797 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (21513115442 / 1000000000000) (21513116650 / 1000000000000), orderedInterval (-43364775361 / 1000000000000) (-43364774152 / 1000000000000)))) (orderedInterval (-1785875784 / 1000000000000) (-1785875294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (460171670403039 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (29767967845 / 1000000000000) (29767969552 / 1000000000000), orderedInterval (-68303142889 / 1000000000000) (-68303141182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1870572292221119 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11987344139 / 1000000000000) (-11987344138 / 1000000000000), orderedInterval (-34881897697 / 1000000000000) (-34881897696 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1249455601282321 / 4000000000000) 4 (IntervalRat.scale (503 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-38239039674 / 1000000000000) (-38238975019 / 1000000000000), orderedInterval (24058008519 / 1000000000000) (24058073175 / 1000000000000)))) (orderedInterval (28819954379 / 1000000000000) (28819983789 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate380_chunkChecks4 :
    compactCertificate380.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate380.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate380_chunkChecks4_0
    compactCertificate380_chunkChecks4_1 compactCertificate380_chunkChecks4_2

theorem compactCertificate380_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate380.chunkCheck r b = true :=
  compactCertificate380.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate380_chunkChecks0
    · exact compactCertificate380_chunkChecks1
    · exact compactCertificate380_chunkChecks2
    · exact compactCertificate380_chunkChecks3
    · exact compactCertificate380_chunkChecks4)

theorem compactCertificate380_coefficient0 :
    compactCertificate380.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate380_coefficient1 :
    compactCertificate380.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate380_coefficient2 :
    compactCertificate380.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate380_coefficient3 :
    compactCertificate380.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate380_coefficient4 :
    compactCertificate380.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate380_coefficients : ∀ r : Fin 5,
    compactCertificate380.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate380_coefficient0
  · exact compactCertificate380_coefficient1
  · exact compactCertificate380_coefficient2
  · exact compactCertificate380_coefficient3
  · exact compactCertificate380_coefficient4

theorem compactCertificate380_lower : (1 : ℚ) ≤ compactCertificate380.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate380, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate380_proves {t : ℝ} (ht : t ∈ compactCertificate380.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate380.proves compactCertificate380_states compactCertificate380_chunks
    compactCertificate380_coefficients compactCertificate380_lower ht

end Erdos232
