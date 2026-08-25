/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate500 : CompactCertificate where
  left := 371
  right := 372
  center := 743 / 2
  grid := fun i =>
    match i.val with
    | 0 => 118
    | 1 => 87
    | 2 => 141
    | 3 => 25
    | 4 => 68
    | 5 => 185
    | 6 => 137
    | 7 => 234
    | 8 => 172
    | 9 => 265
    | 10 => 153
    | 11 => 271
    | 12 => 253
    | 13 => 181
    | 14 => 205
    | 15 => 171
    | 16 => 151
    | 17 => 219
    | 18 => 121
    | 19 => 103
    | 20 => 64
    | 21 => 35
    | 22 => 94
    | 23 => 128
    | 24 => 54
    | 25 => 220
    | _ => 147
  point := fun i =>
    match i.val with
    | 0 => 743 / 2
    | 1 => 1094580874290443 / 4000000000000
    | 2 => 353964965162219 / 800000000000
    | 3 => 319395969194401 / 4000000000000
    | 4 => 857942500015597 / 4000000000000
    | 5 => 2329480781126649 / 4000000000000
    | 6 => 1715885000031937 / 4000000000000
    | 7 => 2940198193877701 / 4000000000000
    | 8 => 2165736682126159 / 4000000000000
    | 9 => 3322797014564257 / 4000000000000
    | 10 => 1918417750820953 / 4000000000000
    | 11 => 3404265963847277 / 4000000000000
    | 12 => 3180706853192513 / 4000000000000
    | 13 => 2269902494234129 / 4000000000000
    | 14 => 2573827500046791 / 4000000000000
    | 15 => 2145789034533079 / 4000000000000
    | 16 => 1895869687262659 / 4000000000000
    | 17 => 549496930439241 / 800000000000
    | 18 => 1519937428034027 / 4000000000000
    | 19 => 1288467790590547 / 4000000000000
    | 20 => 806263317873841 / 4000000000000
    | 21 => 433611093863247 / 4000000000000
    | 22 => 1177338469210741 / 4000000000000
    | 23 => 1607555025945557 / 4000000000000
    | 24 => 679736682126159 / 4000000000000
    | 25 => 2763091874990639 / 4000000000000
    | _ => 1845617319588001 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (41395367960 / 1000000000000) (41395368208 / 1000000000000), orderedInterval (-317843008 / 1000000000000) (-317842760 / 1000000000000))
    | 1 => (orderedInterval (-43236624051 / 1000000000000) (-43236624050 / 1000000000000), orderedInterval (-21299355821 / 1000000000000) (-21299355820 / 1000000000000))
    | 2 => (orderedInterval (-10364456303 / 1000000000000) (-10364456302 / 1000000000000), orderedInterval (-36476778629 / 1000000000000) (-36476778628 / 1000000000000))
    | 3 => (orderedInterval (-77388923507 / 1000000000000) (-77388907771 / 1000000000000), orderedInterval (45023020387 / 1000000000000) (45023036123 / 1000000000000))
    | 4 => (orderedInterval (54341819578 / 1000000000000) (54341819783 / 1000000000000), orderedInterval (-4010222315 / 1000000000000) (-4010222110 / 1000000000000))
    | 5 => (orderedInterval (-30580896188 / 1000000000000) (-30580848034 / 1000000000000), orderedInterval (12594564762 / 1000000000000) (12594612916 / 1000000000000))
    | 6 => (orderedInterval (23062777385 / 1000000000000) (23062781163 / 1000000000000), orderedInterval (-30884137315 / 1000000000000) (-30884133537 / 1000000000000))
    | 7 => (orderedInterval (19006081642 / 1000000000000) (19006081643 / 1000000000000), orderedInterval (22456158296 / 1000000000000) (22456158297 / 1000000000000))
    | 8 => (orderedInterval (32812645316 / 1000000000000) (32812661856 / 1000000000000), orderedInterval (-9986817930 / 1000000000000) (-9986801390 / 1000000000000))
    | 9 => (orderedInterval (23839816454 / 1000000000000) (23839842125 / 1000000000000), orderedInterval (-14086625003 / 1000000000000) (-14086599332 / 1000000000000))
    | 10 => (orderedInterval (9861812119 / 1000000000000) (9861812143 / 1000000000000), orderedInterval (-35083495358 / 1000000000000) (-35083495335 / 1000000000000))
    | 11 => (orderedInterval (-12632917498 / 1000000000000) (-12632917497 / 1000000000000), orderedInterval (-24250264867 / 1000000000000) (-24250264866 / 1000000000000))
    | 12 => (orderedInterval (-25698019775 / 1000000000000) (-25698019765 / 1000000000000), orderedInterval (-11825011308 / 1000000000000) (-11825011298 / 1000000000000))
    | 13 => (orderedInterval (12032849567 / 1000000000000) (12032849616 / 1000000000000), orderedInterval (-31268497060 / 1000000000000) (-31268497011 / 1000000000000))
    | 14 => (orderedInterval (-6728671563 / 1000000000000) (-6728671562 / 1000000000000), orderedInterval (-30720976412 / 1000000000000) (-30720976411 / 1000000000000))
    | 15 => (orderedInterval (-691689814 / 1000000000000) (-691689813 / 1000000000000), orderedInterval (-34441412172 / 1000000000000) (-34441412171 / 1000000000000))
    | 16 => (orderedInterval (-13323502759 / 1000000000000) (-13323502758 / 1000000000000), orderedInterval (-34127661570 / 1000000000000) (-34127661569 / 1000000000000))
    | 17 => (orderedInterval (10508142493 / 1000000000000) (10508142509 / 1000000000000), orderedInterval (-28580700909 / 1000000000000) (-28580700893 / 1000000000000))
    | 18 => (orderedInterval (-24336091745 / 1000000000000) (-24336091744 / 1000000000000), orderedInterval (-32879058107 / 1000000000000) (-32879058106 / 1000000000000))
    | 19 => (orderedInterval (28025819574 / 1000000000000) (28025829604 / 1000000000000), orderedInterval (-34553156362 / 1000000000000) (-34553146332 / 1000000000000))
    | 20 => (orderedInterval (53977620784 / 1000000000000) (53977620786 / 1000000000000), orderedInterval (15511543684 / 1000000000000) (15511543685 / 1000000000000))
    | 21 => (orderedInterval (53276884652 / 1000000000000) (53276945675 / 1000000000000), orderedInterval (-55330222876 / 1000000000000) (-55330161853 / 1000000000000))
    | 22 => (orderedInterval (-8788694781 / 1000000000000) (-8788694753 / 1000000000000), orderedInterval (45684103020 / 1000000000000) (45684103048 / 1000000000000))
    | 23 => (orderedInterval (20802593946 / 1000000000000) (20802593947 / 1000000000000), orderedInterval (33905259093 / 1000000000000) (33905259094 / 1000000000000))
    | 24 => (orderedInterval (53773467959 / 1000000000000) (53773467960 / 1000000000000), orderedInterval (29076662607 / 1000000000000) (29076662608 / 1000000000000))
    | 25 => (orderedInterval (12039738062 / 1000000000000) (12039738063 / 1000000000000), orderedInterval (27859722684 / 1000000000000) (27859722685 / 1000000000000))
    | _ => (orderedInterval (-13616803199 / 1000000000000) (-13616803198 / 1000000000000), orderedInterval (-34544281829 / 1000000000000) (-34544281828 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (15396595150 / 1000000000000) (15396595275 / 1000000000000)
      | 1 => orderedInterval (4997710980 / 1000000000000) (4997714626 / 1000000000000)
      | 2 => orderedInterval (206793286 / 1000000000000) (206793707 / 1000000000000)
      | 3 => orderedInterval (-5301216707 / 1000000000000) (-5301211997 / 1000000000000)
      | 4 => orderedInterval (1635840234 / 1000000000000) (1635840283 / 1000000000000)
      | 5 => orderedInterval (1023522320 / 1000000000000) (1023522357 / 1000000000000)
      | 6 => orderedInterval (4062152441 / 1000000000000) (4062153102 / 1000000000000)
      | 7 => orderedInterval (-2378664446 / 1000000000000) (-2378663274 / 1000000000000)
      | _ => orderedInterval (1898981471 / 1000000000000) (1898981574 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-2821505547 / 1000000000000) (-2821505419 / 1000000000000)
      | 1 => orderedInterval (-1593087061 / 1000000000000) (-1593081602 / 1000000000000)
      | 2 => orderedInterval (-1722219516 / 1000000000000) (-1722218896 / 1000000000000)
      | 3 => orderedInterval (-5656323503 / 1000000000000) (-5656312996 / 1000000000000)
      | 4 => orderedInterval (-3790432422 / 1000000000000) (-3790432342 / 1000000000000)
      | 5 => orderedInterval (564392525 / 1000000000000) (564392578 / 1000000000000)
      | 6 => orderedInterval (7346901997 / 1000000000000) (7346902576 / 1000000000000)
      | 7 => orderedInterval (-3334041349 / 1000000000000) (-3334040979 / 1000000000000)
      | _ => orderedInterval (3913290109 / 1000000000000) (3913290254 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-15318771069 / 1000000000000) (-15318770936 / 1000000000000)
      | 1 => orderedInterval (-6038281229 / 1000000000000) (-6038272721 / 1000000000000)
      | 2 => orderedInterval (615172651 / 1000000000000) (615173566 / 1000000000000)
      | 3 => orderedInterval (29402588757 / 1000000000000) (29402612249 / 1000000000000)
      | 4 => orderedInterval (-4872456670 / 1000000000000) (-4872456539 / 1000000000000)
      | 5 => orderedInterval (-2145676052 / 1000000000000) (-2145675974 / 1000000000000)
      | 6 => orderedInterval (-3415436673 / 1000000000000) (-3415436163 / 1000000000000)
      | 7 => orderedInterval (1833359333 / 1000000000000) (1833359471 / 1000000000000)
      | _ => orderedInterval (-630967976 / 1000000000000) (-630967762 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (3862690542 / 1000000000000) (3862690680 / 1000000000000)
      | 1 => orderedInterval (3498408097 / 1000000000000) (3498421415 / 1000000000000)
      | 2 => orderedInterval (6110638025 / 1000000000000) (6110639382 / 1000000000000)
      | 3 => orderedInterval (18976393995 / 1000000000000) (18976446493 / 1000000000000)
      | 4 => orderedInterval (7650630115 / 1000000000000) (7650630335 / 1000000000000)
      | 5 => orderedInterval (1772701268 / 1000000000000) (1772701389 / 1000000000000)
      | 6 => orderedInterval (-6971877227 / 1000000000000) (-6971876776 / 1000000000000)
      | 7 => orderedInterval (3774814943 / 1000000000000) (3774815013 / 1000000000000)
      | _ => orderedInterval (2146732386 / 1000000000000) (2146732716 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15044421182 / 1000000000000) (15044421327 / 1000000000000)
      | 1 => orderedInterval (13331932553 / 1000000000000) (13331953460 / 1000000000000)
      | 2 => orderedInterval (-5439491303 / 1000000000000) (-5439489275 / 1000000000000)
      | 3 => orderedInterval (-153437358425 / 1000000000000) (-153437240924 / 1000000000000)
      | 4 => orderedInterval (16198270245 / 1000000000000) (16198270624 / 1000000000000)
      | 5 => orderedInterval (5119943478 / 1000000000000) (5119943670 / 1000000000000)
      | 6 => orderedInterval (3552195481 / 1000000000000) (3552195883 / 1000000000000)
      | 7 => orderedInterval (-2132383580 / 1000000000000) (-2132383528 / 1000000000000)
      | _ => orderedInterval (-5633365170 / 1000000000000) (-5633364640 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (21541714729 / 1000000000000) (21541725653 / 1000000000000)
    | 1 => orderedInterval (-7093024767 / 1000000000000) (-7093006826 / 1000000000000)
    | 2 => orderedInterval (-570468928 / 1000000000000) (-570434809 / 1000000000000)
    | 3 => orderedInterval (40821132144 / 1000000000000) (40821200647 / 1000000000000)
    | _ => orderedInterval (-113395835539 / 1000000000000) (-113395693403 / 1000000000000)

theorem compactCertificate500_stateChecks0 :
    compactCertificate500.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (743 / 2)) (orderedInterval (41395367960 / 1000000000000) (41395368208 / 1000000000000), orderedInterval (-317843008 / 1000000000000) (-317842760 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1094580874290443 / 4000000000000)) (orderedInterval (-43236624051 / 1000000000000) (-43236624050 / 1000000000000), orderedInterval (-21299355821 / 1000000000000) (-21299355820 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (353964965162219 / 800000000000)) (orderedInterval (-10364456303 / 1000000000000) (-10364456302 / 1000000000000), orderedInterval (-36476778629 / 1000000000000) (-36476778628 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_stateChecks1 :
    compactCertificate500.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (319395969194401 / 4000000000000)) (orderedInterval (-77388923507 / 1000000000000) (-77388907771 / 1000000000000), orderedInterval (45023020387 / 1000000000000) (45023036123 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (857942500015597 / 4000000000000)) (orderedInterval (54341819578 / 1000000000000) (54341819783 / 1000000000000), orderedInterval (-4010222315 / 1000000000000) (-4010222110 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2329480781126649 / 4000000000000)) (orderedInterval (-30580896188 / 1000000000000) (-30580848034 / 1000000000000), orderedInterval (12594564762 / 1000000000000) (12594612916 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_stateChecks2 :
    compactCertificate500.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1715885000031937 / 4000000000000)) (orderedInterval (23062777385 / 1000000000000) (23062781163 / 1000000000000), orderedInterval (-30884137315 / 1000000000000) (-30884133537 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (2940198193877701 / 4000000000000)) (orderedInterval (19006081642 / 1000000000000) (19006081643 / 1000000000000), orderedInterval (22456158296 / 1000000000000) (22456158297 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2165736682126159 / 4000000000000)) (orderedInterval (32812645316 / 1000000000000) (32812661856 / 1000000000000), orderedInterval (-9986817930 / 1000000000000) (-9986801390 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_stateChecks3 :
    compactCertificate500.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 265 12 (3322797014564257 / 4000000000000)) (orderedInterval (23839816454 / 1000000000000) (23839842125 / 1000000000000), orderedInterval (-14086625003 / 1000000000000) (-14086599332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1918417750820953 / 4000000000000)) (orderedInterval (9861812119 / 1000000000000) (9861812143 / 1000000000000), orderedInterval (-35083495358 / 1000000000000) (-35083495335 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 271 12 (3404265963847277 / 4000000000000)) (orderedInterval (-12632917498 / 1000000000000) (-12632917497 / 1000000000000), orderedInterval (-24250264867 / 1000000000000) (-24250264866 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_stateChecks4 :
    compactCertificate500.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 253 12 (3180706853192513 / 4000000000000)) (orderedInterval (-25698019775 / 1000000000000) (-25698019765 / 1000000000000), orderedInterval (-11825011308 / 1000000000000) (-11825011298 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2269902494234129 / 4000000000000)) (orderedInterval (12032849567 / 1000000000000) (12032849616 / 1000000000000), orderedInterval (-31268497060 / 1000000000000) (-31268497011 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2573827500046791 / 4000000000000)) (orderedInterval (-6728671563 / 1000000000000) (-6728671562 / 1000000000000), orderedInterval (-30720976412 / 1000000000000) (-30720976411 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_stateChecks5 :
    compactCertificate500.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2145789034533079 / 4000000000000)) (orderedInterval (-691689814 / 1000000000000) (-691689813 / 1000000000000), orderedInterval (-34441412172 / 1000000000000) (-34441412171 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1895869687262659 / 4000000000000)) (orderedInterval (-13323502759 / 1000000000000) (-13323502758 / 1000000000000), orderedInterval (-34127661570 / 1000000000000) (-34127661569 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (549496930439241 / 800000000000)) (orderedInterval (10508142493 / 1000000000000) (10508142509 / 1000000000000), orderedInterval (-28580700909 / 1000000000000) (-28580700893 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_stateChecks6 :
    compactCertificate500.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1519937428034027 / 4000000000000)) (orderedInterval (-24336091745 / 1000000000000) (-24336091744 / 1000000000000), orderedInterval (-32879058107 / 1000000000000) (-32879058106 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1288467790590547 / 4000000000000)) (orderedInterval (28025819574 / 1000000000000) (28025829604 / 1000000000000), orderedInterval (-34553156362 / 1000000000000) (-34553146332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (806263317873841 / 4000000000000)) (orderedInterval (53977620784 / 1000000000000) (53977620786 / 1000000000000), orderedInterval (15511543684 / 1000000000000) (15511543685 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_stateChecks7 :
    compactCertificate500.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (433611093863247 / 4000000000000)) (orderedInterval (53276884652 / 1000000000000) (53276945675 / 1000000000000), orderedInterval (-55330222876 / 1000000000000) (-55330161853 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1177338469210741 / 4000000000000)) (orderedInterval (-8788694781 / 1000000000000) (-8788694753 / 1000000000000), orderedInterval (45684103020 / 1000000000000) (45684103048 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1607555025945557 / 4000000000000)) (orderedInterval (20802593946 / 1000000000000) (20802593947 / 1000000000000), orderedInterval (33905259093 / 1000000000000) (33905259094 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_stateChecks8 :
    compactCertificate500.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (679736682126159 / 4000000000000)) (orderedInterval (53773467959 / 1000000000000) (53773467960 / 1000000000000), orderedInterval (29076662607 / 1000000000000) (29076662608 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2763091874990639 / 4000000000000)) (orderedInterval (12039738062 / 1000000000000) (12039738063 / 1000000000000), orderedInterval (27859722684 / 1000000000000) (27859722685 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1845617319588001 / 4000000000000)) (orderedInterval (-13616803199 / 1000000000000) (-13616803198 / 1000000000000), orderedInterval (-34544281829 / 1000000000000) (-34544281828 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_states : ∀ j,
    BesselStateValid (compactCertificate500.point j) (compactCertificate500.state j) :=
  compactCertificate500.statesValid_of_checks3 compactCertificate500_stateChecks0
    compactCertificate500_stateChecks1 compactCertificate500_stateChecks2
    compactCertificate500_stateChecks3 compactCertificate500_stateChecks4
    compactCertificate500_stateChecks5 compactCertificate500_stateChecks6
    compactCertificate500_stateChecks7 compactCertificate500_stateChecks8

theorem compactCertificate500_chunkChecks0_0 :
    compactCertificate500.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (743 / 2) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41395367960 / 1000000000000) (41395368208 / 1000000000000), orderedInterval (-317843008 / 1000000000000) (-317842760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1094580874290443 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43236624051 / 1000000000000) (-43236624050 / 1000000000000), orderedInterval (-21299355821 / 1000000000000) (-21299355820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (353964965162219 / 800000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10364456303 / 1000000000000) (-10364456302 / 1000000000000), orderedInterval (-36476778629 / 1000000000000) (-36476778628 / 1000000000000)))) (orderedInterval (15396595150 / 1000000000000) (15396595275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (319395969194401 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77388923507 / 1000000000000) (-77388907771 / 1000000000000), orderedInterval (45023020387 / 1000000000000) (45023036123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (857942500015597 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (54341819578 / 1000000000000) (54341819783 / 1000000000000), orderedInterval (-4010222315 / 1000000000000) (-4010222110 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2329480781126649 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30580896188 / 1000000000000) (-30580848034 / 1000000000000), orderedInterval (12594564762 / 1000000000000) (12594612916 / 1000000000000)))) (orderedInterval (4997710980 / 1000000000000) (4997714626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1715885000031937 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23062777385 / 1000000000000) (23062781163 / 1000000000000), orderedInterval (-30884137315 / 1000000000000) (-30884133537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2940198193877701 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19006081642 / 1000000000000) (19006081643 / 1000000000000), orderedInterval (22456158296 / 1000000000000) (22456158297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2165736682126159 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32812645316 / 1000000000000) (32812661856 / 1000000000000), orderedInterval (-9986817930 / 1000000000000) (-9986801390 / 1000000000000)))) (orderedInterval (206793286 / 1000000000000) (206793707 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_chunkChecks0_1 :
    compactCertificate500.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3322797014564257 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23839816454 / 1000000000000) (23839842125 / 1000000000000), orderedInterval (-14086625003 / 1000000000000) (-14086599332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1918417750820953 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9861812119 / 1000000000000) (9861812143 / 1000000000000), orderedInterval (-35083495358 / 1000000000000) (-35083495335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3404265963847277 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12632917498 / 1000000000000) (-12632917497 / 1000000000000), orderedInterval (-24250264867 / 1000000000000) (-24250264866 / 1000000000000)))) (orderedInterval (-5301216707 / 1000000000000) (-5301211997 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3180706853192513 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25698019775 / 1000000000000) (-25698019765 / 1000000000000), orderedInterval (-11825011308 / 1000000000000) (-11825011298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2269902494234129 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12032849567 / 1000000000000) (12032849616 / 1000000000000), orderedInterval (-31268497060 / 1000000000000) (-31268497011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2573827500046791 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6728671563 / 1000000000000) (-6728671562 / 1000000000000), orderedInterval (-30720976412 / 1000000000000) (-30720976411 / 1000000000000)))) (orderedInterval (1635840234 / 1000000000000) (1635840283 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2145789034533079 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-691689814 / 1000000000000) (-691689813 / 1000000000000), orderedInterval (-34441412172 / 1000000000000) (-34441412171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1895869687262659 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13323502759 / 1000000000000) (-13323502758 / 1000000000000), orderedInterval (-34127661570 / 1000000000000) (-34127661569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (549496930439241 / 800000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (10508142493 / 1000000000000) (10508142509 / 1000000000000), orderedInterval (-28580700909 / 1000000000000) (-28580700893 / 1000000000000)))) (orderedInterval (1023522320 / 1000000000000) (1023522357 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_chunkChecks0_2 :
    compactCertificate500.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1519937428034027 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24336091745 / 1000000000000) (-24336091744 / 1000000000000), orderedInterval (-32879058107 / 1000000000000) (-32879058106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1288467790590547 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28025819574 / 1000000000000) (28025829604 / 1000000000000), orderedInterval (-34553156362 / 1000000000000) (-34553146332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (806263317873841 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53977620784 / 1000000000000) (53977620786 / 1000000000000), orderedInterval (15511543684 / 1000000000000) (15511543685 / 1000000000000)))) (orderedInterval (4062152441 / 1000000000000) (4062153102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (433611093863247 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (53276884652 / 1000000000000) (53276945675 / 1000000000000), orderedInterval (-55330222876 / 1000000000000) (-55330161853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1177338469210741 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-8788694781 / 1000000000000) (-8788694753 / 1000000000000), orderedInterval (45684103020 / 1000000000000) (45684103048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1607555025945557 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20802593946 / 1000000000000) (20802593947 / 1000000000000), orderedInterval (33905259093 / 1000000000000) (33905259094 / 1000000000000)))) (orderedInterval (-2378664446 / 1000000000000) (-2378663274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (679736682126159 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53773467959 / 1000000000000) (53773467960 / 1000000000000), orderedInterval (29076662607 / 1000000000000) (29076662608 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2763091874990639 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12039738062 / 1000000000000) (12039738063 / 1000000000000), orderedInterval (27859722684 / 1000000000000) (27859722685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1845617319588001 / 4000000000000) 0 (IntervalRat.scale (743 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13616803199 / 1000000000000) (-13616803198 / 1000000000000), orderedInterval (-34544281829 / 1000000000000) (-34544281828 / 1000000000000)))) (orderedInterval (1898981471 / 1000000000000) (1898981574 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_chunkChecks0 :
    compactCertificate500.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate500.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate500_chunkChecks0_0
    compactCertificate500_chunkChecks0_1 compactCertificate500_chunkChecks0_2

theorem compactCertificate500_chunkChecks1_0 :
    compactCertificate500.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (743 / 2) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41395367960 / 1000000000000) (41395368208 / 1000000000000), orderedInterval (-317843008 / 1000000000000) (-317842760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1094580874290443 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43236624051 / 1000000000000) (-43236624050 / 1000000000000), orderedInterval (-21299355821 / 1000000000000) (-21299355820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (353964965162219 / 800000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10364456303 / 1000000000000) (-10364456302 / 1000000000000), orderedInterval (-36476778629 / 1000000000000) (-36476778628 / 1000000000000)))) (orderedInterval (-2821505547 / 1000000000000) (-2821505419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (319395969194401 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77388923507 / 1000000000000) (-77388907771 / 1000000000000), orderedInterval (45023020387 / 1000000000000) (45023036123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (857942500015597 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (54341819578 / 1000000000000) (54341819783 / 1000000000000), orderedInterval (-4010222315 / 1000000000000) (-4010222110 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2329480781126649 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30580896188 / 1000000000000) (-30580848034 / 1000000000000), orderedInterval (12594564762 / 1000000000000) (12594612916 / 1000000000000)))) (orderedInterval (-1593087061 / 1000000000000) (-1593081602 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1715885000031937 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23062777385 / 1000000000000) (23062781163 / 1000000000000), orderedInterval (-30884137315 / 1000000000000) (-30884133537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2940198193877701 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19006081642 / 1000000000000) (19006081643 / 1000000000000), orderedInterval (22456158296 / 1000000000000) (22456158297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2165736682126159 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32812645316 / 1000000000000) (32812661856 / 1000000000000), orderedInterval (-9986817930 / 1000000000000) (-9986801390 / 1000000000000)))) (orderedInterval (-1722219516 / 1000000000000) (-1722218896 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_chunkChecks1_1 :
    compactCertificate500.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3322797014564257 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23839816454 / 1000000000000) (23839842125 / 1000000000000), orderedInterval (-14086625003 / 1000000000000) (-14086599332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1918417750820953 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9861812119 / 1000000000000) (9861812143 / 1000000000000), orderedInterval (-35083495358 / 1000000000000) (-35083495335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3404265963847277 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12632917498 / 1000000000000) (-12632917497 / 1000000000000), orderedInterval (-24250264867 / 1000000000000) (-24250264866 / 1000000000000)))) (orderedInterval (-5656323503 / 1000000000000) (-5656312996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3180706853192513 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25698019775 / 1000000000000) (-25698019765 / 1000000000000), orderedInterval (-11825011308 / 1000000000000) (-11825011298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2269902494234129 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12032849567 / 1000000000000) (12032849616 / 1000000000000), orderedInterval (-31268497060 / 1000000000000) (-31268497011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2573827500046791 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6728671563 / 1000000000000) (-6728671562 / 1000000000000), orderedInterval (-30720976412 / 1000000000000) (-30720976411 / 1000000000000)))) (orderedInterval (-3790432422 / 1000000000000) (-3790432342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2145789034533079 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-691689814 / 1000000000000) (-691689813 / 1000000000000), orderedInterval (-34441412172 / 1000000000000) (-34441412171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1895869687262659 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13323502759 / 1000000000000) (-13323502758 / 1000000000000), orderedInterval (-34127661570 / 1000000000000) (-34127661569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (549496930439241 / 800000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (10508142493 / 1000000000000) (10508142509 / 1000000000000), orderedInterval (-28580700909 / 1000000000000) (-28580700893 / 1000000000000)))) (orderedInterval (564392525 / 1000000000000) (564392578 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_chunkChecks1_2 :
    compactCertificate500.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1519937428034027 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24336091745 / 1000000000000) (-24336091744 / 1000000000000), orderedInterval (-32879058107 / 1000000000000) (-32879058106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1288467790590547 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28025819574 / 1000000000000) (28025829604 / 1000000000000), orderedInterval (-34553156362 / 1000000000000) (-34553146332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (806263317873841 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53977620784 / 1000000000000) (53977620786 / 1000000000000), orderedInterval (15511543684 / 1000000000000) (15511543685 / 1000000000000)))) (orderedInterval (7346901997 / 1000000000000) (7346902576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (433611093863247 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (53276884652 / 1000000000000) (53276945675 / 1000000000000), orderedInterval (-55330222876 / 1000000000000) (-55330161853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1177338469210741 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-8788694781 / 1000000000000) (-8788694753 / 1000000000000), orderedInterval (45684103020 / 1000000000000) (45684103048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1607555025945557 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20802593946 / 1000000000000) (20802593947 / 1000000000000), orderedInterval (33905259093 / 1000000000000) (33905259094 / 1000000000000)))) (orderedInterval (-3334041349 / 1000000000000) (-3334040979 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (679736682126159 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53773467959 / 1000000000000) (53773467960 / 1000000000000), orderedInterval (29076662607 / 1000000000000) (29076662608 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2763091874990639 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12039738062 / 1000000000000) (12039738063 / 1000000000000), orderedInterval (27859722684 / 1000000000000) (27859722685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1845617319588001 / 4000000000000) 1 (IntervalRat.scale (743 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13616803199 / 1000000000000) (-13616803198 / 1000000000000), orderedInterval (-34544281829 / 1000000000000) (-34544281828 / 1000000000000)))) (orderedInterval (3913290109 / 1000000000000) (3913290254 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_chunkChecks1 :
    compactCertificate500.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate500.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate500_chunkChecks1_0
    compactCertificate500_chunkChecks1_1 compactCertificate500_chunkChecks1_2

theorem compactCertificate500_chunkChecks2_0 :
    compactCertificate500.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (743 / 2) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41395367960 / 1000000000000) (41395368208 / 1000000000000), orderedInterval (-317843008 / 1000000000000) (-317842760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1094580874290443 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43236624051 / 1000000000000) (-43236624050 / 1000000000000), orderedInterval (-21299355821 / 1000000000000) (-21299355820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (353964965162219 / 800000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10364456303 / 1000000000000) (-10364456302 / 1000000000000), orderedInterval (-36476778629 / 1000000000000) (-36476778628 / 1000000000000)))) (orderedInterval (-15318771069 / 1000000000000) (-15318770936 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (319395969194401 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77388923507 / 1000000000000) (-77388907771 / 1000000000000), orderedInterval (45023020387 / 1000000000000) (45023036123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (857942500015597 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (54341819578 / 1000000000000) (54341819783 / 1000000000000), orderedInterval (-4010222315 / 1000000000000) (-4010222110 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2329480781126649 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30580896188 / 1000000000000) (-30580848034 / 1000000000000), orderedInterval (12594564762 / 1000000000000) (12594612916 / 1000000000000)))) (orderedInterval (-6038281229 / 1000000000000) (-6038272721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1715885000031937 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23062777385 / 1000000000000) (23062781163 / 1000000000000), orderedInterval (-30884137315 / 1000000000000) (-30884133537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2940198193877701 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19006081642 / 1000000000000) (19006081643 / 1000000000000), orderedInterval (22456158296 / 1000000000000) (22456158297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2165736682126159 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32812645316 / 1000000000000) (32812661856 / 1000000000000), orderedInterval (-9986817930 / 1000000000000) (-9986801390 / 1000000000000)))) (orderedInterval (615172651 / 1000000000000) (615173566 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_chunkChecks2_1 :
    compactCertificate500.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3322797014564257 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23839816454 / 1000000000000) (23839842125 / 1000000000000), orderedInterval (-14086625003 / 1000000000000) (-14086599332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1918417750820953 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9861812119 / 1000000000000) (9861812143 / 1000000000000), orderedInterval (-35083495358 / 1000000000000) (-35083495335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3404265963847277 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12632917498 / 1000000000000) (-12632917497 / 1000000000000), orderedInterval (-24250264867 / 1000000000000) (-24250264866 / 1000000000000)))) (orderedInterval (29402588757 / 1000000000000) (29402612249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3180706853192513 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25698019775 / 1000000000000) (-25698019765 / 1000000000000), orderedInterval (-11825011308 / 1000000000000) (-11825011298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2269902494234129 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12032849567 / 1000000000000) (12032849616 / 1000000000000), orderedInterval (-31268497060 / 1000000000000) (-31268497011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2573827500046791 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6728671563 / 1000000000000) (-6728671562 / 1000000000000), orderedInterval (-30720976412 / 1000000000000) (-30720976411 / 1000000000000)))) (orderedInterval (-4872456670 / 1000000000000) (-4872456539 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2145789034533079 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-691689814 / 1000000000000) (-691689813 / 1000000000000), orderedInterval (-34441412172 / 1000000000000) (-34441412171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1895869687262659 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13323502759 / 1000000000000) (-13323502758 / 1000000000000), orderedInterval (-34127661570 / 1000000000000) (-34127661569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (549496930439241 / 800000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (10508142493 / 1000000000000) (10508142509 / 1000000000000), orderedInterval (-28580700909 / 1000000000000) (-28580700893 / 1000000000000)))) (orderedInterval (-2145676052 / 1000000000000) (-2145675974 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_chunkChecks2_2 :
    compactCertificate500.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1519937428034027 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24336091745 / 1000000000000) (-24336091744 / 1000000000000), orderedInterval (-32879058107 / 1000000000000) (-32879058106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1288467790590547 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28025819574 / 1000000000000) (28025829604 / 1000000000000), orderedInterval (-34553156362 / 1000000000000) (-34553146332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (806263317873841 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53977620784 / 1000000000000) (53977620786 / 1000000000000), orderedInterval (15511543684 / 1000000000000) (15511543685 / 1000000000000)))) (orderedInterval (-3415436673 / 1000000000000) (-3415436163 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (433611093863247 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (53276884652 / 1000000000000) (53276945675 / 1000000000000), orderedInterval (-55330222876 / 1000000000000) (-55330161853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1177338469210741 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-8788694781 / 1000000000000) (-8788694753 / 1000000000000), orderedInterval (45684103020 / 1000000000000) (45684103048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1607555025945557 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20802593946 / 1000000000000) (20802593947 / 1000000000000), orderedInterval (33905259093 / 1000000000000) (33905259094 / 1000000000000)))) (orderedInterval (1833359333 / 1000000000000) (1833359471 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (679736682126159 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53773467959 / 1000000000000) (53773467960 / 1000000000000), orderedInterval (29076662607 / 1000000000000) (29076662608 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2763091874990639 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12039738062 / 1000000000000) (12039738063 / 1000000000000), orderedInterval (27859722684 / 1000000000000) (27859722685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1845617319588001 / 4000000000000) 2 (IntervalRat.scale (743 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13616803199 / 1000000000000) (-13616803198 / 1000000000000), orderedInterval (-34544281829 / 1000000000000) (-34544281828 / 1000000000000)))) (orderedInterval (-630967976 / 1000000000000) (-630967762 / 1000000000000))) = true
  rfl'

theorem compactCertificate500_chunkChecks2 :
    compactCertificate500.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate500.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate500_chunkChecks2_0
    compactCertificate500_chunkChecks2_1 compactCertificate500_chunkChecks2_2

theorem compactCertificate500_chunkChecks3_0 :
    compactCertificate500.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (743 / 2) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41395367960 / 1000000000000) (41395368208 / 1000000000000), orderedInterval (-317843008 / 1000000000000) (-317842760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1094580874290443 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43236624051 / 1000000000000) (-43236624050 / 1000000000000), orderedInterval (-21299355821 / 1000000000000) (-21299355820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (353964965162219 / 800000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10364456303 / 1000000000000) (-10364456302 / 1000000000000), orderedInterval (-36476778629 / 1000000000000) (-36476778628 / 1000000000000)))) (orderedInterval (3862690542 / 1000000000000) (3862690680 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (319395969194401 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77388923507 / 1000000000000) (-77388907771 / 1000000000000), orderedInterval (45023020387 / 1000000000000) (45023036123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (857942500015597 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (54341819578 / 1000000000000) (54341819783 / 1000000000000), orderedInterval (-4010222315 / 1000000000000) (-4010222110 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2329480781126649 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30580896188 / 1000000000000) (-30580848034 / 1000000000000), orderedInterval (12594564762 / 1000000000000) (12594612916 / 1000000000000)))) (orderedInterval (3498408097 / 1000000000000) (3498421415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1715885000031937 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23062777385 / 1000000000000) (23062781163 / 1000000000000), orderedInterval (-30884137315 / 1000000000000) (-30884133537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2940198193877701 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19006081642 / 1000000000000) (19006081643 / 1000000000000), orderedInterval (22456158296 / 1000000000000) (22456158297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2165736682126159 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32812645316 / 1000000000000) (32812661856 / 1000000000000), orderedInterval (-9986817930 / 1000000000000) (-9986801390 / 1000000000000)))) (orderedInterval (6110638025 / 1000000000000) (6110639382 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate500_chunkChecks3_1 :
    compactCertificate500.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3322797014564257 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23839816454 / 1000000000000) (23839842125 / 1000000000000), orderedInterval (-14086625003 / 1000000000000) (-14086599332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1918417750820953 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9861812119 / 1000000000000) (9861812143 / 1000000000000), orderedInterval (-35083495358 / 1000000000000) (-35083495335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3404265963847277 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12632917498 / 1000000000000) (-12632917497 / 1000000000000), orderedInterval (-24250264867 / 1000000000000) (-24250264866 / 1000000000000)))) (orderedInterval (18976393995 / 1000000000000) (18976446493 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3180706853192513 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25698019775 / 1000000000000) (-25698019765 / 1000000000000), orderedInterval (-11825011308 / 1000000000000) (-11825011298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2269902494234129 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12032849567 / 1000000000000) (12032849616 / 1000000000000), orderedInterval (-31268497060 / 1000000000000) (-31268497011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2573827500046791 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6728671563 / 1000000000000) (-6728671562 / 1000000000000), orderedInterval (-30720976412 / 1000000000000) (-30720976411 / 1000000000000)))) (orderedInterval (7650630115 / 1000000000000) (7650630335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2145789034533079 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-691689814 / 1000000000000) (-691689813 / 1000000000000), orderedInterval (-34441412172 / 1000000000000) (-34441412171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1895869687262659 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13323502759 / 1000000000000) (-13323502758 / 1000000000000), orderedInterval (-34127661570 / 1000000000000) (-34127661569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (549496930439241 / 800000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (10508142493 / 1000000000000) (10508142509 / 1000000000000), orderedInterval (-28580700909 / 1000000000000) (-28580700893 / 1000000000000)))) (orderedInterval (1772701268 / 1000000000000) (1772701389 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate500_chunkChecks3_2 :
    compactCertificate500.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1519937428034027 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24336091745 / 1000000000000) (-24336091744 / 1000000000000), orderedInterval (-32879058107 / 1000000000000) (-32879058106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1288467790590547 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28025819574 / 1000000000000) (28025829604 / 1000000000000), orderedInterval (-34553156362 / 1000000000000) (-34553146332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (806263317873841 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53977620784 / 1000000000000) (53977620786 / 1000000000000), orderedInterval (15511543684 / 1000000000000) (15511543685 / 1000000000000)))) (orderedInterval (-6971877227 / 1000000000000) (-6971876776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (433611093863247 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (53276884652 / 1000000000000) (53276945675 / 1000000000000), orderedInterval (-55330222876 / 1000000000000) (-55330161853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1177338469210741 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-8788694781 / 1000000000000) (-8788694753 / 1000000000000), orderedInterval (45684103020 / 1000000000000) (45684103048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1607555025945557 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20802593946 / 1000000000000) (20802593947 / 1000000000000), orderedInterval (33905259093 / 1000000000000) (33905259094 / 1000000000000)))) (orderedInterval (3774814943 / 1000000000000) (3774815013 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (679736682126159 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53773467959 / 1000000000000) (53773467960 / 1000000000000), orderedInterval (29076662607 / 1000000000000) (29076662608 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2763091874990639 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12039738062 / 1000000000000) (12039738063 / 1000000000000), orderedInterval (27859722684 / 1000000000000) (27859722685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1845617319588001 / 4000000000000) 3 (IntervalRat.scale (743 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13616803199 / 1000000000000) (-13616803198 / 1000000000000), orderedInterval (-34544281829 / 1000000000000) (-34544281828 / 1000000000000)))) (orderedInterval (2146732386 / 1000000000000) (2146732716 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate500_chunkChecks3 :
    compactCertificate500.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate500.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate500_chunkChecks3_0
    compactCertificate500_chunkChecks3_1 compactCertificate500_chunkChecks3_2

theorem compactCertificate500_chunkChecks4_0 :
    compactCertificate500.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (743 / 2) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41395367960 / 1000000000000) (41395368208 / 1000000000000), orderedInterval (-317843008 / 1000000000000) (-317842760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1094580874290443 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43236624051 / 1000000000000) (-43236624050 / 1000000000000), orderedInterval (-21299355821 / 1000000000000) (-21299355820 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (353964965162219 / 800000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-10364456303 / 1000000000000) (-10364456302 / 1000000000000), orderedInterval (-36476778629 / 1000000000000) (-36476778628 / 1000000000000)))) (orderedInterval (15044421182 / 1000000000000) (15044421327 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (319395969194401 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77388923507 / 1000000000000) (-77388907771 / 1000000000000), orderedInterval (45023020387 / 1000000000000) (45023036123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (857942500015597 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (54341819578 / 1000000000000) (54341819783 / 1000000000000), orderedInterval (-4010222315 / 1000000000000) (-4010222110 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2329480781126649 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30580896188 / 1000000000000) (-30580848034 / 1000000000000), orderedInterval (12594564762 / 1000000000000) (12594612916 / 1000000000000)))) (orderedInterval (13331932553 / 1000000000000) (13331953460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1715885000031937 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23062777385 / 1000000000000) (23062781163 / 1000000000000), orderedInterval (-30884137315 / 1000000000000) (-30884133537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2940198193877701 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19006081642 / 1000000000000) (19006081643 / 1000000000000), orderedInterval (22456158296 / 1000000000000) (22456158297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2165736682126159 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32812645316 / 1000000000000) (32812661856 / 1000000000000), orderedInterval (-9986817930 / 1000000000000) (-9986801390 / 1000000000000)))) (orderedInterval (-5439491303 / 1000000000000) (-5439489275 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate500_chunkChecks4_1 :
    compactCertificate500.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3322797014564257 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23839816454 / 1000000000000) (23839842125 / 1000000000000), orderedInterval (-14086625003 / 1000000000000) (-14086599332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1918417750820953 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (9861812119 / 1000000000000) (9861812143 / 1000000000000), orderedInterval (-35083495358 / 1000000000000) (-35083495335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3404265963847277 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12632917498 / 1000000000000) (-12632917497 / 1000000000000), orderedInterval (-24250264867 / 1000000000000) (-24250264866 / 1000000000000)))) (orderedInterval (-153437358425 / 1000000000000) (-153437240924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3180706853192513 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25698019775 / 1000000000000) (-25698019765 / 1000000000000), orderedInterval (-11825011308 / 1000000000000) (-11825011298 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2269902494234129 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12032849567 / 1000000000000) (12032849616 / 1000000000000), orderedInterval (-31268497060 / 1000000000000) (-31268497011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2573827500046791 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6728671563 / 1000000000000) (-6728671562 / 1000000000000), orderedInterval (-30720976412 / 1000000000000) (-30720976411 / 1000000000000)))) (orderedInterval (16198270245 / 1000000000000) (16198270624 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2145789034533079 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-691689814 / 1000000000000) (-691689813 / 1000000000000), orderedInterval (-34441412172 / 1000000000000) (-34441412171 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1895869687262659 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13323502759 / 1000000000000) (-13323502758 / 1000000000000), orderedInterval (-34127661570 / 1000000000000) (-34127661569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (549496930439241 / 800000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (10508142493 / 1000000000000) (10508142509 / 1000000000000), orderedInterval (-28580700909 / 1000000000000) (-28580700893 / 1000000000000)))) (orderedInterval (5119943478 / 1000000000000) (5119943670 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate500_chunkChecks4_2 :
    compactCertificate500.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1519937428034027 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24336091745 / 1000000000000) (-24336091744 / 1000000000000), orderedInterval (-32879058107 / 1000000000000) (-32879058106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1288467790590547 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28025819574 / 1000000000000) (28025829604 / 1000000000000), orderedInterval (-34553156362 / 1000000000000) (-34553146332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (806263317873841 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53977620784 / 1000000000000) (53977620786 / 1000000000000), orderedInterval (15511543684 / 1000000000000) (15511543685 / 1000000000000)))) (orderedInterval (3552195481 / 1000000000000) (3552195883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (433611093863247 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (53276884652 / 1000000000000) (53276945675 / 1000000000000), orderedInterval (-55330222876 / 1000000000000) (-55330161853 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1177338469210741 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-8788694781 / 1000000000000) (-8788694753 / 1000000000000), orderedInterval (45684103020 / 1000000000000) (45684103048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1607555025945557 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20802593946 / 1000000000000) (20802593947 / 1000000000000), orderedInterval (33905259093 / 1000000000000) (33905259094 / 1000000000000)))) (orderedInterval (-2132383580 / 1000000000000) (-2132383528 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (679736682126159 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53773467959 / 1000000000000) (53773467960 / 1000000000000), orderedInterval (29076662607 / 1000000000000) (29076662608 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2763091874990639 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12039738062 / 1000000000000) (12039738063 / 1000000000000), orderedInterval (27859722684 / 1000000000000) (27859722685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1845617319588001 / 4000000000000) 4 (IntervalRat.scale (743 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-13616803199 / 1000000000000) (-13616803198 / 1000000000000), orderedInterval (-34544281829 / 1000000000000) (-34544281828 / 1000000000000)))) (orderedInterval (-5633365170 / 1000000000000) (-5633364640 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate500_chunkChecks4 :
    compactCertificate500.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate500.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate500_chunkChecks4_0
    compactCertificate500_chunkChecks4_1 compactCertificate500_chunkChecks4_2

theorem compactCertificate500_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate500.chunkCheck r b = true :=
  compactCertificate500.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate500_chunkChecks0
    · exact compactCertificate500_chunkChecks1
    · exact compactCertificate500_chunkChecks2
    · exact compactCertificate500_chunkChecks3
    · exact compactCertificate500_chunkChecks4)

theorem compactCertificate500_coefficient0 :
    compactCertificate500.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate500_coefficient1 :
    compactCertificate500.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate500_coefficient2 :
    compactCertificate500.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate500_coefficient3 :
    compactCertificate500.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate500_coefficient4 :
    compactCertificate500.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate500_coefficients : ∀ r : Fin 5,
    compactCertificate500.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate500_coefficient0
  · exact compactCertificate500_coefficient1
  · exact compactCertificate500_coefficient2
  · exact compactCertificate500_coefficient3
  · exact compactCertificate500_coefficient4

theorem compactCertificate500_lower : (1 : ℚ) ≤ compactCertificate500.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate500, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate500_proves {t : ℝ} (ht : t ∈ compactCertificate500.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate500.proves compactCertificate500_states compactCertificate500_chunks
    compactCertificate500_coefficients compactCertificate500_lower ht

end Erdos232
