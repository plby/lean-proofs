/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate350 : CompactCertificate where
  left := 221
  right := 222
  center := 443 / 2
  grid := fun i =>
    match i.val with
    | 0 => 71
    | 1 => 52
    | 2 => 84
    | 3 => 15
    | 4 => 41
    | 5 => 111
    | 6 => 81
    | 7 => 140
    | 8 => 103
    | 9 => 158
    | 10 => 91
    | 11 => 162
    | 12 => 151
    | 13 => 108
    | 14 => 122
    | 15 => 102
    | 16 => 90
    | 17 => 130
    | 18 => 72
    | 19 => 61
    | 20 => 38
    | 21 => 21
    | 22 => 56
    | 23 => 76
    | 24 => 32
    | 25 => 131
    | _ => 88
  point := fun i =>
    match i.val with
    | 0 => 443 / 2
    | 1 => 652623589920143 / 4000000000000
    | 2 => 211045059982319 / 800000000000
    | 3 => 190433935872301 / 4000000000000
    | 4 => 511532338501897 / 4000000000000
    | 5 => 1388909806243749 / 4000000000000
    | 6 => 1023064677004237 / 4000000000000
    | 7 => 1753038761625601 / 4000000000000
    | 8 => 1291280417472259 / 4000000000000
    | 9 => 1981156228064557 / 4000000000000
    | 10 => 1143821081579653 / 4000000000000
    | 11 => 2029730581405577 / 4000000000000
    | 12 => 1896437598875213 / 4000000000000
    | 13 => 1353387355243229 / 4000000000000
    | 14 => 1534597015505691 / 4000000000000
    | 15 => 1279387001747179 / 4000000000000
    | 16 => 1130377215958759 / 4000000000000
    | 17 => 327627375753141 / 800000000000
    | 18 => 906234563417327 / 4000000000000
    | 19 => 768225075681847 / 4000000000000
    | 20 => 480719582527741 / 4000000000000
    | 21 => 258532590284547 / 4000000000000
    | 22 => 701966274374641 / 4000000000000
    | 23 => 958474934715857 / 4000000000000
    | 24 => 405280417472259 / 4000000000000
    | 25 => 1647442396528739 / 4000000000000
    | _ => 1100415171705901 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (37252758249 / 1000000000000) (37252795017 / 1000000000000), orderedInterval (-38637458488 / 1000000000000) (-38637421720 / 1000000000000))
    | 1 => (orderedInterval (34112725542 / 1000000000000) (34112725543 / 1000000000000), orderedInterval (52223658022 / 1000000000000) (52223658023 / 1000000000000))
    | 2 => (orderedInterval (31551499059 / 1000000000000) (31551499060 / 1000000000000), orderedInterval (37592723794 / 1000000000000) (37592723795 / 1000000000000))
    | 3 => (orderedInterval (-110351648542 / 1000000000000) (-110351648541 / 1000000000000), orderedInterval (-33393890919 / 1000000000000) (-33393890918 / 1000000000000))
    | 4 => (orderedInterval (9691369901 / 1000000000000) (9691369946 / 1000000000000), orderedInterval (-69925321667 / 1000000000000) (-69925321623 / 1000000000000))
    | 5 => (orderedInterval (27724914023 / 1000000000000) (27724925045 / 1000000000000), orderedInterval (-32670688077 / 1000000000000) (-32670677054 / 1000000000000))
    | 6 => (orderedInterval (-43510551940 / 1000000000000) (-43510519507 / 1000000000000), orderedInterval (24496110443 / 1000000000000) (24496142876 / 1000000000000))
    | 7 => (orderedInterval (-26754479444 / 1000000000000) (-26754464974 / 1000000000000), orderedInterval (27174700875 / 1000000000000) (27174715344 / 1000000000000))
    | 8 => (orderedInterval (-935692512 / 1000000000000) (-935692511 / 1000000000000), orderedInterval (-44396571349 / 1000000000000) (-44396571348 / 1000000000000))
    | 9 => (orderedInterval (-10507084996 / 1000000000000) (-10507084966 / 1000000000000), orderedInterval (34288175073 / 1000000000000) (34288175103 / 1000000000000))
    | 10 => (orderedInterval (-35612625528 / 1000000000000) (-35612625527 / 1000000000000), orderedInterval (-30889820606 / 1000000000000) (-30889820605 / 1000000000000))
    | 11 => (orderedInterval (-23361189596 / 1000000000000) (-23361183911 / 1000000000000), orderedInterval (26647154250 / 1000000000000) (26647159934 / 1000000000000))
    | 12 => (orderedInterval (-18017844276 / 1000000000000) (-18017844275 / 1000000000000), orderedInterval (-31889107699 / 1000000000000) (-31889107698 / 1000000000000))
    | 13 => (orderedInterval (-6916688603 / 1000000000000) (-6916688590 / 1000000000000), orderedInterval (42832190592 / 1000000000000) (42832190604 / 1000000000000))
    | 14 => (orderedInterval (37346768415 / 1000000000000) (37346768416 / 1000000000000), orderedInterval (16217783281 / 1000000000000) (16217783282 / 1000000000000))
    | 15 => (orderedInterval (8395347829 / 1000000000000) (8395347830 / 1000000000000), orderedInterval (43803658082 / 1000000000000) (43803658083 / 1000000000000))
    | 16 => (orderedInterval (28189348935 / 1000000000000) (28189348936 / 1000000000000), orderedInterval (38135604967 / 1000000000000) (38135604968 / 1000000000000))
    | 17 => (orderedInterval (37150686635 / 1000000000000) (37150700273 / 1000000000000), orderedInterval (-13248477089 / 1000000000000) (-13248463452 / 1000000000000))
    | 18 => (orderedInterval (48358993183 / 1000000000000) (48358993184 / 1000000000000), orderedInterval (21604080440 / 1000000000000) (21604080441 / 1000000000000))
    | 19 => (orderedInterval (-53741273965 / 1000000000000) (-53741273964 / 1000000000000), orderedInterval (-20514960984 / 1000000000000) (-20514960983 / 1000000000000))
    | 20 => (orderedInterval (72775622569 / 1000000000000) (72775622615 / 1000000000000), orderedInterval (-1244299680 / 1000000000000) (-1244299633 / 1000000000000))
    | 21 => (orderedInterval (52450738557 / 1000000000000) (52450748974 / 1000000000000), orderedInterval (-84660058954 / 1000000000000) (-84660048537 / 1000000000000))
    | 22 => (orderedInterval (20486553164 / 1000000000000) (20486553165 / 1000000000000), orderedInterval (56580397525 / 1000000000000) (56580397526 / 1000000000000))
    | 23 => (orderedInterval (51411427493 / 1000000000000) (51411427737 / 1000000000000), orderedInterval (-3803544738 / 1000000000000) (-3803544494 / 1000000000000))
    | 24 => (orderedInterval (79266236373 / 1000000000000) (79266236407 / 1000000000000), orderedInterval (-589931774 / 1000000000000) (-589931740 / 1000000000000))
    | 25 => (orderedInterval (-34985691467 / 1000000000000) (-34985691465 / 1000000000000), orderedInterval (-17894008192 / 1000000000000) (-17894008191 / 1000000000000))
    | _ => (orderedInterval (-26016426941 / 1000000000000) (-26016422849 / 1000000000000), orderedInterval (40510287779 / 1000000000000) (40510291871 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (16935031611 / 1000000000000) (16935046201 / 1000000000000)
      | 1 => orderedInterval (-419868998 / 1000000000000) (-419868186 / 1000000000000)
      | 2 => orderedInterval (802600896 / 1000000000000) (802601355 / 1000000000000)
      | 3 => orderedInterval (-4092551149 / 1000000000000) (-4092550247 / 1000000000000)
      | 4 => orderedInterval (-517780379 / 1000000000000) (-517780350 / 1000000000000)
      | 5 => orderedInterval (-565031748 / 1000000000000) (-565031377 / 1000000000000)
      | 6 => orderedInterval (-2321253684 / 1000000000000) (-2321253626 / 1000000000000)
      | 7 => orderedInterval (-5373398561 / 1000000000000) (-5373398323 / 1000000000000)
      | _ => orderedInterval (8207111360 / 1000000000000) (8207112190 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12328766474 / 1000000000000) (-12328751882 / 1000000000000)
      | 1 => orderedInterval (2244707840 / 1000000000000) (2244709100 / 1000000000000)
      | 2 => orderedInterval (-3222202671 / 1000000000000) (-3222201766 / 1000000000000)
      | 3 => orderedInterval (-7900116625 / 1000000000000) (-7900114580 / 1000000000000)
      | 4 => orderedInterval (7277086232 / 1000000000000) (7277086277 / 1000000000000)
      | 5 => orderedInterval (-2681073502 / 1000000000000) (-2681072825 / 1000000000000)
      | 6 => orderedInterval (-2548402218 / 1000000000000) (-2548402165 / 1000000000000)
      | 7 => orderedInterval (-245505945 / 1000000000000) (-245505844 / 1000000000000)
      | _ => orderedInterval (-6733421665 / 1000000000000) (-6733420625 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-17508790972 / 1000000000000) (-17508776312 / 1000000000000)
      | 1 => orderedInterval (4660082765 / 1000000000000) (4660084739 / 1000000000000)
      | 2 => orderedInterval (-3168016081 / 1000000000000) (-3168014290 / 1000000000000)
      | 3 => orderedInterval (12527289502 / 1000000000000) (12527294169 / 1000000000000)
      | 4 => orderedInterval (570012667 / 1000000000000) (570012741 / 1000000000000)
      | 5 => orderedInterval (-815909464 / 1000000000000) (-815908221 / 1000000000000)
      | 6 => orderedInterval (5116660052 / 1000000000000) (5116660102 / 1000000000000)
      | 7 => orderedInterval (4986403008 / 1000000000000) (4986403071 / 1000000000000)
      | _ => orderedInterval (-17445854231 / 1000000000000) (-17445852914 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11472028509 / 1000000000000) (11472043171 / 1000000000000)
      | 1 => orderedInterval (-8480414587 / 1000000000000) (-8480411496 / 1000000000000)
      | 2 => orderedInterval (9828319963 / 1000000000000) (9828323499 / 1000000000000)
      | 3 => orderedInterval (27441162552 / 1000000000000) (27441173201 / 1000000000000)
      | 4 => orderedInterval (-19657853285 / 1000000000000) (-19657853160 / 1000000000000)
      | 5 => orderedInterval (5156667796 / 1000000000000) (5156670080 / 1000000000000)
      | 6 => orderedInterval (2922842820 / 1000000000000) (2922842868 / 1000000000000)
      | 7 => orderedInterval (207991681 / 1000000000000) (207991735 / 1000000000000)
      | _ => orderedInterval (5276994574 / 1000000000000) (5276996248 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (18480650392 / 1000000000000) (18480665124 / 1000000000000)
      | 1 => orderedInterval (-11783955527 / 1000000000000) (-11783950670 / 1000000000000)
      | 2 => orderedInterval (12456473883 / 1000000000000) (12456480885 / 1000000000000)
      | 3 => orderedInterval (-52372383505 / 1000000000000) (-52372359126 / 1000000000000)
      | 4 => orderedInterval (1743226557 / 1000000000000) (1743226773 / 1000000000000)
      | 5 => orderedInterval (7216627249 / 1000000000000) (7216631462 / 1000000000000)
      | 6 => orderedInterval (-6564861464 / 1000000000000) (-6564861416 / 1000000000000)
      | 7 => orderedInterval (-5588244005 / 1000000000000) (-5588243951 / 1000000000000)
      | _ => orderedInterval (45631494856 / 1000000000000) (45631497014 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (12654859348 / 1000000000000) (12654877637 / 1000000000000)
    | 1 => orderedInterval (-26137695028 / 1000000000000) (-26137674310 / 1000000000000)
    | 2 => orderedInterval (-11078122754 / 1000000000000) (-11078096915 / 1000000000000)
    | 3 => orderedInterval (34167740023 / 1000000000000) (34167776146 / 1000000000000)
    | _ => orderedInterval (9219028436 / 1000000000000) (9219086095 / 1000000000000)

theorem compactCertificate350_stateChecks0 :
    compactCertificate350.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (443 / 2)) (orderedInterval (37252758249 / 1000000000000) (37252795017 / 1000000000000), orderedInterval (-38637458488 / 1000000000000) (-38637421720 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (652623589920143 / 4000000000000)) (orderedInterval (34112725542 / 1000000000000) (34112725543 / 1000000000000), orderedInterval (52223658022 / 1000000000000) (52223658023 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (211045059982319 / 800000000000)) (orderedInterval (31551499059 / 1000000000000) (31551499060 / 1000000000000), orderedInterval (37592723794 / 1000000000000) (37592723795 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_stateChecks1 :
    compactCertificate350.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (190433935872301 / 4000000000000)) (orderedInterval (-110351648542 / 1000000000000) (-110351648541 / 1000000000000), orderedInterval (-33393890919 / 1000000000000) (-33393890918 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (511532338501897 / 4000000000000)) (orderedInterval (9691369901 / 1000000000000) (9691369946 / 1000000000000), orderedInterval (-69925321667 / 1000000000000) (-69925321623 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1388909806243749 / 4000000000000)) (orderedInterval (27724914023 / 1000000000000) (27724925045 / 1000000000000), orderedInterval (-32670688077 / 1000000000000) (-32670677054 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_stateChecks2 :
    compactCertificate350.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1023064677004237 / 4000000000000)) (orderedInterval (-43510551940 / 1000000000000) (-43510519507 / 1000000000000), orderedInterval (24496110443 / 1000000000000) (24496142876 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1753038761625601 / 4000000000000)) (orderedInterval (-26754479444 / 1000000000000) (-26754464974 / 1000000000000), orderedInterval (27174700875 / 1000000000000) (27174715344 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1291280417472259 / 4000000000000)) (orderedInterval (-935692512 / 1000000000000) (-935692511 / 1000000000000), orderedInterval (-44396571349 / 1000000000000) (-44396571348 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_stateChecks3 :
    compactCertificate350.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1981156228064557 / 4000000000000)) (orderedInterval (-10507084996 / 1000000000000) (-10507084966 / 1000000000000), orderedInterval (34288175073 / 1000000000000) (34288175103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1143821081579653 / 4000000000000)) (orderedInterval (-35612625528 / 1000000000000) (-35612625527 / 1000000000000), orderedInterval (-30889820606 / 1000000000000) (-30889820605 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2029730581405577 / 4000000000000)) (orderedInterval (-23361189596 / 1000000000000) (-23361183911 / 1000000000000), orderedInterval (26647154250 / 1000000000000) (26647159934 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_stateChecks4 :
    compactCertificate350.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1896437598875213 / 4000000000000)) (orderedInterval (-18017844276 / 1000000000000) (-18017844275 / 1000000000000), orderedInterval (-31889107699 / 1000000000000) (-31889107698 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1353387355243229 / 4000000000000)) (orderedInterval (-6916688603 / 1000000000000) (-6916688590 / 1000000000000), orderedInterval (42832190592 / 1000000000000) (42832190604 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1534597015505691 / 4000000000000)) (orderedInterval (37346768415 / 1000000000000) (37346768416 / 1000000000000), orderedInterval (16217783281 / 1000000000000) (16217783282 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_stateChecks5 :
    compactCertificate350.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1279387001747179 / 4000000000000)) (orderedInterval (8395347829 / 1000000000000) (8395347830 / 1000000000000), orderedInterval (43803658082 / 1000000000000) (43803658083 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1130377215958759 / 4000000000000)) (orderedInterval (28189348935 / 1000000000000) (28189348936 / 1000000000000), orderedInterval (38135604967 / 1000000000000) (38135604968 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (327627375753141 / 800000000000)) (orderedInterval (37150686635 / 1000000000000) (37150700273 / 1000000000000), orderedInterval (-13248477089 / 1000000000000) (-13248463452 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_stateChecks6 :
    compactCertificate350.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (906234563417327 / 4000000000000)) (orderedInterval (48358993183 / 1000000000000) (48358993184 / 1000000000000), orderedInterval (21604080440 / 1000000000000) (21604080441 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (768225075681847 / 4000000000000)) (orderedInterval (-53741273965 / 1000000000000) (-53741273964 / 1000000000000), orderedInterval (-20514960984 / 1000000000000) (-20514960983 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (480719582527741 / 4000000000000)) (orderedInterval (72775622569 / 1000000000000) (72775622615 / 1000000000000), orderedInterval (-1244299680 / 1000000000000) (-1244299633 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_stateChecks7 :
    compactCertificate350.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (258532590284547 / 4000000000000)) (orderedInterval (52450738557 / 1000000000000) (52450748974 / 1000000000000), orderedInterval (-84660058954 / 1000000000000) (-84660048537 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (701966274374641 / 4000000000000)) (orderedInterval (20486553164 / 1000000000000) (20486553165 / 1000000000000), orderedInterval (56580397525 / 1000000000000) (56580397526 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (958474934715857 / 4000000000000)) (orderedInterval (51411427493 / 1000000000000) (51411427737 / 1000000000000), orderedInterval (-3803544738 / 1000000000000) (-3803544494 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_stateChecks8 :
    compactCertificate350.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (405280417472259 / 4000000000000)) (orderedInterval (79266236373 / 1000000000000) (79266236407 / 1000000000000), orderedInterval (-589931774 / 1000000000000) (-589931740 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1647442396528739 / 4000000000000)) (orderedInterval (-34985691467 / 1000000000000) (-34985691465 / 1000000000000), orderedInterval (-17894008192 / 1000000000000) (-17894008191 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1100415171705901 / 4000000000000)) (orderedInterval (-26016426941 / 1000000000000) (-26016422849 / 1000000000000), orderedInterval (40510287779 / 1000000000000) (40510291871 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_states : ∀ j,
    BesselStateValid (compactCertificate350.point j) (compactCertificate350.state j) :=
  compactCertificate350.statesValid_of_checks3 compactCertificate350_stateChecks0
    compactCertificate350_stateChecks1 compactCertificate350_stateChecks2
    compactCertificate350_stateChecks3 compactCertificate350_stateChecks4
    compactCertificate350_stateChecks5 compactCertificate350_stateChecks6
    compactCertificate350_stateChecks7 compactCertificate350_stateChecks8

theorem compactCertificate350_chunkChecks0_0 :
    compactCertificate350.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (443 / 2) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37252758249 / 1000000000000) (37252795017 / 1000000000000), orderedInterval (-38637458488 / 1000000000000) (-38637421720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (652623589920143 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34112725542 / 1000000000000) (34112725543 / 1000000000000), orderedInterval (52223658022 / 1000000000000) (52223658023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (211045059982319 / 800000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31551499059 / 1000000000000) (31551499060 / 1000000000000), orderedInterval (37592723794 / 1000000000000) (37592723795 / 1000000000000)))) (orderedInterval (16935031611 / 1000000000000) (16935046201 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (190433935872301 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-110351648542 / 1000000000000) (-110351648541 / 1000000000000), orderedInterval (-33393890919 / 1000000000000) (-33393890918 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (511532338501897 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9691369901 / 1000000000000) (9691369946 / 1000000000000), orderedInterval (-69925321667 / 1000000000000) (-69925321623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1388909806243749 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27724914023 / 1000000000000) (27724925045 / 1000000000000), orderedInterval (-32670688077 / 1000000000000) (-32670677054 / 1000000000000)))) (orderedInterval (-419868998 / 1000000000000) (-419868186 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1023064677004237 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-43510551940 / 1000000000000) (-43510519507 / 1000000000000), orderedInterval (24496110443 / 1000000000000) (24496142876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1753038761625601 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26754479444 / 1000000000000) (-26754464974 / 1000000000000), orderedInterval (27174700875 / 1000000000000) (27174715344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1291280417472259 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-935692512 / 1000000000000) (-935692511 / 1000000000000), orderedInterval (-44396571349 / 1000000000000) (-44396571348 / 1000000000000)))) (orderedInterval (802600896 / 1000000000000) (802601355 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_chunkChecks0_1 :
    compactCertificate350.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1981156228064557 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10507084996 / 1000000000000) (-10507084966 / 1000000000000), orderedInterval (34288175073 / 1000000000000) (34288175103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1143821081579653 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35612625528 / 1000000000000) (-35612625527 / 1000000000000), orderedInterval (-30889820606 / 1000000000000) (-30889820605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2029730581405577 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23361189596 / 1000000000000) (-23361183911 / 1000000000000), orderedInterval (26647154250 / 1000000000000) (26647159934 / 1000000000000)))) (orderedInterval (-4092551149 / 1000000000000) (-4092550247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1896437598875213 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18017844276 / 1000000000000) (-18017844275 / 1000000000000), orderedInterval (-31889107699 / 1000000000000) (-31889107698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1353387355243229 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6916688603 / 1000000000000) (-6916688590 / 1000000000000), orderedInterval (42832190592 / 1000000000000) (42832190604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1534597015505691 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37346768415 / 1000000000000) (37346768416 / 1000000000000), orderedInterval (16217783281 / 1000000000000) (16217783282 / 1000000000000)))) (orderedInterval (-517780379 / 1000000000000) (-517780350 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1279387001747179 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8395347829 / 1000000000000) (8395347830 / 1000000000000), orderedInterval (43803658082 / 1000000000000) (43803658083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1130377215958759 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28189348935 / 1000000000000) (28189348936 / 1000000000000), orderedInterval (38135604967 / 1000000000000) (38135604968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (327627375753141 / 800000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37150686635 / 1000000000000) (37150700273 / 1000000000000), orderedInterval (-13248477089 / 1000000000000) (-13248463452 / 1000000000000)))) (orderedInterval (-565031748 / 1000000000000) (-565031377 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_chunkChecks0_2 :
    compactCertificate350.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (906234563417327 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48358993183 / 1000000000000) (48358993184 / 1000000000000), orderedInterval (21604080440 / 1000000000000) (21604080441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (768225075681847 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-53741273965 / 1000000000000) (-53741273964 / 1000000000000), orderedInterval (-20514960984 / 1000000000000) (-20514960983 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (480719582527741 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72775622569 / 1000000000000) (72775622615 / 1000000000000), orderedInterval (-1244299680 / 1000000000000) (-1244299633 / 1000000000000)))) (orderedInterval (-2321253684 / 1000000000000) (-2321253626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (258532590284547 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (52450738557 / 1000000000000) (52450748974 / 1000000000000), orderedInterval (-84660058954 / 1000000000000) (-84660048537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (701966274374641 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20486553164 / 1000000000000) (20486553165 / 1000000000000), orderedInterval (56580397525 / 1000000000000) (56580397526 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (958474934715857 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51411427493 / 1000000000000) (51411427737 / 1000000000000), orderedInterval (-3803544738 / 1000000000000) (-3803544494 / 1000000000000)))) (orderedInterval (-5373398561 / 1000000000000) (-5373398323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (405280417472259 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (79266236373 / 1000000000000) (79266236407 / 1000000000000), orderedInterval (-589931774 / 1000000000000) (-589931740 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1647442396528739 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34985691467 / 1000000000000) (-34985691465 / 1000000000000), orderedInterval (-17894008192 / 1000000000000) (-17894008191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1100415171705901 / 4000000000000) 0 (IntervalRat.scale (443 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26016426941 / 1000000000000) (-26016422849 / 1000000000000), orderedInterval (40510287779 / 1000000000000) (40510291871 / 1000000000000)))) (orderedInterval (8207111360 / 1000000000000) (8207112190 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_chunkChecks0 :
    compactCertificate350.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate350.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate350_chunkChecks0_0
    compactCertificate350_chunkChecks0_1 compactCertificate350_chunkChecks0_2

theorem compactCertificate350_chunkChecks1_0 :
    compactCertificate350.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (443 / 2) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37252758249 / 1000000000000) (37252795017 / 1000000000000), orderedInterval (-38637458488 / 1000000000000) (-38637421720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (652623589920143 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34112725542 / 1000000000000) (34112725543 / 1000000000000), orderedInterval (52223658022 / 1000000000000) (52223658023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (211045059982319 / 800000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31551499059 / 1000000000000) (31551499060 / 1000000000000), orderedInterval (37592723794 / 1000000000000) (37592723795 / 1000000000000)))) (orderedInterval (-12328766474 / 1000000000000) (-12328751882 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (190433935872301 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-110351648542 / 1000000000000) (-110351648541 / 1000000000000), orderedInterval (-33393890919 / 1000000000000) (-33393890918 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (511532338501897 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9691369901 / 1000000000000) (9691369946 / 1000000000000), orderedInterval (-69925321667 / 1000000000000) (-69925321623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1388909806243749 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27724914023 / 1000000000000) (27724925045 / 1000000000000), orderedInterval (-32670688077 / 1000000000000) (-32670677054 / 1000000000000)))) (orderedInterval (2244707840 / 1000000000000) (2244709100 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1023064677004237 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-43510551940 / 1000000000000) (-43510519507 / 1000000000000), orderedInterval (24496110443 / 1000000000000) (24496142876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1753038761625601 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26754479444 / 1000000000000) (-26754464974 / 1000000000000), orderedInterval (27174700875 / 1000000000000) (27174715344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1291280417472259 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-935692512 / 1000000000000) (-935692511 / 1000000000000), orderedInterval (-44396571349 / 1000000000000) (-44396571348 / 1000000000000)))) (orderedInterval (-3222202671 / 1000000000000) (-3222201766 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_chunkChecks1_1 :
    compactCertificate350.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1981156228064557 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10507084996 / 1000000000000) (-10507084966 / 1000000000000), orderedInterval (34288175073 / 1000000000000) (34288175103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1143821081579653 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35612625528 / 1000000000000) (-35612625527 / 1000000000000), orderedInterval (-30889820606 / 1000000000000) (-30889820605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2029730581405577 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23361189596 / 1000000000000) (-23361183911 / 1000000000000), orderedInterval (26647154250 / 1000000000000) (26647159934 / 1000000000000)))) (orderedInterval (-7900116625 / 1000000000000) (-7900114580 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1896437598875213 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18017844276 / 1000000000000) (-18017844275 / 1000000000000), orderedInterval (-31889107699 / 1000000000000) (-31889107698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1353387355243229 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6916688603 / 1000000000000) (-6916688590 / 1000000000000), orderedInterval (42832190592 / 1000000000000) (42832190604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1534597015505691 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37346768415 / 1000000000000) (37346768416 / 1000000000000), orderedInterval (16217783281 / 1000000000000) (16217783282 / 1000000000000)))) (orderedInterval (7277086232 / 1000000000000) (7277086277 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1279387001747179 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8395347829 / 1000000000000) (8395347830 / 1000000000000), orderedInterval (43803658082 / 1000000000000) (43803658083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1130377215958759 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28189348935 / 1000000000000) (28189348936 / 1000000000000), orderedInterval (38135604967 / 1000000000000) (38135604968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (327627375753141 / 800000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37150686635 / 1000000000000) (37150700273 / 1000000000000), orderedInterval (-13248477089 / 1000000000000) (-13248463452 / 1000000000000)))) (orderedInterval (-2681073502 / 1000000000000) (-2681072825 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_chunkChecks1_2 :
    compactCertificate350.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (906234563417327 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48358993183 / 1000000000000) (48358993184 / 1000000000000), orderedInterval (21604080440 / 1000000000000) (21604080441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (768225075681847 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-53741273965 / 1000000000000) (-53741273964 / 1000000000000), orderedInterval (-20514960984 / 1000000000000) (-20514960983 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (480719582527741 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72775622569 / 1000000000000) (72775622615 / 1000000000000), orderedInterval (-1244299680 / 1000000000000) (-1244299633 / 1000000000000)))) (orderedInterval (-2548402218 / 1000000000000) (-2548402165 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (258532590284547 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (52450738557 / 1000000000000) (52450748974 / 1000000000000), orderedInterval (-84660058954 / 1000000000000) (-84660048537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (701966274374641 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20486553164 / 1000000000000) (20486553165 / 1000000000000), orderedInterval (56580397525 / 1000000000000) (56580397526 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (958474934715857 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51411427493 / 1000000000000) (51411427737 / 1000000000000), orderedInterval (-3803544738 / 1000000000000) (-3803544494 / 1000000000000)))) (orderedInterval (-245505945 / 1000000000000) (-245505844 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (405280417472259 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (79266236373 / 1000000000000) (79266236407 / 1000000000000), orderedInterval (-589931774 / 1000000000000) (-589931740 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1647442396528739 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34985691467 / 1000000000000) (-34985691465 / 1000000000000), orderedInterval (-17894008192 / 1000000000000) (-17894008191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1100415171705901 / 4000000000000) 1 (IntervalRat.scale (443 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26016426941 / 1000000000000) (-26016422849 / 1000000000000), orderedInterval (40510287779 / 1000000000000) (40510291871 / 1000000000000)))) (orderedInterval (-6733421665 / 1000000000000) (-6733420625 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_chunkChecks1 :
    compactCertificate350.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate350.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate350_chunkChecks1_0
    compactCertificate350_chunkChecks1_1 compactCertificate350_chunkChecks1_2

theorem compactCertificate350_chunkChecks2_0 :
    compactCertificate350.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (443 / 2) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37252758249 / 1000000000000) (37252795017 / 1000000000000), orderedInterval (-38637458488 / 1000000000000) (-38637421720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (652623589920143 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34112725542 / 1000000000000) (34112725543 / 1000000000000), orderedInterval (52223658022 / 1000000000000) (52223658023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (211045059982319 / 800000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31551499059 / 1000000000000) (31551499060 / 1000000000000), orderedInterval (37592723794 / 1000000000000) (37592723795 / 1000000000000)))) (orderedInterval (-17508790972 / 1000000000000) (-17508776312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (190433935872301 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-110351648542 / 1000000000000) (-110351648541 / 1000000000000), orderedInterval (-33393890919 / 1000000000000) (-33393890918 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (511532338501897 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9691369901 / 1000000000000) (9691369946 / 1000000000000), orderedInterval (-69925321667 / 1000000000000) (-69925321623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1388909806243749 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27724914023 / 1000000000000) (27724925045 / 1000000000000), orderedInterval (-32670688077 / 1000000000000) (-32670677054 / 1000000000000)))) (orderedInterval (4660082765 / 1000000000000) (4660084739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1023064677004237 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-43510551940 / 1000000000000) (-43510519507 / 1000000000000), orderedInterval (24496110443 / 1000000000000) (24496142876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1753038761625601 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26754479444 / 1000000000000) (-26754464974 / 1000000000000), orderedInterval (27174700875 / 1000000000000) (27174715344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1291280417472259 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-935692512 / 1000000000000) (-935692511 / 1000000000000), orderedInterval (-44396571349 / 1000000000000) (-44396571348 / 1000000000000)))) (orderedInterval (-3168016081 / 1000000000000) (-3168014290 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_chunkChecks2_1 :
    compactCertificate350.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1981156228064557 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10507084996 / 1000000000000) (-10507084966 / 1000000000000), orderedInterval (34288175073 / 1000000000000) (34288175103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1143821081579653 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35612625528 / 1000000000000) (-35612625527 / 1000000000000), orderedInterval (-30889820606 / 1000000000000) (-30889820605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2029730581405577 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23361189596 / 1000000000000) (-23361183911 / 1000000000000), orderedInterval (26647154250 / 1000000000000) (26647159934 / 1000000000000)))) (orderedInterval (12527289502 / 1000000000000) (12527294169 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1896437598875213 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18017844276 / 1000000000000) (-18017844275 / 1000000000000), orderedInterval (-31889107699 / 1000000000000) (-31889107698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1353387355243229 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6916688603 / 1000000000000) (-6916688590 / 1000000000000), orderedInterval (42832190592 / 1000000000000) (42832190604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1534597015505691 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37346768415 / 1000000000000) (37346768416 / 1000000000000), orderedInterval (16217783281 / 1000000000000) (16217783282 / 1000000000000)))) (orderedInterval (570012667 / 1000000000000) (570012741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1279387001747179 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8395347829 / 1000000000000) (8395347830 / 1000000000000), orderedInterval (43803658082 / 1000000000000) (43803658083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1130377215958759 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28189348935 / 1000000000000) (28189348936 / 1000000000000), orderedInterval (38135604967 / 1000000000000) (38135604968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (327627375753141 / 800000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37150686635 / 1000000000000) (37150700273 / 1000000000000), orderedInterval (-13248477089 / 1000000000000) (-13248463452 / 1000000000000)))) (orderedInterval (-815909464 / 1000000000000) (-815908221 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_chunkChecks2_2 :
    compactCertificate350.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (906234563417327 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48358993183 / 1000000000000) (48358993184 / 1000000000000), orderedInterval (21604080440 / 1000000000000) (21604080441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (768225075681847 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-53741273965 / 1000000000000) (-53741273964 / 1000000000000), orderedInterval (-20514960984 / 1000000000000) (-20514960983 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (480719582527741 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72775622569 / 1000000000000) (72775622615 / 1000000000000), orderedInterval (-1244299680 / 1000000000000) (-1244299633 / 1000000000000)))) (orderedInterval (5116660052 / 1000000000000) (5116660102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (258532590284547 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (52450738557 / 1000000000000) (52450748974 / 1000000000000), orderedInterval (-84660058954 / 1000000000000) (-84660048537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (701966274374641 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20486553164 / 1000000000000) (20486553165 / 1000000000000), orderedInterval (56580397525 / 1000000000000) (56580397526 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (958474934715857 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51411427493 / 1000000000000) (51411427737 / 1000000000000), orderedInterval (-3803544738 / 1000000000000) (-3803544494 / 1000000000000)))) (orderedInterval (4986403008 / 1000000000000) (4986403071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (405280417472259 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (79266236373 / 1000000000000) (79266236407 / 1000000000000), orderedInterval (-589931774 / 1000000000000) (-589931740 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1647442396528739 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34985691467 / 1000000000000) (-34985691465 / 1000000000000), orderedInterval (-17894008192 / 1000000000000) (-17894008191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1100415171705901 / 4000000000000) 2 (IntervalRat.scale (443 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26016426941 / 1000000000000) (-26016422849 / 1000000000000), orderedInterval (40510287779 / 1000000000000) (40510291871 / 1000000000000)))) (orderedInterval (-17445854231 / 1000000000000) (-17445852914 / 1000000000000))) = true
  rfl'

theorem compactCertificate350_chunkChecks2 :
    compactCertificate350.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate350.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate350_chunkChecks2_0
    compactCertificate350_chunkChecks2_1 compactCertificate350_chunkChecks2_2

theorem compactCertificate350_chunkChecks3_0 :
    compactCertificate350.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (443 / 2) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37252758249 / 1000000000000) (37252795017 / 1000000000000), orderedInterval (-38637458488 / 1000000000000) (-38637421720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (652623589920143 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34112725542 / 1000000000000) (34112725543 / 1000000000000), orderedInterval (52223658022 / 1000000000000) (52223658023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (211045059982319 / 800000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31551499059 / 1000000000000) (31551499060 / 1000000000000), orderedInterval (37592723794 / 1000000000000) (37592723795 / 1000000000000)))) (orderedInterval (11472028509 / 1000000000000) (11472043171 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (190433935872301 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-110351648542 / 1000000000000) (-110351648541 / 1000000000000), orderedInterval (-33393890919 / 1000000000000) (-33393890918 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (511532338501897 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9691369901 / 1000000000000) (9691369946 / 1000000000000), orderedInterval (-69925321667 / 1000000000000) (-69925321623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1388909806243749 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27724914023 / 1000000000000) (27724925045 / 1000000000000), orderedInterval (-32670688077 / 1000000000000) (-32670677054 / 1000000000000)))) (orderedInterval (-8480414587 / 1000000000000) (-8480411496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1023064677004237 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-43510551940 / 1000000000000) (-43510519507 / 1000000000000), orderedInterval (24496110443 / 1000000000000) (24496142876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1753038761625601 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26754479444 / 1000000000000) (-26754464974 / 1000000000000), orderedInterval (27174700875 / 1000000000000) (27174715344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1291280417472259 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-935692512 / 1000000000000) (-935692511 / 1000000000000), orderedInterval (-44396571349 / 1000000000000) (-44396571348 / 1000000000000)))) (orderedInterval (9828319963 / 1000000000000) (9828323499 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate350_chunkChecks3_1 :
    compactCertificate350.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1981156228064557 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10507084996 / 1000000000000) (-10507084966 / 1000000000000), orderedInterval (34288175073 / 1000000000000) (34288175103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1143821081579653 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35612625528 / 1000000000000) (-35612625527 / 1000000000000), orderedInterval (-30889820606 / 1000000000000) (-30889820605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2029730581405577 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23361189596 / 1000000000000) (-23361183911 / 1000000000000), orderedInterval (26647154250 / 1000000000000) (26647159934 / 1000000000000)))) (orderedInterval (27441162552 / 1000000000000) (27441173201 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1896437598875213 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18017844276 / 1000000000000) (-18017844275 / 1000000000000), orderedInterval (-31889107699 / 1000000000000) (-31889107698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1353387355243229 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6916688603 / 1000000000000) (-6916688590 / 1000000000000), orderedInterval (42832190592 / 1000000000000) (42832190604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1534597015505691 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37346768415 / 1000000000000) (37346768416 / 1000000000000), orderedInterval (16217783281 / 1000000000000) (16217783282 / 1000000000000)))) (orderedInterval (-19657853285 / 1000000000000) (-19657853160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1279387001747179 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8395347829 / 1000000000000) (8395347830 / 1000000000000), orderedInterval (43803658082 / 1000000000000) (43803658083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1130377215958759 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28189348935 / 1000000000000) (28189348936 / 1000000000000), orderedInterval (38135604967 / 1000000000000) (38135604968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (327627375753141 / 800000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37150686635 / 1000000000000) (37150700273 / 1000000000000), orderedInterval (-13248477089 / 1000000000000) (-13248463452 / 1000000000000)))) (orderedInterval (5156667796 / 1000000000000) (5156670080 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate350_chunkChecks3_2 :
    compactCertificate350.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (906234563417327 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48358993183 / 1000000000000) (48358993184 / 1000000000000), orderedInterval (21604080440 / 1000000000000) (21604080441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (768225075681847 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-53741273965 / 1000000000000) (-53741273964 / 1000000000000), orderedInterval (-20514960984 / 1000000000000) (-20514960983 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (480719582527741 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72775622569 / 1000000000000) (72775622615 / 1000000000000), orderedInterval (-1244299680 / 1000000000000) (-1244299633 / 1000000000000)))) (orderedInterval (2922842820 / 1000000000000) (2922842868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (258532590284547 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (52450738557 / 1000000000000) (52450748974 / 1000000000000), orderedInterval (-84660058954 / 1000000000000) (-84660048537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (701966274374641 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20486553164 / 1000000000000) (20486553165 / 1000000000000), orderedInterval (56580397525 / 1000000000000) (56580397526 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (958474934715857 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51411427493 / 1000000000000) (51411427737 / 1000000000000), orderedInterval (-3803544738 / 1000000000000) (-3803544494 / 1000000000000)))) (orderedInterval (207991681 / 1000000000000) (207991735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (405280417472259 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (79266236373 / 1000000000000) (79266236407 / 1000000000000), orderedInterval (-589931774 / 1000000000000) (-589931740 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1647442396528739 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34985691467 / 1000000000000) (-34985691465 / 1000000000000), orderedInterval (-17894008192 / 1000000000000) (-17894008191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1100415171705901 / 4000000000000) 3 (IntervalRat.scale (443 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26016426941 / 1000000000000) (-26016422849 / 1000000000000), orderedInterval (40510287779 / 1000000000000) (40510291871 / 1000000000000)))) (orderedInterval (5276994574 / 1000000000000) (5276996248 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate350_chunkChecks3 :
    compactCertificate350.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate350.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate350_chunkChecks3_0
    compactCertificate350_chunkChecks3_1 compactCertificate350_chunkChecks3_2

theorem compactCertificate350_chunkChecks4_0 :
    compactCertificate350.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (443 / 2) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37252758249 / 1000000000000) (37252795017 / 1000000000000), orderedInterval (-38637458488 / 1000000000000) (-38637421720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (652623589920143 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (34112725542 / 1000000000000) (34112725543 / 1000000000000), orderedInterval (52223658022 / 1000000000000) (52223658023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (211045059982319 / 800000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31551499059 / 1000000000000) (31551499060 / 1000000000000), orderedInterval (37592723794 / 1000000000000) (37592723795 / 1000000000000)))) (orderedInterval (18480650392 / 1000000000000) (18480665124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (190433935872301 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-110351648542 / 1000000000000) (-110351648541 / 1000000000000), orderedInterval (-33393890919 / 1000000000000) (-33393890918 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (511532338501897 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (9691369901 / 1000000000000) (9691369946 / 1000000000000), orderedInterval (-69925321667 / 1000000000000) (-69925321623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1388909806243749 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27724914023 / 1000000000000) (27724925045 / 1000000000000), orderedInterval (-32670688077 / 1000000000000) (-32670677054 / 1000000000000)))) (orderedInterval (-11783955527 / 1000000000000) (-11783950670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1023064677004237 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-43510551940 / 1000000000000) (-43510519507 / 1000000000000), orderedInterval (24496110443 / 1000000000000) (24496142876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1753038761625601 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26754479444 / 1000000000000) (-26754464974 / 1000000000000), orderedInterval (27174700875 / 1000000000000) (27174715344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1291280417472259 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-935692512 / 1000000000000) (-935692511 / 1000000000000), orderedInterval (-44396571349 / 1000000000000) (-44396571348 / 1000000000000)))) (orderedInterval (12456473883 / 1000000000000) (12456480885 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate350_chunkChecks4_1 :
    compactCertificate350.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1981156228064557 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10507084996 / 1000000000000) (-10507084966 / 1000000000000), orderedInterval (34288175073 / 1000000000000) (34288175103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1143821081579653 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35612625528 / 1000000000000) (-35612625527 / 1000000000000), orderedInterval (-30889820606 / 1000000000000) (-30889820605 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2029730581405577 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23361189596 / 1000000000000) (-23361183911 / 1000000000000), orderedInterval (26647154250 / 1000000000000) (26647159934 / 1000000000000)))) (orderedInterval (-52372383505 / 1000000000000) (-52372359126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1896437598875213 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18017844276 / 1000000000000) (-18017844275 / 1000000000000), orderedInterval (-31889107699 / 1000000000000) (-31889107698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1353387355243229 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6916688603 / 1000000000000) (-6916688590 / 1000000000000), orderedInterval (42832190592 / 1000000000000) (42832190604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1534597015505691 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37346768415 / 1000000000000) (37346768416 / 1000000000000), orderedInterval (16217783281 / 1000000000000) (16217783282 / 1000000000000)))) (orderedInterval (1743226557 / 1000000000000) (1743226773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1279387001747179 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (8395347829 / 1000000000000) (8395347830 / 1000000000000), orderedInterval (43803658082 / 1000000000000) (43803658083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1130377215958759 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (28189348935 / 1000000000000) (28189348936 / 1000000000000), orderedInterval (38135604967 / 1000000000000) (38135604968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (327627375753141 / 800000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37150686635 / 1000000000000) (37150700273 / 1000000000000), orderedInterval (-13248477089 / 1000000000000) (-13248463452 / 1000000000000)))) (orderedInterval (7216627249 / 1000000000000) (7216631462 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate350_chunkChecks4_2 :
    compactCertificate350.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (906234563417327 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48358993183 / 1000000000000) (48358993184 / 1000000000000), orderedInterval (21604080440 / 1000000000000) (21604080441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (768225075681847 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-53741273965 / 1000000000000) (-53741273964 / 1000000000000), orderedInterval (-20514960984 / 1000000000000) (-20514960983 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (480719582527741 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72775622569 / 1000000000000) (72775622615 / 1000000000000), orderedInterval (-1244299680 / 1000000000000) (-1244299633 / 1000000000000)))) (orderedInterval (-6564861464 / 1000000000000) (-6564861416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (258532590284547 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (52450738557 / 1000000000000) (52450748974 / 1000000000000), orderedInterval (-84660058954 / 1000000000000) (-84660048537 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (701966274374641 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (20486553164 / 1000000000000) (20486553165 / 1000000000000), orderedInterval (56580397525 / 1000000000000) (56580397526 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (958474934715857 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51411427493 / 1000000000000) (51411427737 / 1000000000000), orderedInterval (-3803544738 / 1000000000000) (-3803544494 / 1000000000000)))) (orderedInterval (-5588244005 / 1000000000000) (-5588243951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (405280417472259 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (79266236373 / 1000000000000) (79266236407 / 1000000000000), orderedInterval (-589931774 / 1000000000000) (-589931740 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1647442396528739 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-34985691467 / 1000000000000) (-34985691465 / 1000000000000), orderedInterval (-17894008192 / 1000000000000) (-17894008191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1100415171705901 / 4000000000000) 4 (IntervalRat.scale (443 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26016426941 / 1000000000000) (-26016422849 / 1000000000000), orderedInterval (40510287779 / 1000000000000) (40510291871 / 1000000000000)))) (orderedInterval (45631494856 / 1000000000000) (45631497014 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate350_chunkChecks4 :
    compactCertificate350.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate350.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate350_chunkChecks4_0
    compactCertificate350_chunkChecks4_1 compactCertificate350_chunkChecks4_2

theorem compactCertificate350_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate350.chunkCheck r b = true :=
  compactCertificate350.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate350_chunkChecks0
    · exact compactCertificate350_chunkChecks1
    · exact compactCertificate350_chunkChecks2
    · exact compactCertificate350_chunkChecks3
    · exact compactCertificate350_chunkChecks4)

theorem compactCertificate350_coefficient0 :
    compactCertificate350.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate350_coefficient1 :
    compactCertificate350.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate350_coefficient2 :
    compactCertificate350.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate350_coefficient3 :
    compactCertificate350.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate350_coefficient4 :
    compactCertificate350.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate350_coefficients : ∀ r : Fin 5,
    compactCertificate350.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate350_coefficient0
  · exact compactCertificate350_coefficient1
  · exact compactCertificate350_coefficient2
  · exact compactCertificate350_coefficient3
  · exact compactCertificate350_coefficient4

theorem compactCertificate350_lower : (1 : ℚ) ≤ compactCertificate350.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate350, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate350_proves {t : ℝ} (ht : t ∈ compactCertificate350.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate350.proves compactCertificate350_states compactCertificate350_chunks
    compactCertificate350_coefficients compactCertificate350_lower ht

end Erdos232
