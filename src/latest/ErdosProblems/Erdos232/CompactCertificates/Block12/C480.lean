/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate480 : CompactCertificate where
  left := 351
  right := 352
  center := 703 / 2
  grid := fun i =>
    match i.val with
    | 0 => 112
    | 1 => 82
    | 2 => 133
    | 3 => 24
    | 4 => 65
    | 5 => 175
    | 6 => 129
    | 7 => 221
    | 8 => 163
    | 9 => 250
    | 10 => 145
    | 11 => 256
    | 12 => 240
    | 13 => 171
    | 14 => 194
    | 15 => 162
    | 16 => 143
    | 17 => 207
    | 18 => 114
    | 19 => 97
    | 20 => 61
    | 21 => 33
    | 22 => 89
    | 23 => 121
    | 24 => 51
    | 25 => 208
    | _ => 139
  point := fun i =>
    match i.val with
    | 0 => 703 / 2
    | 1 => 1035653236374403 / 4000000000000
    | 2 => 334908977804899 / 800000000000
    | 3 => 302201031418121 / 4000000000000
    | 4 => 811754478480437 / 4000000000000
    | 5 => 2204071317808929 / 4000000000000
    | 6 => 1623508956961577 / 4000000000000
    | 7 => 2781910269577421 / 4000000000000
    | 8 => 2049142513505639 / 4000000000000
    | 9 => 3143911576364297 / 4000000000000
    | 10 => 1815138194922113 / 4000000000000
    | 11 => 3220994579521717 / 4000000000000
    | 12 => 3009470952616873 / 4000000000000
    | 13 => 2147700475702009 / 4000000000000
    | 14 => 2435263435441311 / 4000000000000
    | 15 => 2030268763494959 / 4000000000000
    | 16 => 1793804024422139 / 4000000000000
    | 17 => 519914323147761 / 800000000000
    | 18 => 1438110379418467 / 4000000000000
    | 19 => 1219102095269387 / 4000000000000
    | 20 => 762857486494361 / 4000000000000
    | 21 => 410267293386087 / 4000000000000
    | 22 => 1113955509899261 / 4000000000000
    | 23 => 1521011013781597 / 4000000000000
    | 24 => 643142513505639 / 4000000000000
    | 25 => 2614338611195719 / 4000000000000
    | _ => 1746257033203721 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (17611928608 / 1000000000000) (17611928609 / 1000000000000), orderedInterval (38717336872 / 1000000000000) (38717336873 / 1000000000000))
    | 1 => (orderedInterval (43109874247 / 1000000000000) (43109908855 / 1000000000000), orderedInterval (-24585293426 / 1000000000000) (-24585258818 / 1000000000000))
    | 2 => (orderedInterval (-38989309851 / 1000000000000) (-38989309454 / 1000000000000), orderedInterval (775852925 / 1000000000000) (775853322 / 1000000000000))
    | 3 => (orderedInterval (73900267702 / 1000000000000) (73900267703 / 1000000000000), orderedInterval (53964008587 / 1000000000000) (53964008588 / 1000000000000))
    | 4 => (orderedInterval (25869736225 / 1000000000000) (25869738472 / 1000000000000), orderedInterval (-49740379555 / 1000000000000) (-49740377308 / 1000000000000))
    | 5 => (orderedInterval (-30554868307 / 1000000000000) (-30554795420 / 1000000000000), orderedInterval (14919105506 / 1000000000000) (14919178393 / 1000000000000))
    | 6 => (orderedInterval (-39006853538 / 1000000000000) (-39006853513 / 1000000000000), orderedInterval (-6805232742 / 1000000000000) (-6805232718 / 1000000000000))
    | 7 => (orderedInterval (-27866671006 / 1000000000000) (-27866584788 / 1000000000000), orderedInterval (11802244021 / 1000000000000) (11802330239 / 1000000000000))
    | 8 => (orderedInterval (-29494398836 / 1000000000000) (-29494398835 / 1000000000000), orderedInterval (-19278852083 / 1000000000000) (-19278852082 / 1000000000000))
    | 9 => (orderedInterval (27859274772 / 1000000000000) (27859275013 / 1000000000000), orderedInterval (5798827041 / 1000000000000) (5798827282 / 1000000000000))
    | 10 => (orderedInterval (30710269877 / 1000000000000) (30710341293 / 1000000000000), orderedInterval (-21476557780 / 1000000000000) (-21476486363 / 1000000000000))
    | 11 => (orderedInterval (27467778556 / 1000000000000) (27467806173 / 1000000000000), orderedInterval (-6026066298 / 1000000000000) (-6026038680 / 1000000000000))
    | 12 => (orderedInterval (-21451095540 / 1000000000000) (-21451090688 / 1000000000000), orderedInterval (19661279760 / 1000000000000) (19661284613 / 1000000000000))
    | 13 => (orderedInterval (-16446103776 / 1000000000000) (-16446103775 / 1000000000000), orderedInterval (-30237006584 / 1000000000000) (-30237006583 / 1000000000000))
    | 14 => (orderedInterval (4258537899 / 1000000000000) (4258537900 / 1000000000000), orderedInterval (32051674335 / 1000000000000) (32051674336 / 1000000000000))
    | 15 => (orderedInterval (-19576102340 / 1000000000000) (-19576101050 / 1000000000000), orderedInterval (29532562224 / 1000000000000) (29532563514 / 1000000000000))
    | 16 => (orderedInterval (437951144 / 1000000000000) (437951146 / 1000000000000), orderedInterval (-37675496399 / 1000000000000) (-37675496398 / 1000000000000))
    | 17 => (orderedInterval (-11272092130 / 1000000000000) (-11272092129 / 1000000000000), orderedInterval (-29189214411 / 1000000000000) (-29189214410 / 1000000000000))
    | 18 => (orderedInterval (34723097233 / 1000000000000) (34723208098 / 1000000000000), orderedInterval (-23818362238 / 1000000000000) (-23818251373 / 1000000000000))
    | 19 => (orderedInterval (-33603178130 / 1000000000000) (-33603178129 / 1000000000000), orderedInterval (-30922952964 / 1000000000000) (-30922952963 / 1000000000000))
    | 20 => (orderedInterval (7949954104 / 1000000000000) (7949954131 / 1000000000000), orderedInterval (-57247488035 / 1000000000000) (-57247488007 / 1000000000000))
    | 21 => (orderedInterval (24898821133 / 1000000000000) (24898821764 / 1000000000000), orderedInterval (-74867518500 / 1000000000000) (-74867517869 / 1000000000000))
    | 22 => (orderedInterval (15398960738 / 1000000000000) (15398960959 / 1000000000000), orderedInterval (-45291916861 / 1000000000000) (-45291916641 / 1000000000000))
    | 23 => (orderedInterval (-32180976430 / 1000000000000) (-32180976429 / 1000000000000), orderedInterval (-25227944498 / 1000000000000) (-25227944497 / 1000000000000))
    | 24 => (orderedInterval (-61382803722 / 1000000000000) (-61382803720 / 1000000000000), orderedInterval (-13649861333 / 1000000000000) (-13649861331 / 1000000000000))
    | 25 => (orderedInterval (24803731663 / 1000000000000) (24803731664 / 1000000000000), orderedInterval (18923520780 / 1000000000000) (18923520781 / 1000000000000))
    | _ => (orderedInterval (-23653435529 / 1000000000000) (-23653435528 / 1000000000000), orderedInterval (-29952320514 / 1000000000000) (-29952320513 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (5094515192 / 1000000000000) (5094515563 / 1000000000000)
      | 1 => orderedInterval (2314913145 / 1000000000000) (2314918451 / 1000000000000)
      | 2 => orderedInterval (146695531 / 1000000000000) (146698211 / 1000000000000)
      | 3 => orderedInterval (1229827978 / 1000000000000) (1229837378 / 1000000000000)
      | 4 => orderedInterval (-1189482998 / 1000000000000) (-1189482868 / 1000000000000)
      | 5 => orderedInterval (-539730959 / 1000000000000) (-539730910 / 1000000000000)
      | 6 => orderedInterval (-3391227267 / 1000000000000) (-3391209451 / 1000000000000)
      | 7 => orderedInterval (1657199889 / 1000000000000) (1657199948 / 1000000000000)
      | _ => orderedInterval (2048908403 / 1000000000000) (2048908501 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15231676054 / 1000000000000) (15231676348 / 1000000000000)
      | 1 => orderedInterval (-2836984243 / 1000000000000) (-2836976025 / 1000000000000)
      | 2 => orderedInterval (-1399333241 / 1000000000000) (-1399327944 / 1000000000000)
      | 3 => orderedInterval (-6320752415 / 1000000000000) (-6320736206 / 1000000000000)
      | 4 => orderedInterval (-5408333973 / 1000000000000) (-5408333717 / 1000000000000)
      | 5 => orderedInterval (1861374730 / 1000000000000) (1861374801 / 1000000000000)
      | 6 => orderedInterval (4401717627 / 1000000000000) (4401735841 / 1000000000000)
      | 7 => orderedInterval (3309088539 / 1000000000000) (3309088585 / 1000000000000)
      | _ => orderedInterval (4077974442 / 1000000000000) (4077974579 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-3996646220 / 1000000000000) (-3996645979 / 1000000000000)
      | 1 => orderedInterval (-5607601447 / 1000000000000) (-5607588596 / 1000000000000)
      | 2 => orderedInterval (-1846813497 / 1000000000000) (-1846803009 / 1000000000000)
      | 3 => orderedInterval (484306720 / 1000000000000) (484337021 / 1000000000000)
      | 4 => orderedInterval (1934583886 / 1000000000000) (1934584401 / 1000000000000)
      | 5 => orderedInterval (1493471294 / 1000000000000) (1493471399 / 1000000000000)
      | 6 => orderedInterval (4289834696 / 1000000000000) (4289853372 / 1000000000000)
      | 7 => orderedInterval (-2637277617 / 1000000000000) (-2637277575 / 1000000000000)
      | _ => orderedInterval (200647281 / 1000000000000) (200647484 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-15320062581 / 1000000000000) (-15320062374 / 1000000000000)
      | 1 => orderedInterval (4456987803 / 1000000000000) (4457007915 / 1000000000000)
      | 2 => orderedInterval (4267370890 / 1000000000000) (4267391629 / 1000000000000)
      | 3 => orderedInterval (25241743285 / 1000000000000) (25241803792 / 1000000000000)
      | 4 => orderedInterval (14509240213 / 1000000000000) (14509241265 / 1000000000000)
      | 5 => orderedInterval (-784812623 / 1000000000000) (-784812466 / 1000000000000)
      | 6 => orderedInterval (-4930732201 / 1000000000000) (-4930713104 / 1000000000000)
      | 7 => orderedInterval (-2985621348 / 1000000000000) (-2985621306 / 1000000000000)
      | _ => orderedInterval (-856658142 / 1000000000000) (-856657829 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (2582624115 / 1000000000000) (2582624302 / 1000000000000)
      | 1 => orderedInterval (13195210129 / 1000000000000) (13195241695 / 1000000000000)
      | 2 => orderedInterval (9932643370 / 1000000000000) (9932684449 / 1000000000000)
      | 3 => orderedInterval (-10030367483 / 1000000000000) (-10030240234 / 1000000000000)
      | 4 => orderedInterval (-614963133 / 1000000000000) (-614960958 / 1000000000000)
      | 5 => orderedInterval (-4417486113 / 1000000000000) (-4417485870 / 1000000000000)
      | 6 => orderedInterval (-4951269460 / 1000000000000) (-4951249875 / 1000000000000)
      | 7 => orderedInterval (3253796710 / 1000000000000) (3253796754 / 1000000000000)
      | _ => orderedInterval (-13586474944 / 1000000000000) (-13586474442 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (7371618914 / 1000000000000) (7371654823 / 1000000000000)
    | 1 => orderedInterval (12916427520 / 1000000000000) (12916476262 / 1000000000000)
    | 2 => orderedInterval (-5685494904 / 1000000000000) (-5685421482 / 1000000000000)
    | 3 => orderedInterval (23597455296 / 1000000000000) (23597577522 / 1000000000000)
    | _ => orderedInterval (-4636286809 / 1000000000000) (-4636064179 / 1000000000000)

theorem compactCertificate480_stateChecks0 :
    compactCertificate480.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (703 / 2)) (orderedInterval (17611928608 / 1000000000000) (17611928609 / 1000000000000), orderedInterval (38717336872 / 1000000000000) (38717336873 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1035653236374403 / 4000000000000)) (orderedInterval (43109874247 / 1000000000000) (43109908855 / 1000000000000), orderedInterval (-24585293426 / 1000000000000) (-24585258818 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (334908977804899 / 800000000000)) (orderedInterval (-38989309851 / 1000000000000) (-38989309454 / 1000000000000), orderedInterval (775852925 / 1000000000000) (775853322 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_stateChecks1 :
    compactCertificate480.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (302201031418121 / 4000000000000)) (orderedInterval (73900267702 / 1000000000000) (73900267703 / 1000000000000), orderedInterval (53964008587 / 1000000000000) (53964008588 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (811754478480437 / 4000000000000)) (orderedInterval (25869736225 / 1000000000000) (25869738472 / 1000000000000), orderedInterval (-49740379555 / 1000000000000) (-49740377308 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2204071317808929 / 4000000000000)) (orderedInterval (-30554868307 / 1000000000000) (-30554795420 / 1000000000000), orderedInterval (14919105506 / 1000000000000) (14919178393 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_stateChecks2 :
    compactCertificate480.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1623508956961577 / 4000000000000)) (orderedInterval (-39006853538 / 1000000000000) (-39006853513 / 1000000000000), orderedInterval (-6805232742 / 1000000000000) (-6805232718 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2781910269577421 / 4000000000000)) (orderedInterval (-27866671006 / 1000000000000) (-27866584788 / 1000000000000), orderedInterval (11802244021 / 1000000000000) (11802330239 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2049142513505639 / 4000000000000)) (orderedInterval (-29494398836 / 1000000000000) (-29494398835 / 1000000000000), orderedInterval (-19278852083 / 1000000000000) (-19278852082 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_stateChecks3 :
    compactCertificate480.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 250 12 (3143911576364297 / 4000000000000)) (orderedInterval (27859274772 / 1000000000000) (27859275013 / 1000000000000), orderedInterval (5798827041 / 1000000000000) (5798827282 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1815138194922113 / 4000000000000)) (orderedInterval (30710269877 / 1000000000000) (30710341293 / 1000000000000), orderedInterval (-21476557780 / 1000000000000) (-21476486363 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 256 12 (3220994579521717 / 4000000000000)) (orderedInterval (27467778556 / 1000000000000) (27467806173 / 1000000000000), orderedInterval (-6026066298 / 1000000000000) (-6026038680 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_stateChecks4 :
    compactCertificate480.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3009470952616873 / 4000000000000)) (orderedInterval (-21451095540 / 1000000000000) (-21451090688 / 1000000000000), orderedInterval (19661279760 / 1000000000000) (19661284613 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2147700475702009 / 4000000000000)) (orderedInterval (-16446103776 / 1000000000000) (-16446103775 / 1000000000000), orderedInterval (-30237006584 / 1000000000000) (-30237006583 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2435263435441311 / 4000000000000)) (orderedInterval (4258537899 / 1000000000000) (4258537900 / 1000000000000), orderedInterval (32051674335 / 1000000000000) (32051674336 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_stateChecks5 :
    compactCertificate480.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2030268763494959 / 4000000000000)) (orderedInterval (-19576102340 / 1000000000000) (-19576101050 / 1000000000000), orderedInterval (29532562224 / 1000000000000) (29532563514 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1793804024422139 / 4000000000000)) (orderedInterval (437951144 / 1000000000000) (437951146 / 1000000000000), orderedInterval (-37675496399 / 1000000000000) (-37675496398 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (519914323147761 / 800000000000)) (orderedInterval (-11272092130 / 1000000000000) (-11272092129 / 1000000000000), orderedInterval (-29189214411 / 1000000000000) (-29189214410 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_stateChecks6 :
    compactCertificate480.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1438110379418467 / 4000000000000)) (orderedInterval (34723097233 / 1000000000000) (34723208098 / 1000000000000), orderedInterval (-23818362238 / 1000000000000) (-23818251373 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1219102095269387 / 4000000000000)) (orderedInterval (-33603178130 / 1000000000000) (-33603178129 / 1000000000000), orderedInterval (-30922952964 / 1000000000000) (-30922952963 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (762857486494361 / 4000000000000)) (orderedInterval (7949954104 / 1000000000000) (7949954131 / 1000000000000), orderedInterval (-57247488035 / 1000000000000) (-57247488007 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_stateChecks7 :
    compactCertificate480.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (410267293386087 / 4000000000000)) (orderedInterval (24898821133 / 1000000000000) (24898821764 / 1000000000000), orderedInterval (-74867518500 / 1000000000000) (-74867517869 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1113955509899261 / 4000000000000)) (orderedInterval (15398960738 / 1000000000000) (15398960959 / 1000000000000), orderedInterval (-45291916861 / 1000000000000) (-45291916641 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1521011013781597 / 4000000000000)) (orderedInterval (-32180976430 / 1000000000000) (-32180976429 / 1000000000000), orderedInterval (-25227944498 / 1000000000000) (-25227944497 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_stateChecks8 :
    compactCertificate480.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (643142513505639 / 4000000000000)) (orderedInterval (-61382803722 / 1000000000000) (-61382803720 / 1000000000000), orderedInterval (-13649861333 / 1000000000000) (-13649861331 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2614338611195719 / 4000000000000)) (orderedInterval (24803731663 / 1000000000000) (24803731664 / 1000000000000), orderedInterval (18923520780 / 1000000000000) (18923520781 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1746257033203721 / 4000000000000)) (orderedInterval (-23653435529 / 1000000000000) (-23653435528 / 1000000000000), orderedInterval (-29952320514 / 1000000000000) (-29952320513 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_states : ∀ j,
    BesselStateValid (compactCertificate480.point j) (compactCertificate480.state j) :=
  compactCertificate480.statesValid_of_checks3 compactCertificate480_stateChecks0
    compactCertificate480_stateChecks1 compactCertificate480_stateChecks2
    compactCertificate480_stateChecks3 compactCertificate480_stateChecks4
    compactCertificate480_stateChecks5 compactCertificate480_stateChecks6
    compactCertificate480_stateChecks7 compactCertificate480_stateChecks8

theorem compactCertificate480_chunkChecks0_0 :
    compactCertificate480.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (703 / 2) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17611928608 / 1000000000000) (17611928609 / 1000000000000), orderedInterval (38717336872 / 1000000000000) (38717336873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1035653236374403 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43109874247 / 1000000000000) (43109908855 / 1000000000000), orderedInterval (-24585293426 / 1000000000000) (-24585258818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (334908977804899 / 800000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-38989309851 / 1000000000000) (-38989309454 / 1000000000000), orderedInterval (775852925 / 1000000000000) (775853322 / 1000000000000)))) (orderedInterval (5094515192 / 1000000000000) (5094515563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (302201031418121 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73900267702 / 1000000000000) (73900267703 / 1000000000000), orderedInterval (53964008587 / 1000000000000) (53964008588 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (811754478480437 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25869736225 / 1000000000000) (25869738472 / 1000000000000), orderedInterval (-49740379555 / 1000000000000) (-49740377308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2204071317808929 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30554868307 / 1000000000000) (-30554795420 / 1000000000000), orderedInterval (14919105506 / 1000000000000) (14919178393 / 1000000000000)))) (orderedInterval (2314913145 / 1000000000000) (2314918451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1623508956961577 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39006853538 / 1000000000000) (-39006853513 / 1000000000000), orderedInterval (-6805232742 / 1000000000000) (-6805232718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2781910269577421 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27866671006 / 1000000000000) (-27866584788 / 1000000000000), orderedInterval (11802244021 / 1000000000000) (11802330239 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2049142513505639 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29494398836 / 1000000000000) (-29494398835 / 1000000000000), orderedInterval (-19278852083 / 1000000000000) (-19278852082 / 1000000000000)))) (orderedInterval (146695531 / 1000000000000) (146698211 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_chunkChecks0_1 :
    compactCertificate480.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3143911576364297 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27859274772 / 1000000000000) (27859275013 / 1000000000000), orderedInterval (5798827041 / 1000000000000) (5798827282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1815138194922113 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30710269877 / 1000000000000) (30710341293 / 1000000000000), orderedInterval (-21476557780 / 1000000000000) (-21476486363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3220994579521717 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27467778556 / 1000000000000) (27467806173 / 1000000000000), orderedInterval (-6026066298 / 1000000000000) (-6026038680 / 1000000000000)))) (orderedInterval (1229827978 / 1000000000000) (1229837378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3009470952616873 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21451095540 / 1000000000000) (-21451090688 / 1000000000000), orderedInterval (19661279760 / 1000000000000) (19661284613 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2147700475702009 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16446103776 / 1000000000000) (-16446103775 / 1000000000000), orderedInterval (-30237006584 / 1000000000000) (-30237006583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2435263435441311 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4258537899 / 1000000000000) (4258537900 / 1000000000000), orderedInterval (32051674335 / 1000000000000) (32051674336 / 1000000000000)))) (orderedInterval (-1189482998 / 1000000000000) (-1189482868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2030268763494959 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19576102340 / 1000000000000) (-19576101050 / 1000000000000), orderedInterval (29532562224 / 1000000000000) (29532563514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1793804024422139 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (437951144 / 1000000000000) (437951146 / 1000000000000), orderedInterval (-37675496399 / 1000000000000) (-37675496398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (519914323147761 / 800000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11272092130 / 1000000000000) (-11272092129 / 1000000000000), orderedInterval (-29189214411 / 1000000000000) (-29189214410 / 1000000000000)))) (orderedInterval (-539730959 / 1000000000000) (-539730910 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_chunkChecks0_2 :
    compactCertificate480.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1438110379418467 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34723097233 / 1000000000000) (34723208098 / 1000000000000), orderedInterval (-23818362238 / 1000000000000) (-23818251373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1219102095269387 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-33603178130 / 1000000000000) (-33603178129 / 1000000000000), orderedInterval (-30922952964 / 1000000000000) (-30922952963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (762857486494361 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (7949954104 / 1000000000000) (7949954131 / 1000000000000), orderedInterval (-57247488035 / 1000000000000) (-57247488007 / 1000000000000)))) (orderedInterval (-3391227267 / 1000000000000) (-3391209451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (410267293386087 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24898821133 / 1000000000000) (24898821764 / 1000000000000), orderedInterval (-74867518500 / 1000000000000) (-74867517869 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1113955509899261 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (15398960738 / 1000000000000) (15398960959 / 1000000000000), orderedInterval (-45291916861 / 1000000000000) (-45291916641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1521011013781597 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32180976430 / 1000000000000) (-32180976429 / 1000000000000), orderedInterval (-25227944498 / 1000000000000) (-25227944497 / 1000000000000)))) (orderedInterval (1657199889 / 1000000000000) (1657199948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (643142513505639 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61382803722 / 1000000000000) (-61382803720 / 1000000000000), orderedInterval (-13649861333 / 1000000000000) (-13649861331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2614338611195719 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24803731663 / 1000000000000) (24803731664 / 1000000000000), orderedInterval (18923520780 / 1000000000000) (18923520781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1746257033203721 / 4000000000000) 0 (IntervalRat.scale (703 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23653435529 / 1000000000000) (-23653435528 / 1000000000000), orderedInterval (-29952320514 / 1000000000000) (-29952320513 / 1000000000000)))) (orderedInterval (2048908403 / 1000000000000) (2048908501 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_chunkChecks0 :
    compactCertificate480.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate480.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate480_chunkChecks0_0
    compactCertificate480_chunkChecks0_1 compactCertificate480_chunkChecks0_2

theorem compactCertificate480_chunkChecks1_0 :
    compactCertificate480.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (703 / 2) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17611928608 / 1000000000000) (17611928609 / 1000000000000), orderedInterval (38717336872 / 1000000000000) (38717336873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1035653236374403 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43109874247 / 1000000000000) (43109908855 / 1000000000000), orderedInterval (-24585293426 / 1000000000000) (-24585258818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (334908977804899 / 800000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-38989309851 / 1000000000000) (-38989309454 / 1000000000000), orderedInterval (775852925 / 1000000000000) (775853322 / 1000000000000)))) (orderedInterval (15231676054 / 1000000000000) (15231676348 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (302201031418121 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73900267702 / 1000000000000) (73900267703 / 1000000000000), orderedInterval (53964008587 / 1000000000000) (53964008588 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (811754478480437 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25869736225 / 1000000000000) (25869738472 / 1000000000000), orderedInterval (-49740379555 / 1000000000000) (-49740377308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2204071317808929 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30554868307 / 1000000000000) (-30554795420 / 1000000000000), orderedInterval (14919105506 / 1000000000000) (14919178393 / 1000000000000)))) (orderedInterval (-2836984243 / 1000000000000) (-2836976025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1623508956961577 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39006853538 / 1000000000000) (-39006853513 / 1000000000000), orderedInterval (-6805232742 / 1000000000000) (-6805232718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2781910269577421 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27866671006 / 1000000000000) (-27866584788 / 1000000000000), orderedInterval (11802244021 / 1000000000000) (11802330239 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2049142513505639 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29494398836 / 1000000000000) (-29494398835 / 1000000000000), orderedInterval (-19278852083 / 1000000000000) (-19278852082 / 1000000000000)))) (orderedInterval (-1399333241 / 1000000000000) (-1399327944 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_chunkChecks1_1 :
    compactCertificate480.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3143911576364297 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27859274772 / 1000000000000) (27859275013 / 1000000000000), orderedInterval (5798827041 / 1000000000000) (5798827282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1815138194922113 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30710269877 / 1000000000000) (30710341293 / 1000000000000), orderedInterval (-21476557780 / 1000000000000) (-21476486363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3220994579521717 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27467778556 / 1000000000000) (27467806173 / 1000000000000), orderedInterval (-6026066298 / 1000000000000) (-6026038680 / 1000000000000)))) (orderedInterval (-6320752415 / 1000000000000) (-6320736206 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3009470952616873 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21451095540 / 1000000000000) (-21451090688 / 1000000000000), orderedInterval (19661279760 / 1000000000000) (19661284613 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2147700475702009 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16446103776 / 1000000000000) (-16446103775 / 1000000000000), orderedInterval (-30237006584 / 1000000000000) (-30237006583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2435263435441311 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4258537899 / 1000000000000) (4258537900 / 1000000000000), orderedInterval (32051674335 / 1000000000000) (32051674336 / 1000000000000)))) (orderedInterval (-5408333973 / 1000000000000) (-5408333717 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2030268763494959 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19576102340 / 1000000000000) (-19576101050 / 1000000000000), orderedInterval (29532562224 / 1000000000000) (29532563514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1793804024422139 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (437951144 / 1000000000000) (437951146 / 1000000000000), orderedInterval (-37675496399 / 1000000000000) (-37675496398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (519914323147761 / 800000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11272092130 / 1000000000000) (-11272092129 / 1000000000000), orderedInterval (-29189214411 / 1000000000000) (-29189214410 / 1000000000000)))) (orderedInterval (1861374730 / 1000000000000) (1861374801 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_chunkChecks1_2 :
    compactCertificate480.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1438110379418467 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34723097233 / 1000000000000) (34723208098 / 1000000000000), orderedInterval (-23818362238 / 1000000000000) (-23818251373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1219102095269387 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-33603178130 / 1000000000000) (-33603178129 / 1000000000000), orderedInterval (-30922952964 / 1000000000000) (-30922952963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (762857486494361 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (7949954104 / 1000000000000) (7949954131 / 1000000000000), orderedInterval (-57247488035 / 1000000000000) (-57247488007 / 1000000000000)))) (orderedInterval (4401717627 / 1000000000000) (4401735841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (410267293386087 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24898821133 / 1000000000000) (24898821764 / 1000000000000), orderedInterval (-74867518500 / 1000000000000) (-74867517869 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1113955509899261 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (15398960738 / 1000000000000) (15398960959 / 1000000000000), orderedInterval (-45291916861 / 1000000000000) (-45291916641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1521011013781597 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32180976430 / 1000000000000) (-32180976429 / 1000000000000), orderedInterval (-25227944498 / 1000000000000) (-25227944497 / 1000000000000)))) (orderedInterval (3309088539 / 1000000000000) (3309088585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (643142513505639 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61382803722 / 1000000000000) (-61382803720 / 1000000000000), orderedInterval (-13649861333 / 1000000000000) (-13649861331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2614338611195719 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24803731663 / 1000000000000) (24803731664 / 1000000000000), orderedInterval (18923520780 / 1000000000000) (18923520781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1746257033203721 / 4000000000000) 1 (IntervalRat.scale (703 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23653435529 / 1000000000000) (-23653435528 / 1000000000000), orderedInterval (-29952320514 / 1000000000000) (-29952320513 / 1000000000000)))) (orderedInterval (4077974442 / 1000000000000) (4077974579 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_chunkChecks1 :
    compactCertificate480.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate480.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate480_chunkChecks1_0
    compactCertificate480_chunkChecks1_1 compactCertificate480_chunkChecks1_2

theorem compactCertificate480_chunkChecks2_0 :
    compactCertificate480.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (703 / 2) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17611928608 / 1000000000000) (17611928609 / 1000000000000), orderedInterval (38717336872 / 1000000000000) (38717336873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1035653236374403 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43109874247 / 1000000000000) (43109908855 / 1000000000000), orderedInterval (-24585293426 / 1000000000000) (-24585258818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (334908977804899 / 800000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-38989309851 / 1000000000000) (-38989309454 / 1000000000000), orderedInterval (775852925 / 1000000000000) (775853322 / 1000000000000)))) (orderedInterval (-3996646220 / 1000000000000) (-3996645979 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (302201031418121 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73900267702 / 1000000000000) (73900267703 / 1000000000000), orderedInterval (53964008587 / 1000000000000) (53964008588 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (811754478480437 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25869736225 / 1000000000000) (25869738472 / 1000000000000), orderedInterval (-49740379555 / 1000000000000) (-49740377308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2204071317808929 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30554868307 / 1000000000000) (-30554795420 / 1000000000000), orderedInterval (14919105506 / 1000000000000) (14919178393 / 1000000000000)))) (orderedInterval (-5607601447 / 1000000000000) (-5607588596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1623508956961577 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39006853538 / 1000000000000) (-39006853513 / 1000000000000), orderedInterval (-6805232742 / 1000000000000) (-6805232718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2781910269577421 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27866671006 / 1000000000000) (-27866584788 / 1000000000000), orderedInterval (11802244021 / 1000000000000) (11802330239 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2049142513505639 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29494398836 / 1000000000000) (-29494398835 / 1000000000000), orderedInterval (-19278852083 / 1000000000000) (-19278852082 / 1000000000000)))) (orderedInterval (-1846813497 / 1000000000000) (-1846803009 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_chunkChecks2_1 :
    compactCertificate480.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3143911576364297 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27859274772 / 1000000000000) (27859275013 / 1000000000000), orderedInterval (5798827041 / 1000000000000) (5798827282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1815138194922113 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30710269877 / 1000000000000) (30710341293 / 1000000000000), orderedInterval (-21476557780 / 1000000000000) (-21476486363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3220994579521717 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27467778556 / 1000000000000) (27467806173 / 1000000000000), orderedInterval (-6026066298 / 1000000000000) (-6026038680 / 1000000000000)))) (orderedInterval (484306720 / 1000000000000) (484337021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3009470952616873 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21451095540 / 1000000000000) (-21451090688 / 1000000000000), orderedInterval (19661279760 / 1000000000000) (19661284613 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2147700475702009 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16446103776 / 1000000000000) (-16446103775 / 1000000000000), orderedInterval (-30237006584 / 1000000000000) (-30237006583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2435263435441311 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4258537899 / 1000000000000) (4258537900 / 1000000000000), orderedInterval (32051674335 / 1000000000000) (32051674336 / 1000000000000)))) (orderedInterval (1934583886 / 1000000000000) (1934584401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2030268763494959 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19576102340 / 1000000000000) (-19576101050 / 1000000000000), orderedInterval (29532562224 / 1000000000000) (29532563514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1793804024422139 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (437951144 / 1000000000000) (437951146 / 1000000000000), orderedInterval (-37675496399 / 1000000000000) (-37675496398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (519914323147761 / 800000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11272092130 / 1000000000000) (-11272092129 / 1000000000000), orderedInterval (-29189214411 / 1000000000000) (-29189214410 / 1000000000000)))) (orderedInterval (1493471294 / 1000000000000) (1493471399 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_chunkChecks2_2 :
    compactCertificate480.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1438110379418467 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34723097233 / 1000000000000) (34723208098 / 1000000000000), orderedInterval (-23818362238 / 1000000000000) (-23818251373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1219102095269387 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-33603178130 / 1000000000000) (-33603178129 / 1000000000000), orderedInterval (-30922952964 / 1000000000000) (-30922952963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (762857486494361 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (7949954104 / 1000000000000) (7949954131 / 1000000000000), orderedInterval (-57247488035 / 1000000000000) (-57247488007 / 1000000000000)))) (orderedInterval (4289834696 / 1000000000000) (4289853372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (410267293386087 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24898821133 / 1000000000000) (24898821764 / 1000000000000), orderedInterval (-74867518500 / 1000000000000) (-74867517869 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1113955509899261 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (15398960738 / 1000000000000) (15398960959 / 1000000000000), orderedInterval (-45291916861 / 1000000000000) (-45291916641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1521011013781597 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32180976430 / 1000000000000) (-32180976429 / 1000000000000), orderedInterval (-25227944498 / 1000000000000) (-25227944497 / 1000000000000)))) (orderedInterval (-2637277617 / 1000000000000) (-2637277575 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (643142513505639 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61382803722 / 1000000000000) (-61382803720 / 1000000000000), orderedInterval (-13649861333 / 1000000000000) (-13649861331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2614338611195719 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24803731663 / 1000000000000) (24803731664 / 1000000000000), orderedInterval (18923520780 / 1000000000000) (18923520781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1746257033203721 / 4000000000000) 2 (IntervalRat.scale (703 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23653435529 / 1000000000000) (-23653435528 / 1000000000000), orderedInterval (-29952320514 / 1000000000000) (-29952320513 / 1000000000000)))) (orderedInterval (200647281 / 1000000000000) (200647484 / 1000000000000))) = true
  rfl'

theorem compactCertificate480_chunkChecks2 :
    compactCertificate480.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate480.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate480_chunkChecks2_0
    compactCertificate480_chunkChecks2_1 compactCertificate480_chunkChecks2_2

theorem compactCertificate480_chunkChecks3_0 :
    compactCertificate480.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (703 / 2) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17611928608 / 1000000000000) (17611928609 / 1000000000000), orderedInterval (38717336872 / 1000000000000) (38717336873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1035653236374403 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43109874247 / 1000000000000) (43109908855 / 1000000000000), orderedInterval (-24585293426 / 1000000000000) (-24585258818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (334908977804899 / 800000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-38989309851 / 1000000000000) (-38989309454 / 1000000000000), orderedInterval (775852925 / 1000000000000) (775853322 / 1000000000000)))) (orderedInterval (-15320062581 / 1000000000000) (-15320062374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (302201031418121 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73900267702 / 1000000000000) (73900267703 / 1000000000000), orderedInterval (53964008587 / 1000000000000) (53964008588 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (811754478480437 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25869736225 / 1000000000000) (25869738472 / 1000000000000), orderedInterval (-49740379555 / 1000000000000) (-49740377308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2204071317808929 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30554868307 / 1000000000000) (-30554795420 / 1000000000000), orderedInterval (14919105506 / 1000000000000) (14919178393 / 1000000000000)))) (orderedInterval (4456987803 / 1000000000000) (4457007915 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1623508956961577 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39006853538 / 1000000000000) (-39006853513 / 1000000000000), orderedInterval (-6805232742 / 1000000000000) (-6805232718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2781910269577421 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27866671006 / 1000000000000) (-27866584788 / 1000000000000), orderedInterval (11802244021 / 1000000000000) (11802330239 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2049142513505639 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29494398836 / 1000000000000) (-29494398835 / 1000000000000), orderedInterval (-19278852083 / 1000000000000) (-19278852082 / 1000000000000)))) (orderedInterval (4267370890 / 1000000000000) (4267391629 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate480_chunkChecks3_1 :
    compactCertificate480.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3143911576364297 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27859274772 / 1000000000000) (27859275013 / 1000000000000), orderedInterval (5798827041 / 1000000000000) (5798827282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1815138194922113 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30710269877 / 1000000000000) (30710341293 / 1000000000000), orderedInterval (-21476557780 / 1000000000000) (-21476486363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3220994579521717 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27467778556 / 1000000000000) (27467806173 / 1000000000000), orderedInterval (-6026066298 / 1000000000000) (-6026038680 / 1000000000000)))) (orderedInterval (25241743285 / 1000000000000) (25241803792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3009470952616873 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21451095540 / 1000000000000) (-21451090688 / 1000000000000), orderedInterval (19661279760 / 1000000000000) (19661284613 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2147700475702009 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16446103776 / 1000000000000) (-16446103775 / 1000000000000), orderedInterval (-30237006584 / 1000000000000) (-30237006583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2435263435441311 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4258537899 / 1000000000000) (4258537900 / 1000000000000), orderedInterval (32051674335 / 1000000000000) (32051674336 / 1000000000000)))) (orderedInterval (14509240213 / 1000000000000) (14509241265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2030268763494959 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19576102340 / 1000000000000) (-19576101050 / 1000000000000), orderedInterval (29532562224 / 1000000000000) (29532563514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1793804024422139 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (437951144 / 1000000000000) (437951146 / 1000000000000), orderedInterval (-37675496399 / 1000000000000) (-37675496398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (519914323147761 / 800000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11272092130 / 1000000000000) (-11272092129 / 1000000000000), orderedInterval (-29189214411 / 1000000000000) (-29189214410 / 1000000000000)))) (orderedInterval (-784812623 / 1000000000000) (-784812466 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate480_chunkChecks3_2 :
    compactCertificate480.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1438110379418467 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34723097233 / 1000000000000) (34723208098 / 1000000000000), orderedInterval (-23818362238 / 1000000000000) (-23818251373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1219102095269387 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-33603178130 / 1000000000000) (-33603178129 / 1000000000000), orderedInterval (-30922952964 / 1000000000000) (-30922952963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (762857486494361 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (7949954104 / 1000000000000) (7949954131 / 1000000000000), orderedInterval (-57247488035 / 1000000000000) (-57247488007 / 1000000000000)))) (orderedInterval (-4930732201 / 1000000000000) (-4930713104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (410267293386087 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24898821133 / 1000000000000) (24898821764 / 1000000000000), orderedInterval (-74867518500 / 1000000000000) (-74867517869 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1113955509899261 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (15398960738 / 1000000000000) (15398960959 / 1000000000000), orderedInterval (-45291916861 / 1000000000000) (-45291916641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1521011013781597 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32180976430 / 1000000000000) (-32180976429 / 1000000000000), orderedInterval (-25227944498 / 1000000000000) (-25227944497 / 1000000000000)))) (orderedInterval (-2985621348 / 1000000000000) (-2985621306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (643142513505639 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61382803722 / 1000000000000) (-61382803720 / 1000000000000), orderedInterval (-13649861333 / 1000000000000) (-13649861331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2614338611195719 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24803731663 / 1000000000000) (24803731664 / 1000000000000), orderedInterval (18923520780 / 1000000000000) (18923520781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1746257033203721 / 4000000000000) 3 (IntervalRat.scale (703 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23653435529 / 1000000000000) (-23653435528 / 1000000000000), orderedInterval (-29952320514 / 1000000000000) (-29952320513 / 1000000000000)))) (orderedInterval (-856658142 / 1000000000000) (-856657829 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate480_chunkChecks3 :
    compactCertificate480.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate480.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate480_chunkChecks3_0
    compactCertificate480_chunkChecks3_1 compactCertificate480_chunkChecks3_2

theorem compactCertificate480_chunkChecks4_0 :
    compactCertificate480.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (703 / 2) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (17611928608 / 1000000000000) (17611928609 / 1000000000000), orderedInterval (38717336872 / 1000000000000) (38717336873 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1035653236374403 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43109874247 / 1000000000000) (43109908855 / 1000000000000), orderedInterval (-24585293426 / 1000000000000) (-24585258818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (334908977804899 / 800000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-38989309851 / 1000000000000) (-38989309454 / 1000000000000), orderedInterval (775852925 / 1000000000000) (775853322 / 1000000000000)))) (orderedInterval (2582624115 / 1000000000000) (2582624302 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (302201031418121 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73900267702 / 1000000000000) (73900267703 / 1000000000000), orderedInterval (53964008587 / 1000000000000) (53964008588 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (811754478480437 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25869736225 / 1000000000000) (25869738472 / 1000000000000), orderedInterval (-49740379555 / 1000000000000) (-49740377308 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2204071317808929 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30554868307 / 1000000000000) (-30554795420 / 1000000000000), orderedInterval (14919105506 / 1000000000000) (14919178393 / 1000000000000)))) (orderedInterval (13195210129 / 1000000000000) (13195241695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1623508956961577 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39006853538 / 1000000000000) (-39006853513 / 1000000000000), orderedInterval (-6805232742 / 1000000000000) (-6805232718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2781910269577421 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27866671006 / 1000000000000) (-27866584788 / 1000000000000), orderedInterval (11802244021 / 1000000000000) (11802330239 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2049142513505639 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29494398836 / 1000000000000) (-29494398835 / 1000000000000), orderedInterval (-19278852083 / 1000000000000) (-19278852082 / 1000000000000)))) (orderedInterval (9932643370 / 1000000000000) (9932684449 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate480_chunkChecks4_1 :
    compactCertificate480.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3143911576364297 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27859274772 / 1000000000000) (27859275013 / 1000000000000), orderedInterval (5798827041 / 1000000000000) (5798827282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1815138194922113 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30710269877 / 1000000000000) (30710341293 / 1000000000000), orderedInterval (-21476557780 / 1000000000000) (-21476486363 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3220994579521717 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27467778556 / 1000000000000) (27467806173 / 1000000000000), orderedInterval (-6026066298 / 1000000000000) (-6026038680 / 1000000000000)))) (orderedInterval (-10030367483 / 1000000000000) (-10030240234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3009470952616873 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21451095540 / 1000000000000) (-21451090688 / 1000000000000), orderedInterval (19661279760 / 1000000000000) (19661284613 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2147700475702009 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16446103776 / 1000000000000) (-16446103775 / 1000000000000), orderedInterval (-30237006584 / 1000000000000) (-30237006583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2435263435441311 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4258537899 / 1000000000000) (4258537900 / 1000000000000), orderedInterval (32051674335 / 1000000000000) (32051674336 / 1000000000000)))) (orderedInterval (-614963133 / 1000000000000) (-614960958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2030268763494959 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-19576102340 / 1000000000000) (-19576101050 / 1000000000000), orderedInterval (29532562224 / 1000000000000) (29532563514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1793804024422139 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (437951144 / 1000000000000) (437951146 / 1000000000000), orderedInterval (-37675496399 / 1000000000000) (-37675496398 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (519914323147761 / 800000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11272092130 / 1000000000000) (-11272092129 / 1000000000000), orderedInterval (-29189214411 / 1000000000000) (-29189214410 / 1000000000000)))) (orderedInterval (-4417486113 / 1000000000000) (-4417485870 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate480_chunkChecks4_2 :
    compactCertificate480.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1438110379418467 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (34723097233 / 1000000000000) (34723208098 / 1000000000000), orderedInterval (-23818362238 / 1000000000000) (-23818251373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1219102095269387 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-33603178130 / 1000000000000) (-33603178129 / 1000000000000), orderedInterval (-30922952964 / 1000000000000) (-30922952963 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (762857486494361 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (7949954104 / 1000000000000) (7949954131 / 1000000000000), orderedInterval (-57247488035 / 1000000000000) (-57247488007 / 1000000000000)))) (orderedInterval (-4951269460 / 1000000000000) (-4951249875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (410267293386087 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24898821133 / 1000000000000) (24898821764 / 1000000000000), orderedInterval (-74867518500 / 1000000000000) (-74867517869 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1113955509899261 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (15398960738 / 1000000000000) (15398960959 / 1000000000000), orderedInterval (-45291916861 / 1000000000000) (-45291916641 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1521011013781597 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32180976430 / 1000000000000) (-32180976429 / 1000000000000), orderedInterval (-25227944498 / 1000000000000) (-25227944497 / 1000000000000)))) (orderedInterval (3253796710 / 1000000000000) (3253796754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (643142513505639 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61382803722 / 1000000000000) (-61382803720 / 1000000000000), orderedInterval (-13649861333 / 1000000000000) (-13649861331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2614338611195719 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24803731663 / 1000000000000) (24803731664 / 1000000000000), orderedInterval (18923520780 / 1000000000000) (18923520781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1746257033203721 / 4000000000000) 4 (IntervalRat.scale (703 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23653435529 / 1000000000000) (-23653435528 / 1000000000000), orderedInterval (-29952320514 / 1000000000000) (-29952320513 / 1000000000000)))) (orderedInterval (-13586474944 / 1000000000000) (-13586474442 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate480_chunkChecks4 :
    compactCertificate480.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate480.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate480_chunkChecks4_0
    compactCertificate480_chunkChecks4_1 compactCertificate480_chunkChecks4_2

theorem compactCertificate480_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate480.chunkCheck r b = true :=
  compactCertificate480.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate480_chunkChecks0
    · exact compactCertificate480_chunkChecks1
    · exact compactCertificate480_chunkChecks2
    · exact compactCertificate480_chunkChecks3
    · exact compactCertificate480_chunkChecks4)

theorem compactCertificate480_coefficient0 :
    compactCertificate480.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate480_coefficient1 :
    compactCertificate480.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate480_coefficient2 :
    compactCertificate480.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate480_coefficient3 :
    compactCertificate480.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate480_coefficient4 :
    compactCertificate480.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate480_coefficients : ∀ r : Fin 5,
    compactCertificate480.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate480_coefficient0
  · exact compactCertificate480_coefficient1
  · exact compactCertificate480_coefficient2
  · exact compactCertificate480_coefficient3
  · exact compactCertificate480_coefficient4

theorem compactCertificate480_lower : (1 : ℚ) ≤ compactCertificate480.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate480, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate480_proves {t : ℝ} (ht : t ∈ compactCertificate480.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate480.proves compactCertificate480_states compactCertificate480_chunks
    compactCertificate480_coefficients compactCertificate480_lower ht

end Erdos232
