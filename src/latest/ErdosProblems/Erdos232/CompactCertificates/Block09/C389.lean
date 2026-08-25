/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate389 : CompactCertificate where
  left := 260
  right := 261
  center := 521 / 2
  grid := fun i =>
    match i.val with
    | 0 => 83
    | 1 => 61
    | 2 => 99
    | 3 => 18
    | 4 => 48
    | 5 => 130
    | 6 => 96
    | 7 => 164
    | 8 => 121
    | 9 => 186
    | 10 => 107
    | 11 => 190
    | 12 => 178
    | 13 => 127
    | 14 => 144
    | 15 => 120
    | 16 => 106
    | 17 => 153
    | 18 => 85
    | 19 => 72
    | 20 => 45
    | 21 => 24
    | 22 => 66
    | 23 => 90
    | 24 => 38
    | 25 => 154
    | _ => 103
  point := fun i =>
    match i.val with
    | 0 => 521 / 2
    | 1 => 767532483856421 / 4000000000000
    | 2 => 248204235329093 / 800000000000
    | 3 => 223964064536047 / 4000000000000
    | 4 => 601598980495459 / 4000000000000
    | 5 => 1633458259713303 / 4000000000000
    | 6 => 1203197960991439 / 4000000000000
    | 7 => 2061700214011147 / 4000000000000
    | 8 => 1518639046282273 / 4000000000000
    | 9 => 2329982832554479 / 4000000000000
    | 10 => 1345216215582391 / 4000000000000
    | 11 => 2387109780840419 / 4000000000000
    | 12 => 2230347604997711 / 4000000000000
    | 13 => 1591681291380863 / 4000000000000
    | 14 => 1804796941486377 / 4000000000000
    | 15 => 1504651530271513 / 4000000000000
    | 16 => 1329405258497773 / 4000000000000
    | 17 => 385313459971527 / 800000000000
    | 18 => 1065797308217669 / 4000000000000
    | 19 => 903488181558109 / 4000000000000
    | 20 => 565360953717727 / 4000000000000
    | 21 => 304053001215009 / 4000000000000
    | 22 => 825563045032027 / 4000000000000
    | 23 => 1127235758435579 / 4000000000000
    | 24 => 476639046282273 / 4000000000000
    | 25 => 1937511260928833 / 4000000000000
    | _ => 1294167730155247 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-25107380501 / 1000000000000) (-25107380500 / 1000000000000), orderedInterval (-42536542859 / 1000000000000) (-42536542858 / 1000000000000))
    | 1 => (orderedInterval (-49401460171 / 1000000000000) (-49401460170 / 1000000000000), orderedInterval (-29489477908 / 1000000000000) (-29489477907 / 1000000000000))
    | 2 => (orderedInterval (-1024407903 / 1000000000000) (-1024407901 / 1000000000000), orderedInterval (-45284943142 / 1000000000000) (-45284943141 / 1000000000000))
    | 3 => (orderedInterval (23842902429 / 1000000000000) (23842902430 / 1000000000000), orderedInterval (103719568636 / 1000000000000) (103719568637 / 1000000000000))
    | 4 => (orderedInterval (24606589139 / 1000000000000) (24606589140 / 1000000000000), orderedInterval (60145963575 / 1000000000000) (60145963576 / 1000000000000))
    | 5 => (orderedInterval (26699329716 / 1000000000000) (26699329717 / 1000000000000), orderedInterval (29055030025 / 1000000000000) (29055030026 / 1000000000000))
    | 6 => (orderedInterval (-387441070 / 1000000000000) (-387441068 / 1000000000000), orderedInterval (46003671254 / 1000000000000) (46003671256 / 1000000000000))
    | 7 => (orderedInterval (29362674852 / 1000000000000) (29362674853 / 1000000000000), orderedInterval (19283910504 / 1000000000000) (19283910505 / 1000000000000))
    | 8 => (orderedInterval (-12574448159 / 1000000000000) (-12574448158 / 1000000000000), orderedInterval (-38953954184 / 1000000000000) (-38953954183 / 1000000000000))
    | 9 => (orderedInterval (-28763906984 / 1000000000000) (-28763815733 / 1000000000000), orderedInterval (16320579856 / 1000000000000) (16320671107 / 1000000000000))
    | 10 => (orderedInterval (-35101362628 / 1000000000000) (-35101362627 / 1000000000000), orderedInterval (-25655446397 / 1000000000000) (-25655446396 / 1000000000000))
    | 11 => (orderedInterval (20025975282 / 1000000000000) (20025975283 / 1000000000000), orderedInterval (25784827378 / 1000000000000) (25784827379 / 1000000000000))
    | 12 => (orderedInterval (-24966739640 / 1000000000000) (-24966726151 / 1000000000000), orderedInterval (22790848561 / 1000000000000) (22790862051 / 1000000000000))
    | 13 => (orderedInterval (10933010833 / 1000000000000) (10933010879 / 1000000000000), orderedInterval (-38488895886 / 1000000000000) (-38488895840 / 1000000000000))
    | 14 => (orderedInterval (-14799876333 / 1000000000000) (-14799876141 / 1000000000000), orderedInterval (34540518556 / 1000000000000) (34540518747 / 1000000000000))
    | 15 => (orderedInterval (-1775411613 / 1000000000000) (-1775411611 / 1000000000000), orderedInterval (41102894545 / 1000000000000) (41102894547 / 1000000000000))
    | 16 => (orderedInterval (5565781680 / 1000000000000) (5565781681 / 1000000000000), orderedInterval (43402761963 / 1000000000000) (43402761964 / 1000000000000))
    | 17 => (orderedInterval (-35684675887 / 1000000000000) (-35684671542 / 1000000000000), orderedInterval (6992149784 / 1000000000000) (6992154129 / 1000000000000))
    | 18 => (orderedInterval (-9657348028 / 1000000000000) (-9657348027 / 1000000000000), orderedInterval (-47898586399 / 1000000000000) (-47898586398 / 1000000000000))
    | 19 => (orderedInterval (23674470193 / 1000000000000) (23674470194 / 1000000000000), orderedInterval (47466232084 / 1000000000000) (47466232085 / 1000000000000))
    | 20 => (orderedInterval (-45897897784 / 1000000000000) (-45897897783 / 1000000000000), orderedInterval (-48802417793 / 1000000000000) (-48802417792 / 1000000000000))
    | 21 => (orderedInterval (90164069824 / 1000000000000) (90164069826 / 1000000000000), orderedInterval (15071738595 / 1000000000000) (15071738597 / 1000000000000))
    | 22 => (orderedInterval (-9372125801 / 1000000000000) (-9372125761 / 1000000000000), orderedInterval (54764900300 / 1000000000000) (54764900339 / 1000000000000))
    | 23 => (orderedInterval (-7076602866 / 1000000000000) (-7076602850 / 1000000000000), orderedInterval (47012263723 / 1000000000000) (47012263739 / 1000000000000))
    | 24 => (orderedInterval (39047840146 / 1000000000000) (39047840147 / 1000000000000), orderedInterval (61624988326 / 1000000000000) (61624988327 / 1000000000000))
    | 25 => (orderedInterval (35433198794 / 1000000000000) (35433198819 / 1000000000000), orderedInterval (7631013876 / 1000000000000) (7631013901 / 1000000000000))
    | _ => (orderedInterval (-30005143112 / 1000000000000) (-30005143111 / 1000000000000), orderedInterval (-32623942207 / 1000000000000) (-32623942206 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-10472125899 / 1000000000000) (-10472125880 / 1000000000000)
      | 1 => orderedInterval (-1258294835 / 1000000000000) (-1258294803 / 1000000000000)
      | 2 => orderedInterval (-1209561983 / 1000000000000) (-1209561967 / 1000000000000)
      | 3 => orderedInterval (5357070967 / 1000000000000) (5357087285 / 1000000000000)
      | 4 => orderedInterval (1559479175 / 1000000000000) (1559479455 / 1000000000000)
      | 5 => orderedInterval (-1252681728 / 1000000000000) (-1252681591 / 1000000000000)
      | 6 => orderedInterval (-1290055546 / 1000000000000) (-1290055480 / 1000000000000)
      | 7 => orderedInterval (-909923145 / 1000000000000) (-909923111 / 1000000000000)
      | _ => orderedInterval (2980828597 / 1000000000000) (2980828672 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-20227329765 / 1000000000000) (-20227329743 / 1000000000000)
      | 1 => orderedInterval (-2211917771 / 1000000000000) (-2211917735 / 1000000000000)
      | 2 => orderedInterval (-2548937283 / 1000000000000) (-2548937256 / 1000000000000)
      | 3 => orderedInterval (-541376941 / 1000000000000) (-541340470 / 1000000000000)
      | 4 => orderedInterval (-6743043336 / 1000000000000) (-6743042755 / 1000000000000)
      | 5 => orderedInterval (-2152488066 / 1000000000000) (-2152487824 / 1000000000000)
      | 6 => orderedInterval (4642041709 / 1000000000000) (4642041770 / 1000000000000)
      | 7 => orderedInterval (-4963269682 / 1000000000000) (-4963269651 / 1000000000000)
      | _ => orderedInterval (6617352962 / 1000000000000) (6617353068 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (10364364703 / 1000000000000) (10364364728 / 1000000000000)
      | 1 => orderedInterval (4385274005 / 1000000000000) (4385274055 / 1000000000000)
      | 2 => orderedInterval (4200832176 / 1000000000000) (4200832222 / 1000000000000)
      | 3 => orderedInterval (-36158974943 / 1000000000000) (-36158893273 / 1000000000000)
      | 4 => orderedInterval (-4676149149 / 1000000000000) (-4676147935 / 1000000000000)
      | 5 => orderedInterval (3692815723 / 1000000000000) (3692816158 / 1000000000000)
      | 6 => orderedInterval (-186007306 / 1000000000000) (-186007248 / 1000000000000)
      | 7 => orderedInterval (-607356178 / 1000000000000) (-607356147 / 1000000000000)
      | _ => orderedInterval (1213372101 / 1000000000000) (1213372259 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (21419115921 / 1000000000000) (21419115950 / 1000000000000)
      | 1 => orderedInterval (7528666370 / 1000000000000) (7528666444 / 1000000000000)
      | 2 => orderedInterval (7505486710 / 1000000000000) (7505486793 / 1000000000000)
      | 3 => orderedInterval (-7418564930 / 1000000000000) (-7418382333 / 1000000000000)
      | 4 => orderedInterval (17933381148 / 1000000000000) (17933383703 / 1000000000000)
      | 5 => orderedInterval (2583172576 / 1000000000000) (2583173364 / 1000000000000)
      | 6 => orderedInterval (-6189553298 / 1000000000000) (-6189553241 / 1000000000000)
      | 7 => orderedInterval (5188515275 / 1000000000000) (5188515306 / 1000000000000)
      | _ => orderedInterval (-7774022695 / 1000000000000) (-7774022451 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10372445383 / 1000000000000) (-10372445350 / 1000000000000)
      | 1 => orderedInterval (-11420663203 / 1000000000000) (-11420663089 / 1000000000000)
      | 2 => orderedInterval (-15308945333 / 1000000000000) (-15308945180 / 1000000000000)
      | 3 => orderedInterval (199017805482 / 1000000000000) (199018214461 / 1000000000000)
      | 4 => orderedInterval (15625984861 / 1000000000000) (15625990269 / 1000000000000)
      | 5 => orderedInterval (-11629933333 / 1000000000000) (-11629931896 / 1000000000000)
      | 6 => orderedInterval (850745716 / 1000000000000) (850745771 / 1000000000000)
      | 7 => orderedInterval (774649770 / 1000000000000) (774649803 / 1000000000000)
      | _ => orderedInterval (-21012455153 / 1000000000000) (-21012454757 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-6495264397 / 1000000000000) (-6495247420 / 1000000000000)
    | 1 => orderedInterval (-28128968173 / 1000000000000) (-28128930596 / 1000000000000)
    | 2 => orderedInterval (-17771828868 / 1000000000000) (-17771745181 / 1000000000000)
    | 3 => orderedInterval (40776197077 / 1000000000000) (40776383535 / 1000000000000)
    | _ => orderedInterval (146524743424 / 1000000000000) (146525160032 / 1000000000000)

theorem compactCertificate389_stateChecks0 :
    compactCertificate389.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (521 / 2)) (orderedInterval (-25107380501 / 1000000000000) (-25107380500 / 1000000000000), orderedInterval (-42536542859 / 1000000000000) (-42536542858 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (767532483856421 / 4000000000000)) (orderedInterval (-49401460171 / 1000000000000) (-49401460170 / 1000000000000), orderedInterval (-29489477908 / 1000000000000) (-29489477907 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (248204235329093 / 800000000000)) (orderedInterval (-1024407903 / 1000000000000) (-1024407901 / 1000000000000), orderedInterval (-45284943142 / 1000000000000) (-45284943141 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_stateChecks1 :
    compactCertificate389.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (223964064536047 / 4000000000000)) (orderedInterval (23842902429 / 1000000000000) (23842902430 / 1000000000000), orderedInterval (103719568636 / 1000000000000) (103719568637 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (601598980495459 / 4000000000000)) (orderedInterval (24606589139 / 1000000000000) (24606589140 / 1000000000000), orderedInterval (60145963575 / 1000000000000) (60145963576 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1633458259713303 / 4000000000000)) (orderedInterval (26699329716 / 1000000000000) (26699329717 / 1000000000000), orderedInterval (29055030025 / 1000000000000) (29055030026 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_stateChecks2 :
    compactCertificate389.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1203197960991439 / 4000000000000)) (orderedInterval (-387441070 / 1000000000000) (-387441068 / 1000000000000), orderedInterval (46003671254 / 1000000000000) (46003671256 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2061700214011147 / 4000000000000)) (orderedInterval (29362674852 / 1000000000000) (29362674853 / 1000000000000), orderedInterval (19283910504 / 1000000000000) (19283910505 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1518639046282273 / 4000000000000)) (orderedInterval (-12574448159 / 1000000000000) (-12574448158 / 1000000000000), orderedInterval (-38953954184 / 1000000000000) (-38953954183 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_stateChecks3 :
    compactCertificate389.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2329982832554479 / 4000000000000)) (orderedInterval (-28763906984 / 1000000000000) (-28763815733 / 1000000000000), orderedInterval (16320579856 / 1000000000000) (16320671107 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1345216215582391 / 4000000000000)) (orderedInterval (-35101362628 / 1000000000000) (-35101362627 / 1000000000000), orderedInterval (-25655446397 / 1000000000000) (-25655446396 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2387109780840419 / 4000000000000)) (orderedInterval (20025975282 / 1000000000000) (20025975283 / 1000000000000), orderedInterval (25784827378 / 1000000000000) (25784827379 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_stateChecks4 :
    compactCertificate389.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2230347604997711 / 4000000000000)) (orderedInterval (-24966739640 / 1000000000000) (-24966726151 / 1000000000000), orderedInterval (22790848561 / 1000000000000) (22790862051 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1591681291380863 / 4000000000000)) (orderedInterval (10933010833 / 1000000000000) (10933010879 / 1000000000000), orderedInterval (-38488895886 / 1000000000000) (-38488895840 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1804796941486377 / 4000000000000)) (orderedInterval (-14799876333 / 1000000000000) (-14799876141 / 1000000000000), orderedInterval (34540518556 / 1000000000000) (34540518747 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_stateChecks5 :
    compactCertificate389.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1504651530271513 / 4000000000000)) (orderedInterval (-1775411613 / 1000000000000) (-1775411611 / 1000000000000), orderedInterval (41102894545 / 1000000000000) (41102894547 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1329405258497773 / 4000000000000)) (orderedInterval (5565781680 / 1000000000000) (5565781681 / 1000000000000), orderedInterval (43402761963 / 1000000000000) (43402761964 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (385313459971527 / 800000000000)) (orderedInterval (-35684675887 / 1000000000000) (-35684671542 / 1000000000000), orderedInterval (6992149784 / 1000000000000) (6992154129 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_stateChecks6 :
    compactCertificate389.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1065797308217669 / 4000000000000)) (orderedInterval (-9657348028 / 1000000000000) (-9657348027 / 1000000000000), orderedInterval (-47898586399 / 1000000000000) (-47898586398 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (903488181558109 / 4000000000000)) (orderedInterval (23674470193 / 1000000000000) (23674470194 / 1000000000000), orderedInterval (47466232084 / 1000000000000) (47466232085 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (565360953717727 / 4000000000000)) (orderedInterval (-45897897784 / 1000000000000) (-45897897783 / 1000000000000), orderedInterval (-48802417793 / 1000000000000) (-48802417792 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_stateChecks7 :
    compactCertificate389.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (304053001215009 / 4000000000000)) (orderedInterval (90164069824 / 1000000000000) (90164069826 / 1000000000000), orderedInterval (15071738595 / 1000000000000) (15071738597 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (825563045032027 / 4000000000000)) (orderedInterval (-9372125801 / 1000000000000) (-9372125761 / 1000000000000), orderedInterval (54764900300 / 1000000000000) (54764900339 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1127235758435579 / 4000000000000)) (orderedInterval (-7076602866 / 1000000000000) (-7076602850 / 1000000000000), orderedInterval (47012263723 / 1000000000000) (47012263739 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_stateChecks8 :
    compactCertificate389.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (476639046282273 / 4000000000000)) (orderedInterval (39047840146 / 1000000000000) (39047840147 / 1000000000000), orderedInterval (61624988326 / 1000000000000) (61624988327 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1937511260928833 / 4000000000000)) (orderedInterval (35433198794 / 1000000000000) (35433198819 / 1000000000000), orderedInterval (7631013876 / 1000000000000) (7631013901 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1294167730155247 / 4000000000000)) (orderedInterval (-30005143112 / 1000000000000) (-30005143111 / 1000000000000), orderedInterval (-32623942207 / 1000000000000) (-32623942206 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_states : ∀ j,
    BesselStateValid (compactCertificate389.point j) (compactCertificate389.state j) :=
  compactCertificate389.statesValid_of_checks3 compactCertificate389_stateChecks0
    compactCertificate389_stateChecks1 compactCertificate389_stateChecks2
    compactCertificate389_stateChecks3 compactCertificate389_stateChecks4
    compactCertificate389_stateChecks5 compactCertificate389_stateChecks6
    compactCertificate389_stateChecks7 compactCertificate389_stateChecks8

theorem compactCertificate389_chunkChecks0_0 :
    compactCertificate389.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (521 / 2) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25107380501 / 1000000000000) (-25107380500 / 1000000000000), orderedInterval (-42536542859 / 1000000000000) (-42536542858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (767532483856421 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49401460171 / 1000000000000) (-49401460170 / 1000000000000), orderedInterval (-29489477908 / 1000000000000) (-29489477907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (248204235329093 / 800000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1024407903 / 1000000000000) (-1024407901 / 1000000000000), orderedInterval (-45284943142 / 1000000000000) (-45284943141 / 1000000000000)))) (orderedInterval (-10472125899 / 1000000000000) (-10472125880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (223964064536047 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (23842902429 / 1000000000000) (23842902430 / 1000000000000), orderedInterval (103719568636 / 1000000000000) (103719568637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (601598980495459 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24606589139 / 1000000000000) (24606589140 / 1000000000000), orderedInterval (60145963575 / 1000000000000) (60145963576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1633458259713303 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26699329716 / 1000000000000) (26699329717 / 1000000000000), orderedInterval (29055030025 / 1000000000000) (29055030026 / 1000000000000)))) (orderedInterval (-1258294835 / 1000000000000) (-1258294803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1203197960991439 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-387441070 / 1000000000000) (-387441068 / 1000000000000), orderedInterval (46003671254 / 1000000000000) (46003671256 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2061700214011147 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29362674852 / 1000000000000) (29362674853 / 1000000000000), orderedInterval (19283910504 / 1000000000000) (19283910505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1518639046282273 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12574448159 / 1000000000000) (-12574448158 / 1000000000000), orderedInterval (-38953954184 / 1000000000000) (-38953954183 / 1000000000000)))) (orderedInterval (-1209561983 / 1000000000000) (-1209561967 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_chunkChecks0_1 :
    compactCertificate389.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2329982832554479 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28763906984 / 1000000000000) (-28763815733 / 1000000000000), orderedInterval (16320579856 / 1000000000000) (16320671107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1345216215582391 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35101362628 / 1000000000000) (-35101362627 / 1000000000000), orderedInterval (-25655446397 / 1000000000000) (-25655446396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2387109780840419 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20025975282 / 1000000000000) (20025975283 / 1000000000000), orderedInterval (25784827378 / 1000000000000) (25784827379 / 1000000000000)))) (orderedInterval (5357070967 / 1000000000000) (5357087285 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2230347604997711 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24966739640 / 1000000000000) (-24966726151 / 1000000000000), orderedInterval (22790848561 / 1000000000000) (22790862051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1591681291380863 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10933010833 / 1000000000000) (10933010879 / 1000000000000), orderedInterval (-38488895886 / 1000000000000) (-38488895840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1804796941486377 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14799876333 / 1000000000000) (-14799876141 / 1000000000000), orderedInterval (34540518556 / 1000000000000) (34540518747 / 1000000000000)))) (orderedInterval (1559479175 / 1000000000000) (1559479455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1504651530271513 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1775411613 / 1000000000000) (-1775411611 / 1000000000000), orderedInterval (41102894545 / 1000000000000) (41102894547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1329405258497773 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5565781680 / 1000000000000) (5565781681 / 1000000000000), orderedInterval (43402761963 / 1000000000000) (43402761964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (385313459971527 / 800000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35684675887 / 1000000000000) (-35684671542 / 1000000000000), orderedInterval (6992149784 / 1000000000000) (6992154129 / 1000000000000)))) (orderedInterval (-1252681728 / 1000000000000) (-1252681591 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_chunkChecks0_2 :
    compactCertificate389.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1065797308217669 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-9657348028 / 1000000000000) (-9657348027 / 1000000000000), orderedInterval (-47898586399 / 1000000000000) (-47898586398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (903488181558109 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23674470193 / 1000000000000) (23674470194 / 1000000000000), orderedInterval (47466232084 / 1000000000000) (47466232085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (565360953717727 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45897897784 / 1000000000000) (-45897897783 / 1000000000000), orderedInterval (-48802417793 / 1000000000000) (-48802417792 / 1000000000000)))) (orderedInterval (-1290055546 / 1000000000000) (-1290055480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (304053001215009 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90164069824 / 1000000000000) (90164069826 / 1000000000000), orderedInterval (15071738595 / 1000000000000) (15071738597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (825563045032027 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9372125801 / 1000000000000) (-9372125761 / 1000000000000), orderedInterval (54764900300 / 1000000000000) (54764900339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1127235758435579 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7076602866 / 1000000000000) (-7076602850 / 1000000000000), orderedInterval (47012263723 / 1000000000000) (47012263739 / 1000000000000)))) (orderedInterval (-909923145 / 1000000000000) (-909923111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (476639046282273 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (39047840146 / 1000000000000) (39047840147 / 1000000000000), orderedInterval (61624988326 / 1000000000000) (61624988327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1937511260928833 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35433198794 / 1000000000000) (35433198819 / 1000000000000), orderedInterval (7631013876 / 1000000000000) (7631013901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1294167730155247 / 4000000000000) 0 (IntervalRat.scale (521 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30005143112 / 1000000000000) (-30005143111 / 1000000000000), orderedInterval (-32623942207 / 1000000000000) (-32623942206 / 1000000000000)))) (orderedInterval (2980828597 / 1000000000000) (2980828672 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_chunkChecks0 :
    compactCertificate389.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate389.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate389_chunkChecks0_0
    compactCertificate389_chunkChecks0_1 compactCertificate389_chunkChecks0_2

theorem compactCertificate389_chunkChecks1_0 :
    compactCertificate389.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (521 / 2) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25107380501 / 1000000000000) (-25107380500 / 1000000000000), orderedInterval (-42536542859 / 1000000000000) (-42536542858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (767532483856421 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49401460171 / 1000000000000) (-49401460170 / 1000000000000), orderedInterval (-29489477908 / 1000000000000) (-29489477907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (248204235329093 / 800000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1024407903 / 1000000000000) (-1024407901 / 1000000000000), orderedInterval (-45284943142 / 1000000000000) (-45284943141 / 1000000000000)))) (orderedInterval (-20227329765 / 1000000000000) (-20227329743 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (223964064536047 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (23842902429 / 1000000000000) (23842902430 / 1000000000000), orderedInterval (103719568636 / 1000000000000) (103719568637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (601598980495459 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24606589139 / 1000000000000) (24606589140 / 1000000000000), orderedInterval (60145963575 / 1000000000000) (60145963576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1633458259713303 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26699329716 / 1000000000000) (26699329717 / 1000000000000), orderedInterval (29055030025 / 1000000000000) (29055030026 / 1000000000000)))) (orderedInterval (-2211917771 / 1000000000000) (-2211917735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1203197960991439 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-387441070 / 1000000000000) (-387441068 / 1000000000000), orderedInterval (46003671254 / 1000000000000) (46003671256 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2061700214011147 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29362674852 / 1000000000000) (29362674853 / 1000000000000), orderedInterval (19283910504 / 1000000000000) (19283910505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1518639046282273 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12574448159 / 1000000000000) (-12574448158 / 1000000000000), orderedInterval (-38953954184 / 1000000000000) (-38953954183 / 1000000000000)))) (orderedInterval (-2548937283 / 1000000000000) (-2548937256 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_chunkChecks1_1 :
    compactCertificate389.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2329982832554479 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28763906984 / 1000000000000) (-28763815733 / 1000000000000), orderedInterval (16320579856 / 1000000000000) (16320671107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1345216215582391 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35101362628 / 1000000000000) (-35101362627 / 1000000000000), orderedInterval (-25655446397 / 1000000000000) (-25655446396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2387109780840419 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20025975282 / 1000000000000) (20025975283 / 1000000000000), orderedInterval (25784827378 / 1000000000000) (25784827379 / 1000000000000)))) (orderedInterval (-541376941 / 1000000000000) (-541340470 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2230347604997711 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24966739640 / 1000000000000) (-24966726151 / 1000000000000), orderedInterval (22790848561 / 1000000000000) (22790862051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1591681291380863 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10933010833 / 1000000000000) (10933010879 / 1000000000000), orderedInterval (-38488895886 / 1000000000000) (-38488895840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1804796941486377 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14799876333 / 1000000000000) (-14799876141 / 1000000000000), orderedInterval (34540518556 / 1000000000000) (34540518747 / 1000000000000)))) (orderedInterval (-6743043336 / 1000000000000) (-6743042755 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1504651530271513 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1775411613 / 1000000000000) (-1775411611 / 1000000000000), orderedInterval (41102894545 / 1000000000000) (41102894547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1329405258497773 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5565781680 / 1000000000000) (5565781681 / 1000000000000), orderedInterval (43402761963 / 1000000000000) (43402761964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (385313459971527 / 800000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35684675887 / 1000000000000) (-35684671542 / 1000000000000), orderedInterval (6992149784 / 1000000000000) (6992154129 / 1000000000000)))) (orderedInterval (-2152488066 / 1000000000000) (-2152487824 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_chunkChecks1_2 :
    compactCertificate389.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1065797308217669 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-9657348028 / 1000000000000) (-9657348027 / 1000000000000), orderedInterval (-47898586399 / 1000000000000) (-47898586398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (903488181558109 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23674470193 / 1000000000000) (23674470194 / 1000000000000), orderedInterval (47466232084 / 1000000000000) (47466232085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (565360953717727 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45897897784 / 1000000000000) (-45897897783 / 1000000000000), orderedInterval (-48802417793 / 1000000000000) (-48802417792 / 1000000000000)))) (orderedInterval (4642041709 / 1000000000000) (4642041770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (304053001215009 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90164069824 / 1000000000000) (90164069826 / 1000000000000), orderedInterval (15071738595 / 1000000000000) (15071738597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (825563045032027 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9372125801 / 1000000000000) (-9372125761 / 1000000000000), orderedInterval (54764900300 / 1000000000000) (54764900339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1127235758435579 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7076602866 / 1000000000000) (-7076602850 / 1000000000000), orderedInterval (47012263723 / 1000000000000) (47012263739 / 1000000000000)))) (orderedInterval (-4963269682 / 1000000000000) (-4963269651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (476639046282273 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (39047840146 / 1000000000000) (39047840147 / 1000000000000), orderedInterval (61624988326 / 1000000000000) (61624988327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1937511260928833 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35433198794 / 1000000000000) (35433198819 / 1000000000000), orderedInterval (7631013876 / 1000000000000) (7631013901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1294167730155247 / 4000000000000) 1 (IntervalRat.scale (521 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30005143112 / 1000000000000) (-30005143111 / 1000000000000), orderedInterval (-32623942207 / 1000000000000) (-32623942206 / 1000000000000)))) (orderedInterval (6617352962 / 1000000000000) (6617353068 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_chunkChecks1 :
    compactCertificate389.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate389.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate389_chunkChecks1_0
    compactCertificate389_chunkChecks1_1 compactCertificate389_chunkChecks1_2

theorem compactCertificate389_chunkChecks2_0 :
    compactCertificate389.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (521 / 2) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25107380501 / 1000000000000) (-25107380500 / 1000000000000), orderedInterval (-42536542859 / 1000000000000) (-42536542858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (767532483856421 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49401460171 / 1000000000000) (-49401460170 / 1000000000000), orderedInterval (-29489477908 / 1000000000000) (-29489477907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (248204235329093 / 800000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1024407903 / 1000000000000) (-1024407901 / 1000000000000), orderedInterval (-45284943142 / 1000000000000) (-45284943141 / 1000000000000)))) (orderedInterval (10364364703 / 1000000000000) (10364364728 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (223964064536047 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (23842902429 / 1000000000000) (23842902430 / 1000000000000), orderedInterval (103719568636 / 1000000000000) (103719568637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (601598980495459 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24606589139 / 1000000000000) (24606589140 / 1000000000000), orderedInterval (60145963575 / 1000000000000) (60145963576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1633458259713303 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26699329716 / 1000000000000) (26699329717 / 1000000000000), orderedInterval (29055030025 / 1000000000000) (29055030026 / 1000000000000)))) (orderedInterval (4385274005 / 1000000000000) (4385274055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1203197960991439 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-387441070 / 1000000000000) (-387441068 / 1000000000000), orderedInterval (46003671254 / 1000000000000) (46003671256 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2061700214011147 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29362674852 / 1000000000000) (29362674853 / 1000000000000), orderedInterval (19283910504 / 1000000000000) (19283910505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1518639046282273 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12574448159 / 1000000000000) (-12574448158 / 1000000000000), orderedInterval (-38953954184 / 1000000000000) (-38953954183 / 1000000000000)))) (orderedInterval (4200832176 / 1000000000000) (4200832222 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_chunkChecks2_1 :
    compactCertificate389.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2329982832554479 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28763906984 / 1000000000000) (-28763815733 / 1000000000000), orderedInterval (16320579856 / 1000000000000) (16320671107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1345216215582391 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35101362628 / 1000000000000) (-35101362627 / 1000000000000), orderedInterval (-25655446397 / 1000000000000) (-25655446396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2387109780840419 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20025975282 / 1000000000000) (20025975283 / 1000000000000), orderedInterval (25784827378 / 1000000000000) (25784827379 / 1000000000000)))) (orderedInterval (-36158974943 / 1000000000000) (-36158893273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2230347604997711 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24966739640 / 1000000000000) (-24966726151 / 1000000000000), orderedInterval (22790848561 / 1000000000000) (22790862051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1591681291380863 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10933010833 / 1000000000000) (10933010879 / 1000000000000), orderedInterval (-38488895886 / 1000000000000) (-38488895840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1804796941486377 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14799876333 / 1000000000000) (-14799876141 / 1000000000000), orderedInterval (34540518556 / 1000000000000) (34540518747 / 1000000000000)))) (orderedInterval (-4676149149 / 1000000000000) (-4676147935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1504651530271513 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1775411613 / 1000000000000) (-1775411611 / 1000000000000), orderedInterval (41102894545 / 1000000000000) (41102894547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1329405258497773 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5565781680 / 1000000000000) (5565781681 / 1000000000000), orderedInterval (43402761963 / 1000000000000) (43402761964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (385313459971527 / 800000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35684675887 / 1000000000000) (-35684671542 / 1000000000000), orderedInterval (6992149784 / 1000000000000) (6992154129 / 1000000000000)))) (orderedInterval (3692815723 / 1000000000000) (3692816158 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_chunkChecks2_2 :
    compactCertificate389.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1065797308217669 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-9657348028 / 1000000000000) (-9657348027 / 1000000000000), orderedInterval (-47898586399 / 1000000000000) (-47898586398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (903488181558109 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23674470193 / 1000000000000) (23674470194 / 1000000000000), orderedInterval (47466232084 / 1000000000000) (47466232085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (565360953717727 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45897897784 / 1000000000000) (-45897897783 / 1000000000000), orderedInterval (-48802417793 / 1000000000000) (-48802417792 / 1000000000000)))) (orderedInterval (-186007306 / 1000000000000) (-186007248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (304053001215009 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90164069824 / 1000000000000) (90164069826 / 1000000000000), orderedInterval (15071738595 / 1000000000000) (15071738597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (825563045032027 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9372125801 / 1000000000000) (-9372125761 / 1000000000000), orderedInterval (54764900300 / 1000000000000) (54764900339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1127235758435579 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7076602866 / 1000000000000) (-7076602850 / 1000000000000), orderedInterval (47012263723 / 1000000000000) (47012263739 / 1000000000000)))) (orderedInterval (-607356178 / 1000000000000) (-607356147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (476639046282273 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (39047840146 / 1000000000000) (39047840147 / 1000000000000), orderedInterval (61624988326 / 1000000000000) (61624988327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1937511260928833 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35433198794 / 1000000000000) (35433198819 / 1000000000000), orderedInterval (7631013876 / 1000000000000) (7631013901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1294167730155247 / 4000000000000) 2 (IntervalRat.scale (521 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30005143112 / 1000000000000) (-30005143111 / 1000000000000), orderedInterval (-32623942207 / 1000000000000) (-32623942206 / 1000000000000)))) (orderedInterval (1213372101 / 1000000000000) (1213372259 / 1000000000000))) = true
  rfl'

theorem compactCertificate389_chunkChecks2 :
    compactCertificate389.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate389.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate389_chunkChecks2_0
    compactCertificate389_chunkChecks2_1 compactCertificate389_chunkChecks2_2

theorem compactCertificate389_chunkChecks3_0 :
    compactCertificate389.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (521 / 2) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25107380501 / 1000000000000) (-25107380500 / 1000000000000), orderedInterval (-42536542859 / 1000000000000) (-42536542858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (767532483856421 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49401460171 / 1000000000000) (-49401460170 / 1000000000000), orderedInterval (-29489477908 / 1000000000000) (-29489477907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (248204235329093 / 800000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1024407903 / 1000000000000) (-1024407901 / 1000000000000), orderedInterval (-45284943142 / 1000000000000) (-45284943141 / 1000000000000)))) (orderedInterval (21419115921 / 1000000000000) (21419115950 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (223964064536047 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (23842902429 / 1000000000000) (23842902430 / 1000000000000), orderedInterval (103719568636 / 1000000000000) (103719568637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (601598980495459 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24606589139 / 1000000000000) (24606589140 / 1000000000000), orderedInterval (60145963575 / 1000000000000) (60145963576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1633458259713303 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26699329716 / 1000000000000) (26699329717 / 1000000000000), orderedInterval (29055030025 / 1000000000000) (29055030026 / 1000000000000)))) (orderedInterval (7528666370 / 1000000000000) (7528666444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1203197960991439 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-387441070 / 1000000000000) (-387441068 / 1000000000000), orderedInterval (46003671254 / 1000000000000) (46003671256 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2061700214011147 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29362674852 / 1000000000000) (29362674853 / 1000000000000), orderedInterval (19283910504 / 1000000000000) (19283910505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1518639046282273 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12574448159 / 1000000000000) (-12574448158 / 1000000000000), orderedInterval (-38953954184 / 1000000000000) (-38953954183 / 1000000000000)))) (orderedInterval (7505486710 / 1000000000000) (7505486793 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate389_chunkChecks3_1 :
    compactCertificate389.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2329982832554479 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28763906984 / 1000000000000) (-28763815733 / 1000000000000), orderedInterval (16320579856 / 1000000000000) (16320671107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1345216215582391 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35101362628 / 1000000000000) (-35101362627 / 1000000000000), orderedInterval (-25655446397 / 1000000000000) (-25655446396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2387109780840419 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20025975282 / 1000000000000) (20025975283 / 1000000000000), orderedInterval (25784827378 / 1000000000000) (25784827379 / 1000000000000)))) (orderedInterval (-7418564930 / 1000000000000) (-7418382333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2230347604997711 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24966739640 / 1000000000000) (-24966726151 / 1000000000000), orderedInterval (22790848561 / 1000000000000) (22790862051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1591681291380863 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10933010833 / 1000000000000) (10933010879 / 1000000000000), orderedInterval (-38488895886 / 1000000000000) (-38488895840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1804796941486377 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14799876333 / 1000000000000) (-14799876141 / 1000000000000), orderedInterval (34540518556 / 1000000000000) (34540518747 / 1000000000000)))) (orderedInterval (17933381148 / 1000000000000) (17933383703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1504651530271513 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1775411613 / 1000000000000) (-1775411611 / 1000000000000), orderedInterval (41102894545 / 1000000000000) (41102894547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1329405258497773 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5565781680 / 1000000000000) (5565781681 / 1000000000000), orderedInterval (43402761963 / 1000000000000) (43402761964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (385313459971527 / 800000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35684675887 / 1000000000000) (-35684671542 / 1000000000000), orderedInterval (6992149784 / 1000000000000) (6992154129 / 1000000000000)))) (orderedInterval (2583172576 / 1000000000000) (2583173364 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate389_chunkChecks3_2 :
    compactCertificate389.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1065797308217669 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-9657348028 / 1000000000000) (-9657348027 / 1000000000000), orderedInterval (-47898586399 / 1000000000000) (-47898586398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (903488181558109 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23674470193 / 1000000000000) (23674470194 / 1000000000000), orderedInterval (47466232084 / 1000000000000) (47466232085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (565360953717727 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45897897784 / 1000000000000) (-45897897783 / 1000000000000), orderedInterval (-48802417793 / 1000000000000) (-48802417792 / 1000000000000)))) (orderedInterval (-6189553298 / 1000000000000) (-6189553241 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (304053001215009 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90164069824 / 1000000000000) (90164069826 / 1000000000000), orderedInterval (15071738595 / 1000000000000) (15071738597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (825563045032027 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9372125801 / 1000000000000) (-9372125761 / 1000000000000), orderedInterval (54764900300 / 1000000000000) (54764900339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1127235758435579 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7076602866 / 1000000000000) (-7076602850 / 1000000000000), orderedInterval (47012263723 / 1000000000000) (47012263739 / 1000000000000)))) (orderedInterval (5188515275 / 1000000000000) (5188515306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (476639046282273 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (39047840146 / 1000000000000) (39047840147 / 1000000000000), orderedInterval (61624988326 / 1000000000000) (61624988327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1937511260928833 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35433198794 / 1000000000000) (35433198819 / 1000000000000), orderedInterval (7631013876 / 1000000000000) (7631013901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1294167730155247 / 4000000000000) 3 (IntervalRat.scale (521 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30005143112 / 1000000000000) (-30005143111 / 1000000000000), orderedInterval (-32623942207 / 1000000000000) (-32623942206 / 1000000000000)))) (orderedInterval (-7774022695 / 1000000000000) (-7774022451 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate389_chunkChecks3 :
    compactCertificate389.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate389.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate389_chunkChecks3_0
    compactCertificate389_chunkChecks3_1 compactCertificate389_chunkChecks3_2

theorem compactCertificate389_chunkChecks4_0 :
    compactCertificate389.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (521 / 2) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25107380501 / 1000000000000) (-25107380500 / 1000000000000), orderedInterval (-42536542859 / 1000000000000) (-42536542858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (767532483856421 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-49401460171 / 1000000000000) (-49401460170 / 1000000000000), orderedInterval (-29489477908 / 1000000000000) (-29489477907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (248204235329093 / 800000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1024407903 / 1000000000000) (-1024407901 / 1000000000000), orderedInterval (-45284943142 / 1000000000000) (-45284943141 / 1000000000000)))) (orderedInterval (-10372445383 / 1000000000000) (-10372445350 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (223964064536047 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (23842902429 / 1000000000000) (23842902430 / 1000000000000), orderedInterval (103719568636 / 1000000000000) (103719568637 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (601598980495459 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (24606589139 / 1000000000000) (24606589140 / 1000000000000), orderedInterval (60145963575 / 1000000000000) (60145963576 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1633458259713303 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26699329716 / 1000000000000) (26699329717 / 1000000000000), orderedInterval (29055030025 / 1000000000000) (29055030026 / 1000000000000)))) (orderedInterval (-11420663203 / 1000000000000) (-11420663089 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1203197960991439 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-387441070 / 1000000000000) (-387441068 / 1000000000000), orderedInterval (46003671254 / 1000000000000) (46003671256 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2061700214011147 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29362674852 / 1000000000000) (29362674853 / 1000000000000), orderedInterval (19283910504 / 1000000000000) (19283910505 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1518639046282273 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12574448159 / 1000000000000) (-12574448158 / 1000000000000), orderedInterval (-38953954184 / 1000000000000) (-38953954183 / 1000000000000)))) (orderedInterval (-15308945333 / 1000000000000) (-15308945180 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate389_chunkChecks4_1 :
    compactCertificate389.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2329982832554479 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28763906984 / 1000000000000) (-28763815733 / 1000000000000), orderedInterval (16320579856 / 1000000000000) (16320671107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1345216215582391 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35101362628 / 1000000000000) (-35101362627 / 1000000000000), orderedInterval (-25655446397 / 1000000000000) (-25655446396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2387109780840419 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20025975282 / 1000000000000) (20025975283 / 1000000000000), orderedInterval (25784827378 / 1000000000000) (25784827379 / 1000000000000)))) (orderedInterval (199017805482 / 1000000000000) (199018214461 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2230347604997711 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24966739640 / 1000000000000) (-24966726151 / 1000000000000), orderedInterval (22790848561 / 1000000000000) (22790862051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1591681291380863 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10933010833 / 1000000000000) (10933010879 / 1000000000000), orderedInterval (-38488895886 / 1000000000000) (-38488895840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1804796941486377 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-14799876333 / 1000000000000) (-14799876141 / 1000000000000), orderedInterval (34540518556 / 1000000000000) (34540518747 / 1000000000000)))) (orderedInterval (15625984861 / 1000000000000) (15625990269 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1504651530271513 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1775411613 / 1000000000000) (-1775411611 / 1000000000000), orderedInterval (41102894545 / 1000000000000) (41102894547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1329405258497773 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5565781680 / 1000000000000) (5565781681 / 1000000000000), orderedInterval (43402761963 / 1000000000000) (43402761964 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (385313459971527 / 800000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35684675887 / 1000000000000) (-35684671542 / 1000000000000), orderedInterval (6992149784 / 1000000000000) (6992154129 / 1000000000000)))) (orderedInterval (-11629933333 / 1000000000000) (-11629931896 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate389_chunkChecks4_2 :
    compactCertificate389.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1065797308217669 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-9657348028 / 1000000000000) (-9657348027 / 1000000000000), orderedInterval (-47898586399 / 1000000000000) (-47898586398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (903488181558109 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (23674470193 / 1000000000000) (23674470194 / 1000000000000), orderedInterval (47466232084 / 1000000000000) (47466232085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (565360953717727 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-45897897784 / 1000000000000) (-45897897783 / 1000000000000), orderedInterval (-48802417793 / 1000000000000) (-48802417792 / 1000000000000)))) (orderedInterval (850745716 / 1000000000000) (850745771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (304053001215009 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90164069824 / 1000000000000) (90164069826 / 1000000000000), orderedInterval (15071738595 / 1000000000000) (15071738597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (825563045032027 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9372125801 / 1000000000000) (-9372125761 / 1000000000000), orderedInterval (54764900300 / 1000000000000) (54764900339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1127235758435579 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7076602866 / 1000000000000) (-7076602850 / 1000000000000), orderedInterval (47012263723 / 1000000000000) (47012263739 / 1000000000000)))) (orderedInterval (774649770 / 1000000000000) (774649803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (476639046282273 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (39047840146 / 1000000000000) (39047840147 / 1000000000000), orderedInterval (61624988326 / 1000000000000) (61624988327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1937511260928833 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35433198794 / 1000000000000) (35433198819 / 1000000000000), orderedInterval (7631013876 / 1000000000000) (7631013901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1294167730155247 / 4000000000000) 4 (IntervalRat.scale (521 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-30005143112 / 1000000000000) (-30005143111 / 1000000000000), orderedInterval (-32623942207 / 1000000000000) (-32623942206 / 1000000000000)))) (orderedInterval (-21012455153 / 1000000000000) (-21012454757 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate389_chunkChecks4 :
    compactCertificate389.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate389.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate389_chunkChecks4_0
    compactCertificate389_chunkChecks4_1 compactCertificate389_chunkChecks4_2

theorem compactCertificate389_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate389.chunkCheck r b = true :=
  compactCertificate389.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate389_chunkChecks0
    · exact compactCertificate389_chunkChecks1
    · exact compactCertificate389_chunkChecks2
    · exact compactCertificate389_chunkChecks3
    · exact compactCertificate389_chunkChecks4)

theorem compactCertificate389_coefficient0 :
    compactCertificate389.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate389_coefficient1 :
    compactCertificate389.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate389_coefficient2 :
    compactCertificate389.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate389_coefficient3 :
    compactCertificate389.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate389_coefficient4 :
    compactCertificate389.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate389_coefficients : ∀ r : Fin 5,
    compactCertificate389.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate389_coefficient0
  · exact compactCertificate389_coefficient1
  · exact compactCertificate389_coefficient2
  · exact compactCertificate389_coefficient3
  · exact compactCertificate389_coefficient4

theorem compactCertificate389_lower : (1 : ℚ) ≤ compactCertificate389.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate389, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate389_proves {t : ℝ} (ht : t ∈ compactCertificate389.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate389.proves compactCertificate389_states compactCertificate389_chunks
    compactCertificate389_coefficients compactCertificate389_lower ht

end Erdos232
