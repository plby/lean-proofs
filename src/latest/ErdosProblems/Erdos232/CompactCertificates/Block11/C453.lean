/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate453 : CompactCertificate where
  left := 324
  right := 325
  center := 649 / 2
  grid := fun i =>
    match i.val with
    | 0 => 103
    | 1 => 76
    | 2 => 123
    | 3 => 22
    | 4 => 60
    | 5 => 162
    | 6 => 119
    | 7 => 204
    | 8 => 151
    | 9 => 231
    | 10 => 133
    | 11 => 237
    | 12 => 221
    | 13 => 158
    | 14 => 179
    | 15 => 149
    | 16 => 132
    | 17 => 191
    | 18 => 106
    | 19 => 90
    | 20 => 56
    | 21 => 30
    | 22 => 82
    | 23 => 112
    | 24 => 47
    | 25 => 192
    | _ => 128
  point := fun i =>
    match i.val with
    | 0 => 649 / 2
    | 1 => 956100925187749 / 4000000000000
    | 2 => 309183394872517 / 800000000000
    | 3 => 278987865420143 / 4000000000000
    | 4 => 749400649407971 / 4000000000000
    | 5 => 2034768542330007 / 4000000000000
    | 6 => 1498801298816591 / 4000000000000
    | 7 => 2568221571772043 / 4000000000000
    | 8 => 1891740385867937 / 4000000000000
    | 9 => 2902416234794351 / 4000000000000
    | 10 => 1675710794458679 / 4000000000000
    | 11 => 2973578210682211 / 4000000000000
    | 12 => 2778302486839759 / 4000000000000
    | 13 => 1982727750683647 / 4000000000000
    | 14 => 2248201948223913 / 4000000000000
    | 15 => 1874316397593497 / 4000000000000
    | 16 => 1656015379587437 / 4000000000000
    | 17 => 479977803304263 / 800000000000
    | 18 => 1327643863787461 / 4000000000000
    | 19 => 1125458406585821 / 4000000000000
    | 20 => 704259614132063 / 4000000000000
    | 21 => 378753162741921 / 4000000000000
    | 22 => 1028388514828763 / 4000000000000
    | 23 => 1404176597360251 / 4000000000000
    | 24 => 593740385867937 / 4000000000000
    | 25 => 2413521705072577 / 4000000000000
    | _ => 1612120646584943 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-43917988293 / 1000000000000) (-43917987418 / 1000000000000), orderedInterval (5817138136 / 1000000000000) (5817139010 / 1000000000000))
    | 1 => (orderedInterval (44742014945 / 1000000000000) (44742014946 / 1000000000000), orderedInterval (25627003510 / 1000000000000) (25627003511 / 1000000000000))
    | 2 => (orderedInterval (-30449196263 / 1000000000000) (-30449196262 / 1000000000000), orderedInterval (-26794823150 / 1000000000000) (-26794823149 / 1000000000000))
    | 3 => (orderedInterval (94387835725 / 1000000000000) (94387835727 / 1000000000000), orderedInterval (14097536501 / 1000000000000) (14097536503 / 1000000000000))
    | 4 => (orderedInterval (-20571249242 / 1000000000000) (-20571248636 / 1000000000000), orderedInterval (54597119537 / 1000000000000) (54597120143 / 1000000000000))
    | 5 => (orderedInterval (18166322697 / 1000000000000) (18166322698 / 1000000000000), orderedInterval (30337842467 / 1000000000000) (30337842468 / 1000000000000))
    | 6 => (orderedInterval (-41131812052 / 1000000000000) (-41131811514 / 1000000000000), orderedInterval (2735002035 / 1000000000000) (2735002573 / 1000000000000))
    | 7 => (orderedInterval (29184777910 / 1000000000000) (29184837968 / 1000000000000), orderedInterval (-11845648300 / 1000000000000) (-11845588242 / 1000000000000))
    | 8 => (orderedInterval (22502358697 / 1000000000000) (22502362322 / 1000000000000), orderedInterval (-29002194926 / 1000000000000) (-29002191302 / 1000000000000))
    | 9 => (orderedInterval (-18656871745 / 1000000000000) (-18656871744 / 1000000000000), orderedInterval (-22993369382 / 1000000000000) (-22993369381 / 1000000000000))
    | 10 => (orderedInterval (-37122275751 / 1000000000000) (-37122265246 / 1000000000000), orderedInterval (11942926697 / 1000000000000) (11942937201 / 1000000000000))
    | 11 => (orderedInterval (10791351567 / 1000000000000) (10791351582 / 1000000000000), orderedInterval (-27208645980 / 1000000000000) (-27208645965 / 1000000000000))
    | 12 => (orderedInterval (-26540468468 / 1000000000000) (-26540468466 / 1000000000000), orderedInterval (-14546701859 / 1000000000000) (-14546701857 / 1000000000000))
    | 13 => (orderedInterval (3415302943 / 1000000000000) (3415302944 / 1000000000000), orderedInterval (35671021115 / 1000000000000) (35671021116 / 1000000000000))
    | 14 => (orderedInterval (-15856169327 / 1000000000000) (-15856169326 / 1000000000000), orderedInterval (-29671847036 / 1000000000000) (-29671847035 / 1000000000000))
    | 15 => (orderedInterval (-35170719188 / 1000000000000) (-35170719182 / 1000000000000), orderedInterval (-10991405314 / 1000000000000) (-10991405308 / 1000000000000))
    | 16 => (orderedInterval (3864533979 / 1000000000000) (3864533980 / 1000000000000), orderedInterval (39018160858 / 1000000000000) (39018160859 / 1000000000000))
    | 17 => (orderedInterval (-21313096752 / 1000000000000) (-21313096751 / 1000000000000), orderedInterval (-24616238796 / 1000000000000) (-24616238795 / 1000000000000))
    | 18 => (orderedInterval (-13478317943 / 1000000000000) (-13478317818 / 1000000000000), orderedInterval (41690203420 / 1000000000000) (41690203544 / 1000000000000))
    | 19 => (orderedInterval (-26613725349 / 1000000000000) (-26613720333 / 1000000000000), orderedInterval (39472233931 / 1000000000000) (39472238946 / 1000000000000))
    | 20 => (orderedInterval (47855483768 / 1000000000000) (47855483769 / 1000000000000), orderedInterval (36273893162 / 1000000000000) (36273893163 / 1000000000000))
    | 21 => (orderedInterval (77130222308 / 1000000000000) (77130222309 / 1000000000000), orderedInterval (27416774735 / 1000000000000) (27416774736 / 1000000000000))
    | 22 => (orderedInterval (13342076366 / 1000000000000) (13342076367 / 1000000000000), orderedInterval (47913357032 / 1000000000000) (47913357033 / 1000000000000))
    | 23 => (orderedInterval (-1242706540 / 1000000000000) (-1242706538 / 1000000000000), orderedInterval (42568904711 / 1000000000000) (42568904713 / 1000000000000))
    | 24 => (orderedInterval (-65488149203 / 1000000000000) (-65488149160 / 1000000000000), orderedInterval (-172245821 / 1000000000000) (-172245778 / 1000000000000))
    | 25 => (orderedInterval (26973199488 / 1000000000000) (26973199489 / 1000000000000), orderedInterval (18075573877 / 1000000000000) (18075573878 / 1000000000000))
    | _ => (orderedInterval (39455312960 / 1000000000000) (39455314211 / 1000000000000), orderedInterval (-4830213973 / 1000000000000) (-4830212722 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-18777437903 / 1000000000000) (-18777437533 / 1000000000000)
      | 1 => orderedInterval (-3066570702 / 1000000000000) (-3066570641 / 1000000000000)
      | 2 => orderedInterval (-356339568 / 1000000000000) (-356337609 / 1000000000000)
      | 3 => orderedInterval (2098699835 / 1000000000000) (2098700745 / 1000000000000)
      | 4 => orderedInterval (882339525 / 1000000000000) (882339564 / 1000000000000)
      | 5 => orderedInterval (-1172993776 / 1000000000000) (-1172993744 / 1000000000000)
      | 6 => orderedInterval (5219364752 / 1000000000000) (5219365138 / 1000000000000)
      | 7 => orderedInterval (-1631668819 / 1000000000000) (-1631668780 / 1000000000000)
      | _ => orderedInterval (-9993314036 / 1000000000000) (-9993313710 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (608935928 / 1000000000000) (608936301 / 1000000000000)
      | 1 => orderedInterval (-2262855611 / 1000000000000) (-2262855554 / 1000000000000)
      | 2 => orderedInterval (-298636814 / 1000000000000) (-298632989 / 1000000000000)
      | 3 => orderedInterval (1417271343 / 1000000000000) (1417272620 / 1000000000000)
      | 4 => orderedInterval (5974766091 / 1000000000000) (5974766155 / 1000000000000)
      | 5 => orderedInterval (-4197354464 / 1000000000000) (-4197354419 / 1000000000000)
      | 6 => orderedInterval (-8114605475 / 1000000000000) (-8114605133 / 1000000000000)
      | 7 => orderedInterval (-4538242815 / 1000000000000) (-4538242779 / 1000000000000)
      | _ => orderedInterval (-1610791297 / 1000000000000) (-1610790878 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (19714002158 / 1000000000000) (19714002536 / 1000000000000)
      | 1 => orderedInterval (3478259012 / 1000000000000) (3478259081 / 1000000000000)
      | 2 => orderedInterval (2369813127 / 1000000000000) (2369820634 / 1000000000000)
      | 3 => orderedInterval (-20046785652 / 1000000000000) (-20046783768 / 1000000000000)
      | 4 => orderedInterval (-3207889424 / 1000000000000) (-3207889319 / 1000000000000)
      | 5 => orderedInterval (3085235047 / 1000000000000) (3085235115 / 1000000000000)
      | 6 => orderedInterval (-3820753767 / 1000000000000) (-3820753460 / 1000000000000)
      | 7 => orderedInterval (213797470 / 1000000000000) (213797505 / 1000000000000)
      | _ => orderedInterval (19098381005 / 1000000000000) (19098381555 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (194449150 / 1000000000000) (194449532 / 1000000000000)
      | 1 => orderedInterval (7915437748 / 1000000000000) (7915437845 / 1000000000000)
      | 2 => orderedInterval (-667549265 / 1000000000000) (-667534519 / 1000000000000)
      | 3 => orderedInterval (-1017525330 / 1000000000000) (-1017522371 / 1000000000000)
      | 4 => orderedInterval (-15368291899 / 1000000000000) (-15368291722 / 1000000000000)
      | 5 => orderedInterval (8993210657 / 1000000000000) (8993210761 / 1000000000000)
      | 6 => orderedInterval (8412618707 / 1000000000000) (8412618984 / 1000000000000)
      | 7 => orderedInterval (4682789596 / 1000000000000) (4682789632 / 1000000000000)
      | _ => orderedInterval (7664136025 / 1000000000000) (7664136764 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-20881009503 / 1000000000000) (-20881009114 / 1000000000000)
      | 1 => orderedInterval (-7933315694 / 1000000000000) (-7933315549 / 1000000000000)
      | 2 => orderedInterval (-11338381269 / 1000000000000) (-11338352203 / 1000000000000)
      | 3 => orderedInterval (117496627422 / 1000000000000) (117496632438 / 1000000000000)
      | 4 => orderedInterval (12632456522 / 1000000000000) (12632456830 / 1000000000000)
      | 5 => orderedInterval (-8784212300 / 1000000000000) (-8784212135 / 1000000000000)
      | 6 => orderedInterval (3293344680 / 1000000000000) (3293344933 / 1000000000000)
      | 7 => orderedInterval (-28015325 / 1000000000000) (-28015286 / 1000000000000)
      | _ => orderedInterval (-43926245330 / 1000000000000) (-43926244305 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-26797920692 / 1000000000000) (-26797916570 / 1000000000000)
    | 1 => orderedInterval (-13021513114 / 1000000000000) (-13021506676 / 1000000000000)
    | 2 => orderedInterval (20884058976 / 1000000000000) (20884069879 / 1000000000000)
    | 3 => orderedInterval (20809275389 / 1000000000000) (20809294906 / 1000000000000)
    | _ => orderedInterval (40531249203 / 1000000000000) (40531285609 / 1000000000000)

theorem compactCertificate453_stateChecks0 :
    compactCertificate453.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (649 / 2)) (orderedInterval (-43917988293 / 1000000000000) (-43917987418 / 1000000000000), orderedInterval (5817138136 / 1000000000000) (5817139010 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (956100925187749 / 4000000000000)) (orderedInterval (44742014945 / 1000000000000) (44742014946 / 1000000000000), orderedInterval (25627003510 / 1000000000000) (25627003511 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (309183394872517 / 800000000000)) (orderedInterval (-30449196263 / 1000000000000) (-30449196262 / 1000000000000), orderedInterval (-26794823150 / 1000000000000) (-26794823149 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_stateChecks1 :
    compactCertificate453.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (278987865420143 / 4000000000000)) (orderedInterval (94387835725 / 1000000000000) (94387835727 / 1000000000000), orderedInterval (14097536501 / 1000000000000) (14097536503 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (749400649407971 / 4000000000000)) (orderedInterval (-20571249242 / 1000000000000) (-20571248636 / 1000000000000), orderedInterval (54597119537 / 1000000000000) (54597120143 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2034768542330007 / 4000000000000)) (orderedInterval (18166322697 / 1000000000000) (18166322698 / 1000000000000), orderedInterval (30337842467 / 1000000000000) (30337842468 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_stateChecks2 :
    compactCertificate453.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1498801298816591 / 4000000000000)) (orderedInterval (-41131812052 / 1000000000000) (-41131811514 / 1000000000000), orderedInterval (2735002035 / 1000000000000) (2735002573 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2568221571772043 / 4000000000000)) (orderedInterval (29184777910 / 1000000000000) (29184837968 / 1000000000000), orderedInterval (-11845648300 / 1000000000000) (-11845588242 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1891740385867937 / 4000000000000)) (orderedInterval (22502358697 / 1000000000000) (22502362322 / 1000000000000), orderedInterval (-29002194926 / 1000000000000) (-29002191302 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_stateChecks3 :
    compactCertificate453.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2902416234794351 / 4000000000000)) (orderedInterval (-18656871745 / 1000000000000) (-18656871744 / 1000000000000), orderedInterval (-22993369382 / 1000000000000) (-22993369381 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1675710794458679 / 4000000000000)) (orderedInterval (-37122275751 / 1000000000000) (-37122265246 / 1000000000000), orderedInterval (11942926697 / 1000000000000) (11942937201 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (2973578210682211 / 4000000000000)) (orderedInterval (10791351567 / 1000000000000) (10791351582 / 1000000000000), orderedInterval (-27208645980 / 1000000000000) (-27208645965 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_stateChecks4 :
    compactCertificate453.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2778302486839759 / 4000000000000)) (orderedInterval (-26540468468 / 1000000000000) (-26540468466 / 1000000000000), orderedInterval (-14546701859 / 1000000000000) (-14546701857 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1982727750683647 / 4000000000000)) (orderedInterval (3415302943 / 1000000000000) (3415302944 / 1000000000000), orderedInterval (35671021115 / 1000000000000) (35671021116 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2248201948223913 / 4000000000000)) (orderedInterval (-15856169327 / 1000000000000) (-15856169326 / 1000000000000), orderedInterval (-29671847036 / 1000000000000) (-29671847035 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_stateChecks5 :
    compactCertificate453.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1874316397593497 / 4000000000000)) (orderedInterval (-35170719188 / 1000000000000) (-35170719182 / 1000000000000), orderedInterval (-10991405314 / 1000000000000) (-10991405308 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1656015379587437 / 4000000000000)) (orderedInterval (3864533979 / 1000000000000) (3864533980 / 1000000000000), orderedInterval (39018160858 / 1000000000000) (39018160859 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (479977803304263 / 800000000000)) (orderedInterval (-21313096752 / 1000000000000) (-21313096751 / 1000000000000), orderedInterval (-24616238796 / 1000000000000) (-24616238795 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_stateChecks6 :
    compactCertificate453.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1327643863787461 / 4000000000000)) (orderedInterval (-13478317943 / 1000000000000) (-13478317818 / 1000000000000), orderedInterval (41690203420 / 1000000000000) (41690203544 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1125458406585821 / 4000000000000)) (orderedInterval (-26613725349 / 1000000000000) (-26613720333 / 1000000000000), orderedInterval (39472233931 / 1000000000000) (39472238946 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (704259614132063 / 4000000000000)) (orderedInterval (47855483768 / 1000000000000) (47855483769 / 1000000000000), orderedInterval (36273893162 / 1000000000000) (36273893163 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_stateChecks7 :
    compactCertificate453.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (378753162741921 / 4000000000000)) (orderedInterval (77130222308 / 1000000000000) (77130222309 / 1000000000000), orderedInterval (27416774735 / 1000000000000) (27416774736 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1028388514828763 / 4000000000000)) (orderedInterval (13342076366 / 1000000000000) (13342076367 / 1000000000000), orderedInterval (47913357032 / 1000000000000) (47913357033 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1404176597360251 / 4000000000000)) (orderedInterval (-1242706540 / 1000000000000) (-1242706538 / 1000000000000), orderedInterval (42568904711 / 1000000000000) (42568904713 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_stateChecks8 :
    compactCertificate453.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (593740385867937 / 4000000000000)) (orderedInterval (-65488149203 / 1000000000000) (-65488149160 / 1000000000000), orderedInterval (-172245821 / 1000000000000) (-172245778 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2413521705072577 / 4000000000000)) (orderedInterval (26973199488 / 1000000000000) (26973199489 / 1000000000000), orderedInterval (18075573877 / 1000000000000) (18075573878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1612120646584943 / 4000000000000)) (orderedInterval (39455312960 / 1000000000000) (39455314211 / 1000000000000), orderedInterval (-4830213973 / 1000000000000) (-4830212722 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_states : ∀ j,
    BesselStateValid (compactCertificate453.point j) (compactCertificate453.state j) :=
  compactCertificate453.statesValid_of_checks3 compactCertificate453_stateChecks0
    compactCertificate453_stateChecks1 compactCertificate453_stateChecks2
    compactCertificate453_stateChecks3 compactCertificate453_stateChecks4
    compactCertificate453_stateChecks5 compactCertificate453_stateChecks6
    compactCertificate453_stateChecks7 compactCertificate453_stateChecks8

theorem compactCertificate453_chunkChecks0_0 :
    compactCertificate453.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (649 / 2) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43917988293 / 1000000000000) (-43917987418 / 1000000000000), orderedInterval (5817138136 / 1000000000000) (5817139010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (956100925187749 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (44742014945 / 1000000000000) (44742014946 / 1000000000000), orderedInterval (25627003510 / 1000000000000) (25627003511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (309183394872517 / 800000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30449196263 / 1000000000000) (-30449196262 / 1000000000000), orderedInterval (-26794823150 / 1000000000000) (-26794823149 / 1000000000000)))) (orderedInterval (-18777437903 / 1000000000000) (-18777437533 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (278987865420143 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94387835725 / 1000000000000) (94387835727 / 1000000000000), orderedInterval (14097536501 / 1000000000000) (14097536503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (749400649407971 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-20571249242 / 1000000000000) (-20571248636 / 1000000000000), orderedInterval (54597119537 / 1000000000000) (54597120143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2034768542330007 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (18166322697 / 1000000000000) (18166322698 / 1000000000000), orderedInterval (30337842467 / 1000000000000) (30337842468 / 1000000000000)))) (orderedInterval (-3066570702 / 1000000000000) (-3066570641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1498801298816591 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41131812052 / 1000000000000) (-41131811514 / 1000000000000), orderedInterval (2735002035 / 1000000000000) (2735002573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2568221571772043 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29184777910 / 1000000000000) (29184837968 / 1000000000000), orderedInterval (-11845648300 / 1000000000000) (-11845588242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1891740385867937 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22502358697 / 1000000000000) (22502362322 / 1000000000000), orderedInterval (-29002194926 / 1000000000000) (-29002191302 / 1000000000000)))) (orderedInterval (-356339568 / 1000000000000) (-356337609 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_chunkChecks0_1 :
    compactCertificate453.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2902416234794351 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18656871745 / 1000000000000) (-18656871744 / 1000000000000), orderedInterval (-22993369382 / 1000000000000) (-22993369381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1675710794458679 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37122275751 / 1000000000000) (-37122265246 / 1000000000000), orderedInterval (11942926697 / 1000000000000) (11942937201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2973578210682211 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10791351567 / 1000000000000) (10791351582 / 1000000000000), orderedInterval (-27208645980 / 1000000000000) (-27208645965 / 1000000000000)))) (orderedInterval (2098699835 / 1000000000000) (2098700745 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2778302486839759 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26540468468 / 1000000000000) (-26540468466 / 1000000000000), orderedInterval (-14546701859 / 1000000000000) (-14546701857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1982727750683647 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3415302943 / 1000000000000) (3415302944 / 1000000000000), orderedInterval (35671021115 / 1000000000000) (35671021116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2248201948223913 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15856169327 / 1000000000000) (-15856169326 / 1000000000000), orderedInterval (-29671847036 / 1000000000000) (-29671847035 / 1000000000000)))) (orderedInterval (882339525 / 1000000000000) (882339564 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1874316397593497 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35170719188 / 1000000000000) (-35170719182 / 1000000000000), orderedInterval (-10991405314 / 1000000000000) (-10991405308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1656015379587437 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (3864533979 / 1000000000000) (3864533980 / 1000000000000), orderedInterval (39018160858 / 1000000000000) (39018160859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (479977803304263 / 800000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21313096752 / 1000000000000) (-21313096751 / 1000000000000), orderedInterval (-24616238796 / 1000000000000) (-24616238795 / 1000000000000)))) (orderedInterval (-1172993776 / 1000000000000) (-1172993744 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_chunkChecks0_2 :
    compactCertificate453.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1327643863787461 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13478317943 / 1000000000000) (-13478317818 / 1000000000000), orderedInterval (41690203420 / 1000000000000) (41690203544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1125458406585821 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26613725349 / 1000000000000) (-26613720333 / 1000000000000), orderedInterval (39472233931 / 1000000000000) (39472238946 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (704259614132063 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47855483768 / 1000000000000) (47855483769 / 1000000000000), orderedInterval (36273893162 / 1000000000000) (36273893163 / 1000000000000)))) (orderedInterval (5219364752 / 1000000000000) (5219365138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (378753162741921 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77130222308 / 1000000000000) (77130222309 / 1000000000000), orderedInterval (27416774735 / 1000000000000) (27416774736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1028388514828763 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (13342076366 / 1000000000000) (13342076367 / 1000000000000), orderedInterval (47913357032 / 1000000000000) (47913357033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1404176597360251 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1242706540 / 1000000000000) (-1242706538 / 1000000000000), orderedInterval (42568904711 / 1000000000000) (42568904713 / 1000000000000)))) (orderedInterval (-1631668819 / 1000000000000) (-1631668780 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (593740385867937 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65488149203 / 1000000000000) (-65488149160 / 1000000000000), orderedInterval (-172245821 / 1000000000000) (-172245778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2413521705072577 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26973199488 / 1000000000000) (26973199489 / 1000000000000), orderedInterval (18075573877 / 1000000000000) (18075573878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1612120646584943 / 4000000000000) 0 (IntervalRat.scale (649 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39455312960 / 1000000000000) (39455314211 / 1000000000000), orderedInterval (-4830213973 / 1000000000000) (-4830212722 / 1000000000000)))) (orderedInterval (-9993314036 / 1000000000000) (-9993313710 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_chunkChecks0 :
    compactCertificate453.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate453.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate453_chunkChecks0_0
    compactCertificate453_chunkChecks0_1 compactCertificate453_chunkChecks0_2

theorem compactCertificate453_chunkChecks1_0 :
    compactCertificate453.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (649 / 2) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43917988293 / 1000000000000) (-43917987418 / 1000000000000), orderedInterval (5817138136 / 1000000000000) (5817139010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (956100925187749 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (44742014945 / 1000000000000) (44742014946 / 1000000000000), orderedInterval (25627003510 / 1000000000000) (25627003511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (309183394872517 / 800000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30449196263 / 1000000000000) (-30449196262 / 1000000000000), orderedInterval (-26794823150 / 1000000000000) (-26794823149 / 1000000000000)))) (orderedInterval (608935928 / 1000000000000) (608936301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (278987865420143 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94387835725 / 1000000000000) (94387835727 / 1000000000000), orderedInterval (14097536501 / 1000000000000) (14097536503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (749400649407971 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-20571249242 / 1000000000000) (-20571248636 / 1000000000000), orderedInterval (54597119537 / 1000000000000) (54597120143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2034768542330007 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (18166322697 / 1000000000000) (18166322698 / 1000000000000), orderedInterval (30337842467 / 1000000000000) (30337842468 / 1000000000000)))) (orderedInterval (-2262855611 / 1000000000000) (-2262855554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1498801298816591 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41131812052 / 1000000000000) (-41131811514 / 1000000000000), orderedInterval (2735002035 / 1000000000000) (2735002573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2568221571772043 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29184777910 / 1000000000000) (29184837968 / 1000000000000), orderedInterval (-11845648300 / 1000000000000) (-11845588242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1891740385867937 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22502358697 / 1000000000000) (22502362322 / 1000000000000), orderedInterval (-29002194926 / 1000000000000) (-29002191302 / 1000000000000)))) (orderedInterval (-298636814 / 1000000000000) (-298632989 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_chunkChecks1_1 :
    compactCertificate453.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2902416234794351 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18656871745 / 1000000000000) (-18656871744 / 1000000000000), orderedInterval (-22993369382 / 1000000000000) (-22993369381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1675710794458679 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37122275751 / 1000000000000) (-37122265246 / 1000000000000), orderedInterval (11942926697 / 1000000000000) (11942937201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2973578210682211 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10791351567 / 1000000000000) (10791351582 / 1000000000000), orderedInterval (-27208645980 / 1000000000000) (-27208645965 / 1000000000000)))) (orderedInterval (1417271343 / 1000000000000) (1417272620 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2778302486839759 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26540468468 / 1000000000000) (-26540468466 / 1000000000000), orderedInterval (-14546701859 / 1000000000000) (-14546701857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1982727750683647 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3415302943 / 1000000000000) (3415302944 / 1000000000000), orderedInterval (35671021115 / 1000000000000) (35671021116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2248201948223913 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15856169327 / 1000000000000) (-15856169326 / 1000000000000), orderedInterval (-29671847036 / 1000000000000) (-29671847035 / 1000000000000)))) (orderedInterval (5974766091 / 1000000000000) (5974766155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1874316397593497 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35170719188 / 1000000000000) (-35170719182 / 1000000000000), orderedInterval (-10991405314 / 1000000000000) (-10991405308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1656015379587437 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (3864533979 / 1000000000000) (3864533980 / 1000000000000), orderedInterval (39018160858 / 1000000000000) (39018160859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (479977803304263 / 800000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21313096752 / 1000000000000) (-21313096751 / 1000000000000), orderedInterval (-24616238796 / 1000000000000) (-24616238795 / 1000000000000)))) (orderedInterval (-4197354464 / 1000000000000) (-4197354419 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_chunkChecks1_2 :
    compactCertificate453.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1327643863787461 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13478317943 / 1000000000000) (-13478317818 / 1000000000000), orderedInterval (41690203420 / 1000000000000) (41690203544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1125458406585821 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26613725349 / 1000000000000) (-26613720333 / 1000000000000), orderedInterval (39472233931 / 1000000000000) (39472238946 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (704259614132063 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47855483768 / 1000000000000) (47855483769 / 1000000000000), orderedInterval (36273893162 / 1000000000000) (36273893163 / 1000000000000)))) (orderedInterval (-8114605475 / 1000000000000) (-8114605133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (378753162741921 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77130222308 / 1000000000000) (77130222309 / 1000000000000), orderedInterval (27416774735 / 1000000000000) (27416774736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1028388514828763 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (13342076366 / 1000000000000) (13342076367 / 1000000000000), orderedInterval (47913357032 / 1000000000000) (47913357033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1404176597360251 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1242706540 / 1000000000000) (-1242706538 / 1000000000000), orderedInterval (42568904711 / 1000000000000) (42568904713 / 1000000000000)))) (orderedInterval (-4538242815 / 1000000000000) (-4538242779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (593740385867937 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65488149203 / 1000000000000) (-65488149160 / 1000000000000), orderedInterval (-172245821 / 1000000000000) (-172245778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2413521705072577 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26973199488 / 1000000000000) (26973199489 / 1000000000000), orderedInterval (18075573877 / 1000000000000) (18075573878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1612120646584943 / 4000000000000) 1 (IntervalRat.scale (649 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39455312960 / 1000000000000) (39455314211 / 1000000000000), orderedInterval (-4830213973 / 1000000000000) (-4830212722 / 1000000000000)))) (orderedInterval (-1610791297 / 1000000000000) (-1610790878 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_chunkChecks1 :
    compactCertificate453.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate453.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate453_chunkChecks1_0
    compactCertificate453_chunkChecks1_1 compactCertificate453_chunkChecks1_2

theorem compactCertificate453_chunkChecks2_0 :
    compactCertificate453.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (649 / 2) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43917988293 / 1000000000000) (-43917987418 / 1000000000000), orderedInterval (5817138136 / 1000000000000) (5817139010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (956100925187749 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (44742014945 / 1000000000000) (44742014946 / 1000000000000), orderedInterval (25627003510 / 1000000000000) (25627003511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (309183394872517 / 800000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30449196263 / 1000000000000) (-30449196262 / 1000000000000), orderedInterval (-26794823150 / 1000000000000) (-26794823149 / 1000000000000)))) (orderedInterval (19714002158 / 1000000000000) (19714002536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (278987865420143 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94387835725 / 1000000000000) (94387835727 / 1000000000000), orderedInterval (14097536501 / 1000000000000) (14097536503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (749400649407971 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-20571249242 / 1000000000000) (-20571248636 / 1000000000000), orderedInterval (54597119537 / 1000000000000) (54597120143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2034768542330007 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (18166322697 / 1000000000000) (18166322698 / 1000000000000), orderedInterval (30337842467 / 1000000000000) (30337842468 / 1000000000000)))) (orderedInterval (3478259012 / 1000000000000) (3478259081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1498801298816591 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41131812052 / 1000000000000) (-41131811514 / 1000000000000), orderedInterval (2735002035 / 1000000000000) (2735002573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2568221571772043 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29184777910 / 1000000000000) (29184837968 / 1000000000000), orderedInterval (-11845648300 / 1000000000000) (-11845588242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1891740385867937 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22502358697 / 1000000000000) (22502362322 / 1000000000000), orderedInterval (-29002194926 / 1000000000000) (-29002191302 / 1000000000000)))) (orderedInterval (2369813127 / 1000000000000) (2369820634 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_chunkChecks2_1 :
    compactCertificate453.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2902416234794351 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18656871745 / 1000000000000) (-18656871744 / 1000000000000), orderedInterval (-22993369382 / 1000000000000) (-22993369381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1675710794458679 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37122275751 / 1000000000000) (-37122265246 / 1000000000000), orderedInterval (11942926697 / 1000000000000) (11942937201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2973578210682211 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10791351567 / 1000000000000) (10791351582 / 1000000000000), orderedInterval (-27208645980 / 1000000000000) (-27208645965 / 1000000000000)))) (orderedInterval (-20046785652 / 1000000000000) (-20046783768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2778302486839759 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26540468468 / 1000000000000) (-26540468466 / 1000000000000), orderedInterval (-14546701859 / 1000000000000) (-14546701857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1982727750683647 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3415302943 / 1000000000000) (3415302944 / 1000000000000), orderedInterval (35671021115 / 1000000000000) (35671021116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2248201948223913 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15856169327 / 1000000000000) (-15856169326 / 1000000000000), orderedInterval (-29671847036 / 1000000000000) (-29671847035 / 1000000000000)))) (orderedInterval (-3207889424 / 1000000000000) (-3207889319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1874316397593497 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35170719188 / 1000000000000) (-35170719182 / 1000000000000), orderedInterval (-10991405314 / 1000000000000) (-10991405308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1656015379587437 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (3864533979 / 1000000000000) (3864533980 / 1000000000000), orderedInterval (39018160858 / 1000000000000) (39018160859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (479977803304263 / 800000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21313096752 / 1000000000000) (-21313096751 / 1000000000000), orderedInterval (-24616238796 / 1000000000000) (-24616238795 / 1000000000000)))) (orderedInterval (3085235047 / 1000000000000) (3085235115 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_chunkChecks2_2 :
    compactCertificate453.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1327643863787461 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13478317943 / 1000000000000) (-13478317818 / 1000000000000), orderedInterval (41690203420 / 1000000000000) (41690203544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1125458406585821 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26613725349 / 1000000000000) (-26613720333 / 1000000000000), orderedInterval (39472233931 / 1000000000000) (39472238946 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (704259614132063 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47855483768 / 1000000000000) (47855483769 / 1000000000000), orderedInterval (36273893162 / 1000000000000) (36273893163 / 1000000000000)))) (orderedInterval (-3820753767 / 1000000000000) (-3820753460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (378753162741921 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77130222308 / 1000000000000) (77130222309 / 1000000000000), orderedInterval (27416774735 / 1000000000000) (27416774736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1028388514828763 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (13342076366 / 1000000000000) (13342076367 / 1000000000000), orderedInterval (47913357032 / 1000000000000) (47913357033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1404176597360251 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1242706540 / 1000000000000) (-1242706538 / 1000000000000), orderedInterval (42568904711 / 1000000000000) (42568904713 / 1000000000000)))) (orderedInterval (213797470 / 1000000000000) (213797505 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (593740385867937 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65488149203 / 1000000000000) (-65488149160 / 1000000000000), orderedInterval (-172245821 / 1000000000000) (-172245778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2413521705072577 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26973199488 / 1000000000000) (26973199489 / 1000000000000), orderedInterval (18075573877 / 1000000000000) (18075573878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1612120646584943 / 4000000000000) 2 (IntervalRat.scale (649 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39455312960 / 1000000000000) (39455314211 / 1000000000000), orderedInterval (-4830213973 / 1000000000000) (-4830212722 / 1000000000000)))) (orderedInterval (19098381005 / 1000000000000) (19098381555 / 1000000000000))) = true
  rfl'

theorem compactCertificate453_chunkChecks2 :
    compactCertificate453.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate453.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate453_chunkChecks2_0
    compactCertificate453_chunkChecks2_1 compactCertificate453_chunkChecks2_2

theorem compactCertificate453_chunkChecks3_0 :
    compactCertificate453.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (649 / 2) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43917988293 / 1000000000000) (-43917987418 / 1000000000000), orderedInterval (5817138136 / 1000000000000) (5817139010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (956100925187749 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (44742014945 / 1000000000000) (44742014946 / 1000000000000), orderedInterval (25627003510 / 1000000000000) (25627003511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (309183394872517 / 800000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30449196263 / 1000000000000) (-30449196262 / 1000000000000), orderedInterval (-26794823150 / 1000000000000) (-26794823149 / 1000000000000)))) (orderedInterval (194449150 / 1000000000000) (194449532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (278987865420143 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94387835725 / 1000000000000) (94387835727 / 1000000000000), orderedInterval (14097536501 / 1000000000000) (14097536503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (749400649407971 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-20571249242 / 1000000000000) (-20571248636 / 1000000000000), orderedInterval (54597119537 / 1000000000000) (54597120143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2034768542330007 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (18166322697 / 1000000000000) (18166322698 / 1000000000000), orderedInterval (30337842467 / 1000000000000) (30337842468 / 1000000000000)))) (orderedInterval (7915437748 / 1000000000000) (7915437845 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1498801298816591 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41131812052 / 1000000000000) (-41131811514 / 1000000000000), orderedInterval (2735002035 / 1000000000000) (2735002573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2568221571772043 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29184777910 / 1000000000000) (29184837968 / 1000000000000), orderedInterval (-11845648300 / 1000000000000) (-11845588242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1891740385867937 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22502358697 / 1000000000000) (22502362322 / 1000000000000), orderedInterval (-29002194926 / 1000000000000) (-29002191302 / 1000000000000)))) (orderedInterval (-667549265 / 1000000000000) (-667534519 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate453_chunkChecks3_1 :
    compactCertificate453.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2902416234794351 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18656871745 / 1000000000000) (-18656871744 / 1000000000000), orderedInterval (-22993369382 / 1000000000000) (-22993369381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1675710794458679 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37122275751 / 1000000000000) (-37122265246 / 1000000000000), orderedInterval (11942926697 / 1000000000000) (11942937201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2973578210682211 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10791351567 / 1000000000000) (10791351582 / 1000000000000), orderedInterval (-27208645980 / 1000000000000) (-27208645965 / 1000000000000)))) (orderedInterval (-1017525330 / 1000000000000) (-1017522371 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2778302486839759 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26540468468 / 1000000000000) (-26540468466 / 1000000000000), orderedInterval (-14546701859 / 1000000000000) (-14546701857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1982727750683647 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3415302943 / 1000000000000) (3415302944 / 1000000000000), orderedInterval (35671021115 / 1000000000000) (35671021116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2248201948223913 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15856169327 / 1000000000000) (-15856169326 / 1000000000000), orderedInterval (-29671847036 / 1000000000000) (-29671847035 / 1000000000000)))) (orderedInterval (-15368291899 / 1000000000000) (-15368291722 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1874316397593497 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35170719188 / 1000000000000) (-35170719182 / 1000000000000), orderedInterval (-10991405314 / 1000000000000) (-10991405308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1656015379587437 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (3864533979 / 1000000000000) (3864533980 / 1000000000000), orderedInterval (39018160858 / 1000000000000) (39018160859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (479977803304263 / 800000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21313096752 / 1000000000000) (-21313096751 / 1000000000000), orderedInterval (-24616238796 / 1000000000000) (-24616238795 / 1000000000000)))) (orderedInterval (8993210657 / 1000000000000) (8993210761 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate453_chunkChecks3_2 :
    compactCertificate453.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1327643863787461 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13478317943 / 1000000000000) (-13478317818 / 1000000000000), orderedInterval (41690203420 / 1000000000000) (41690203544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1125458406585821 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26613725349 / 1000000000000) (-26613720333 / 1000000000000), orderedInterval (39472233931 / 1000000000000) (39472238946 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (704259614132063 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47855483768 / 1000000000000) (47855483769 / 1000000000000), orderedInterval (36273893162 / 1000000000000) (36273893163 / 1000000000000)))) (orderedInterval (8412618707 / 1000000000000) (8412618984 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (378753162741921 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77130222308 / 1000000000000) (77130222309 / 1000000000000), orderedInterval (27416774735 / 1000000000000) (27416774736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1028388514828763 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (13342076366 / 1000000000000) (13342076367 / 1000000000000), orderedInterval (47913357032 / 1000000000000) (47913357033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1404176597360251 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1242706540 / 1000000000000) (-1242706538 / 1000000000000), orderedInterval (42568904711 / 1000000000000) (42568904713 / 1000000000000)))) (orderedInterval (4682789596 / 1000000000000) (4682789632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (593740385867937 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65488149203 / 1000000000000) (-65488149160 / 1000000000000), orderedInterval (-172245821 / 1000000000000) (-172245778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2413521705072577 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26973199488 / 1000000000000) (26973199489 / 1000000000000), orderedInterval (18075573877 / 1000000000000) (18075573878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1612120646584943 / 4000000000000) 3 (IntervalRat.scale (649 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39455312960 / 1000000000000) (39455314211 / 1000000000000), orderedInterval (-4830213973 / 1000000000000) (-4830212722 / 1000000000000)))) (orderedInterval (7664136025 / 1000000000000) (7664136764 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate453_chunkChecks3 :
    compactCertificate453.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate453.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate453_chunkChecks3_0
    compactCertificate453_chunkChecks3_1 compactCertificate453_chunkChecks3_2

theorem compactCertificate453_chunkChecks4_0 :
    compactCertificate453.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (649 / 2) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-43917988293 / 1000000000000) (-43917987418 / 1000000000000), orderedInterval (5817138136 / 1000000000000) (5817139010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (956100925187749 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (44742014945 / 1000000000000) (44742014946 / 1000000000000), orderedInterval (25627003510 / 1000000000000) (25627003511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (309183394872517 / 800000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30449196263 / 1000000000000) (-30449196262 / 1000000000000), orderedInterval (-26794823150 / 1000000000000) (-26794823149 / 1000000000000)))) (orderedInterval (-20881009503 / 1000000000000) (-20881009114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (278987865420143 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94387835725 / 1000000000000) (94387835727 / 1000000000000), orderedInterval (14097536501 / 1000000000000) (14097536503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (749400649407971 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-20571249242 / 1000000000000) (-20571248636 / 1000000000000), orderedInterval (54597119537 / 1000000000000) (54597120143 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2034768542330007 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (18166322697 / 1000000000000) (18166322698 / 1000000000000), orderedInterval (30337842467 / 1000000000000) (30337842468 / 1000000000000)))) (orderedInterval (-7933315694 / 1000000000000) (-7933315549 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1498801298816591 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41131812052 / 1000000000000) (-41131811514 / 1000000000000), orderedInterval (2735002035 / 1000000000000) (2735002573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2568221571772043 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29184777910 / 1000000000000) (29184837968 / 1000000000000), orderedInterval (-11845648300 / 1000000000000) (-11845588242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1891740385867937 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22502358697 / 1000000000000) (22502362322 / 1000000000000), orderedInterval (-29002194926 / 1000000000000) (-29002191302 / 1000000000000)))) (orderedInterval (-11338381269 / 1000000000000) (-11338352203 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate453_chunkChecks4_1 :
    compactCertificate453.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2902416234794351 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-18656871745 / 1000000000000) (-18656871744 / 1000000000000), orderedInterval (-22993369382 / 1000000000000) (-22993369381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1675710794458679 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37122275751 / 1000000000000) (-37122265246 / 1000000000000), orderedInterval (11942926697 / 1000000000000) (11942937201 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2973578210682211 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10791351567 / 1000000000000) (10791351582 / 1000000000000), orderedInterval (-27208645980 / 1000000000000) (-27208645965 / 1000000000000)))) (orderedInterval (117496627422 / 1000000000000) (117496632438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2778302486839759 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26540468468 / 1000000000000) (-26540468466 / 1000000000000), orderedInterval (-14546701859 / 1000000000000) (-14546701857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1982727750683647 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (3415302943 / 1000000000000) (3415302944 / 1000000000000), orderedInterval (35671021115 / 1000000000000) (35671021116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2248201948223913 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15856169327 / 1000000000000) (-15856169326 / 1000000000000), orderedInterval (-29671847036 / 1000000000000) (-29671847035 / 1000000000000)))) (orderedInterval (12632456522 / 1000000000000) (12632456830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1874316397593497 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35170719188 / 1000000000000) (-35170719182 / 1000000000000), orderedInterval (-10991405314 / 1000000000000) (-10991405308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1656015379587437 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (3864533979 / 1000000000000) (3864533980 / 1000000000000), orderedInterval (39018160858 / 1000000000000) (39018160859 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (479977803304263 / 800000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21313096752 / 1000000000000) (-21313096751 / 1000000000000), orderedInterval (-24616238796 / 1000000000000) (-24616238795 / 1000000000000)))) (orderedInterval (-8784212300 / 1000000000000) (-8784212135 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate453_chunkChecks4_2 :
    compactCertificate453.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1327643863787461 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-13478317943 / 1000000000000) (-13478317818 / 1000000000000), orderedInterval (41690203420 / 1000000000000) (41690203544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1125458406585821 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26613725349 / 1000000000000) (-26613720333 / 1000000000000), orderedInterval (39472233931 / 1000000000000) (39472238946 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (704259614132063 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47855483768 / 1000000000000) (47855483769 / 1000000000000), orderedInterval (36273893162 / 1000000000000) (36273893163 / 1000000000000)))) (orderedInterval (3293344680 / 1000000000000) (3293344933 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (378753162741921 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (77130222308 / 1000000000000) (77130222309 / 1000000000000), orderedInterval (27416774735 / 1000000000000) (27416774736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1028388514828763 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (13342076366 / 1000000000000) (13342076367 / 1000000000000), orderedInterval (47913357032 / 1000000000000) (47913357033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1404176597360251 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1242706540 / 1000000000000) (-1242706538 / 1000000000000), orderedInterval (42568904711 / 1000000000000) (42568904713 / 1000000000000)))) (orderedInterval (-28015325 / 1000000000000) (-28015286 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (593740385867937 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65488149203 / 1000000000000) (-65488149160 / 1000000000000), orderedInterval (-172245821 / 1000000000000) (-172245778 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2413521705072577 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (26973199488 / 1000000000000) (26973199489 / 1000000000000), orderedInterval (18075573877 / 1000000000000) (18075573878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1612120646584943 / 4000000000000) 4 (IntervalRat.scale (649 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39455312960 / 1000000000000) (39455314211 / 1000000000000), orderedInterval (-4830213973 / 1000000000000) (-4830212722 / 1000000000000)))) (orderedInterval (-43926245330 / 1000000000000) (-43926244305 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate453_chunkChecks4 :
    compactCertificate453.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate453.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate453_chunkChecks4_0
    compactCertificate453_chunkChecks4_1 compactCertificate453_chunkChecks4_2

theorem compactCertificate453_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate453.chunkCheck r b = true :=
  compactCertificate453.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate453_chunkChecks0
    · exact compactCertificate453_chunkChecks1
    · exact compactCertificate453_chunkChecks2
    · exact compactCertificate453_chunkChecks3
    · exact compactCertificate453_chunkChecks4)

theorem compactCertificate453_coefficient0 :
    compactCertificate453.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate453_coefficient1 :
    compactCertificate453.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate453_coefficient2 :
    compactCertificate453.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate453_coefficient3 :
    compactCertificate453.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate453_coefficient4 :
    compactCertificate453.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate453_coefficients : ∀ r : Fin 5,
    compactCertificate453.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate453_coefficient0
  · exact compactCertificate453_coefficient1
  · exact compactCertificate453_coefficient2
  · exact compactCertificate453_coefficient3
  · exact compactCertificate453_coefficient4

theorem compactCertificate453_lower : (1 : ℚ) ≤ compactCertificate453.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate453, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate453_proves {t : ℝ} (ht : t ∈ compactCertificate453.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate453.proves compactCertificate453_states compactCertificate453_chunks
    compactCertificate453_coefficients compactCertificate453_lower ht

end Erdos232
