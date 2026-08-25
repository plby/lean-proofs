/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate516 : CompactCertificate where
  left := 387
  right := 388
  center := 775 / 2
  grid := fun i =>
    match i.val with
    | 0 => 123
    | 1 => 91
    | 2 => 147
    | 3 => 27
    | 4 => 71
    | 5 => 193
    | 6 => 142
    | 7 => 244
    | 8 => 180
    | 9 => 276
    | 10 => 159
    | 11 => 283
    | 12 => 264
    | 13 => 189
    | 14 => 214
    | 15 => 178
    | 16 => 157
    | 17 => 228
    | 18 => 126
    | 19 => 107
    | 20 => 67
    | 21 => 36
    | 22 => 98
    | 23 => 134
    | 24 => 56
    | 25 => 229
    | _ => 153
  point := fun i =>
    match i.val with
    | 0 => 775 / 2
    | 1 => 45668919384931 / 160000000000
    | 2 => 14768390201923 / 32000000000
    | 3 => 13326076776617 / 160000000000
    | 4 => 35795716689749 / 160000000000
    | 5 => 97192334071233 / 160000000000
    | 6 => 71591433379529 / 160000000000
    | 7 => 122673141332717 / 160000000000
    | 8 => 90360480680903 / 160000000000
    | 9 => 138636214604969 / 160000000000
    | 10 => 80041655821601 / 160000000000
    | 11 => 142035322852309 / 160000000000
    | 12 => 132707822946121 / 160000000000
    | 13 => 94706564362393 / 160000000000
    | 14 => 107387150069247 / 160000000000
    | 15 => 89528210054543 / 160000000000
    | 16 => 79100888701403 / 160000000000
    | 17 => 22926520650897 / 32000000000
    | 18 => 63415962677059 / 160000000000
    | 19 => 53758413873899 / 160000000000
    | 20 => 33639519319097 / 160000000000
    | 21 => 18091445369799 / 160000000000
    | 22 => 49121793466397 / 160000000000
    | 23 => 67071609427069 / 160000000000
    | 24 => 28360480680903 / 160000000000
    | 25 => 115283779441063 / 160000000000
    | _ => 77004221947817 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-38741556503 / 1000000000000) (-38741548550 / 1000000000000), orderedInterval (11965550480 / 1000000000000) (11965558433 / 1000000000000))
    | 1 => (orderedInterval (-15338161982 / 1000000000000) (-15338161981 / 1000000000000), orderedInterval (-44639966047 / 1000000000000) (-44639966046 / 1000000000000))
    | 2 => (orderedInterval (-17256098683 / 1000000000000) (-17256098682 / 1000000000000), orderedInterval (-32869735431 / 1000000000000) (-32869735430 / 1000000000000))
    | 3 => (orderedInterval (59665404881 / 1000000000000) (59665463202 / 1000000000000), orderedInterval (-64261585653 / 1000000000000) (-64261527331 / 1000000000000))
    | 4 => (orderedInterval (-52986505693 / 1000000000000) (-52986505679 / 1000000000000), orderedInterval (-6045328971 / 1000000000000) (-6045328957 / 1000000000000))
    | 5 => (orderedInterval (-30529569543 / 1000000000000) (-30529535316 / 1000000000000), orderedInterval (10793703123 / 1000000000000) (10793737350 / 1000000000000))
    | 6 => (orderedInterval (32065484125 / 1000000000000) (32065593949 / 1000000000000), orderedInterval (-19900047834 / 1000000000000) (-19899938009 / 1000000000000))
    | 7 => (orderedInterval (23333895583 / 1000000000000) (23333895584 / 1000000000000), orderedInterval (16892149821 / 1000000000000) (16892149822 / 1000000000000))
    | 8 => (orderedInterval (1728442351 / 1000000000000) (1728442352 / 1000000000000), orderedInterval (33528551400 / 1000000000000) (33528551401 / 1000000000000))
    | 9 => (orderedInterval (4906667070 / 1000000000000) (4906667071 / 1000000000000), orderedInterval (26655138487 / 1000000000000) (26655138488 / 1000000000000))
    | 10 => (orderedInterval (-35646709601 / 1000000000000) (-35646709277 / 1000000000000), orderedInterval (-1338558660 / 1000000000000) (-1338558336 / 1000000000000))
    | 11 => (orderedInterval (14331265828 / 1000000000000) (14331265909 / 1000000000000), orderedInterval (-22630064164 / 1000000000000) (-22630064083 / 1000000000000))
    | 12 => (orderedInterval (20419395173 / 1000000000000) (20419395174 / 1000000000000), orderedInterval (18711814593 / 1000000000000) (18711814594 / 1000000000000))
    | 13 => (orderedInterval (28605751863 / 1000000000000) (28605842869 / 1000000000000), orderedInterval (-16062658519 / 1000000000000) (-16062567513 / 1000000000000))
    | 14 => (orderedInterval (-10442705361 / 1000000000000) (-10442705345 / 1000000000000), orderedInterval (28981438859 / 1000000000000) (28981438875 / 1000000000000))
    | 15 => (orderedInterval (30549050349 / 1000000000000) (30549050351 / 1000000000000), orderedInterval (14272626547 / 1000000000000) (14272626549 / 1000000000000))
    | 16 => (orderedInterval (-33522593135 / 1000000000000) (-33522567509 / 1000000000000), orderedInterval (12838112183 / 1000000000000) (12838137808 / 1000000000000))
    | 17 => (orderedInterval (24348366512 / 1000000000000) (24348366513 / 1000000000000), orderedInterval (17179739913 / 1000000000000) (17179739914 / 1000000000000))
    | 18 => (orderedInterval (38553898874 / 1000000000000) (38553898878 / 1000000000000), orderedInterval (10896810437 / 1000000000000) (10896810442 / 1000000000000))
    | 19 => (orderedInterval (-25457946211 / 1000000000000) (-25457946210 / 1000000000000), orderedInterval (-35270063849 / 1000000000000) (-35270063848 / 1000000000000))
    | 20 => (orderedInterval (-28531217076 / 1000000000000) (-28531217075 / 1000000000000), orderedInterval (-46984618776 / 1000000000000) (-46984618775 / 1000000000000))
    | 21 => (orderedInterval (51610768636 / 1000000000000) (51610768637 / 1000000000000), orderedInterval (54238016720 / 1000000000000) (54238016721 / 1000000000000))
    | 22 => (orderedInterval (-3633607931 / 1000000000000) (-3633607926 / 1000000000000), orderedInterval (45397590249 / 1000000000000) (45397590253 / 1000000000000))
    | 23 => (orderedInterval (-32596163806 / 1000000000000) (-32596057587 / 1000000000000), orderedInterval (21396631551 / 1000000000000) (21396737770 / 1000000000000))
    | 24 => (orderedInterval (51472597755 / 1000000000000) (51472626505 / 1000000000000), orderedInterval (-30839692769 / 1000000000000) (-30839664020 / 1000000000000))
    | 25 => (orderedInterval (-28277376136 / 1000000000000) (-28277330707 / 1000000000000), orderedInterval (9181621434 / 1000000000000) (9181666863 / 1000000000000))
    | _ => (orderedInterval (-35827378483 / 1000000000000) (-35827378440 / 1000000000000), orderedInterval (-6221535349 / 1000000000000) (-6221535305 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-16511326242 / 1000000000000) (-16511323062 / 1000000000000)
      | 1 => orderedInterval (-411624128 / 1000000000000) (-411621015 / 1000000000000)
      | 2 => orderedInterval (-677937668 / 1000000000000) (-677937646 / 1000000000000)
      | 3 => orderedInterval (-1475709540 / 1000000000000) (-1475709350 / 1000000000000)
      | 4 => orderedInterval (2389254864 / 1000000000000) (2389263516 / 1000000000000)
      | 5 => orderedInterval (2894569835 / 1000000000000) (2894571339 / 1000000000000)
      | 6 => orderedInterval (-5652399958 / 1000000000000) (-5652399859 / 1000000000000)
      | 7 => orderedInterval (1627561277 / 1000000000000) (1627569464 / 1000000000000)
      | _ => orderedInterval (9334285205 / 1000000000000) (9334289192 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (2139093394 / 1000000000000) (2139096577 / 1000000000000)
      | 1 => orderedInterval (-1180453232 / 1000000000000) (-1180449228 / 1000000000000)
      | 2 => orderedInterval (150088144 / 1000000000000) (150088183 / 1000000000000)
      | 3 => orderedInterval (-18088510064 / 1000000000000) (-18088509688 / 1000000000000)
      | 4 => orderedInterval (-3297289309 / 1000000000000) (-3297276088 / 1000000000000)
      | 5 => orderedInterval (113949023 / 1000000000000) (113950948 / 1000000000000)
      | 6 => orderedInterval (-881106381 / 1000000000000) (-881106290 / 1000000000000)
      | 7 => orderedInterval (-2882197247 / 1000000000000) (-2882188398 / 1000000000000)
      | _ => orderedInterval (-24954061 / 1000000000000) (-24946944 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (16864181563 / 1000000000000) (16864184759 / 1000000000000)
      | 1 => orderedInterval (-4655614869 / 1000000000000) (-4655608776 / 1000000000000)
      | 2 => orderedInterval (2728445247 / 1000000000000) (2728445315 / 1000000000000)
      | 3 => orderedInterval (-1884158595 / 1000000000000) (-1884157811 / 1000000000000)
      | 4 => orderedInterval (-4772913510 / 1000000000000) (-4772893271 / 1000000000000)
      | 5 => orderedInterval (-5989594401 / 1000000000000) (-5989591928 / 1000000000000)
      | 6 => orderedInterval (5641672817 / 1000000000000) (5641672904 / 1000000000000)
      | 7 => orderedInterval (-2886708544 / 1000000000000) (-2886698953 / 1000000000000)
      | _ => orderedInterval (-18392698283 / 1000000000000) (-18392685208 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-1361408490 / 1000000000000) (-1361405289 / 1000000000000)
      | 1 => orderedInterval (3003516939 / 1000000000000) (3003526444 / 1000000000000)
      | 2 => orderedInterval (1520240177 / 1000000000000) (1520240300 / 1000000000000)
      | 3 => orderedInterval (91849595130 / 1000000000000) (91849596818 / 1000000000000)
      | 4 => orderedInterval (9500857416 / 1000000000000) (9500888352 / 1000000000000)
      | 5 => orderedInterval (-1735276770 / 1000000000000) (-1735273595 / 1000000000000)
      | 6 => orderedInterval (792861450 / 1000000000000) (792861534 / 1000000000000)
      | 7 => orderedInterval (2620570685 / 1000000000000) (2620581059 / 1000000000000)
      | _ => orderedInterval (2633685617 / 1000000000000) (2633709799 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-17428182460 / 1000000000000) (-17428179244 / 1000000000000)
      | 1 => orderedInterval (12874658806 / 1000000000000) (12874673718 / 1000000000000)
      | 2 => orderedInterval (-10849704094 / 1000000000000) (-10849703867 / 1000000000000)
      | 3 => orderedInterval (26506667162 / 1000000000000) (26506670871 / 1000000000000)
      | 4 => orderedInterval (7416264736 / 1000000000000) (7416312114 / 1000000000000)
      | 5 => orderedInterval (13910622915 / 1000000000000) (13910627011 / 1000000000000)
      | 6 => orderedInterval (-6017315704 / 1000000000000) (-6017315620 / 1000000000000)
      | 7 => orderedInterval (3433416106 / 1000000000000) (3433427353 / 1000000000000)
      | _ => orderedInterval (43511033950 / 1000000000000) (43511078856 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-8483326355 / 1000000000000) (-8483297421 / 1000000000000)
    | 1 => orderedInterval (-23951379733 / 1000000000000) (-23951340928 / 1000000000000)
    | 2 => orderedInterval (-13347388575 / 1000000000000) (-13347332969 / 1000000000000)
    | 3 => orderedInterval (108824642154 / 1000000000000) (108824725422 / 1000000000000)
    | _ => orderedInterval (73357461417 / 1000000000000) (73357591192 / 1000000000000)

theorem compactCertificate516_stateChecks0 :
    compactCertificate516.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (775 / 2)) (orderedInterval (-38741556503 / 1000000000000) (-38741548550 / 1000000000000), orderedInterval (11965550480 / 1000000000000) (11965558433 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (45668919384931 / 160000000000)) (orderedInterval (-15338161982 / 1000000000000) (-15338161981 / 1000000000000), orderedInterval (-44639966047 / 1000000000000) (-44639966046 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (14768390201923 / 32000000000)) (orderedInterval (-17256098683 / 1000000000000) (-17256098682 / 1000000000000), orderedInterval (-32869735431 / 1000000000000) (-32869735430 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_stateChecks1 :
    compactCertificate516.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (13326076776617 / 160000000000)) (orderedInterval (59665404881 / 1000000000000) (59665463202 / 1000000000000), orderedInterval (-64261585653 / 1000000000000) (-64261527331 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (35795716689749 / 160000000000)) (orderedInterval (-52986505693 / 1000000000000) (-52986505679 / 1000000000000), orderedInterval (-6045328971 / 1000000000000) (-6045328957 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (97192334071233 / 160000000000)) (orderedInterval (-30529569543 / 1000000000000) (-30529535316 / 1000000000000), orderedInterval (10793703123 / 1000000000000) (10793737350 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_stateChecks2 :
    compactCertificate516.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (71591433379529 / 160000000000)) (orderedInterval (32065484125 / 1000000000000) (32065593949 / 1000000000000), orderedInterval (-19900047834 / 1000000000000) (-19899938009 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (122673141332717 / 160000000000)) (orderedInterval (23333895583 / 1000000000000) (23333895584 / 1000000000000), orderedInterval (16892149821 / 1000000000000) (16892149822 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (90360480680903 / 160000000000)) (orderedInterval (1728442351 / 1000000000000) (1728442352 / 1000000000000), orderedInterval (33528551400 / 1000000000000) (33528551401 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_stateChecks3 :
    compactCertificate516.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 276 12 (138636214604969 / 160000000000)) (orderedInterval (4906667070 / 1000000000000) (4906667071 / 1000000000000), orderedInterval (26655138487 / 1000000000000) (26655138488 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (80041655821601 / 160000000000)) (orderedInterval (-35646709601 / 1000000000000) (-35646709277 / 1000000000000), orderedInterval (-1338558660 / 1000000000000) (-1338558336 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 283 12 (142035322852309 / 160000000000)) (orderedInterval (14331265828 / 1000000000000) (14331265909 / 1000000000000), orderedInterval (-22630064164 / 1000000000000) (-22630064083 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_stateChecks4 :
    compactCertificate516.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 264 12 (132707822946121 / 160000000000)) (orderedInterval (20419395173 / 1000000000000) (20419395174 / 1000000000000), orderedInterval (18711814593 / 1000000000000) (18711814594 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (94706564362393 / 160000000000)) (orderedInterval (28605751863 / 1000000000000) (28605842869 / 1000000000000), orderedInterval (-16062658519 / 1000000000000) (-16062567513 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (107387150069247 / 160000000000)) (orderedInterval (-10442705361 / 1000000000000) (-10442705345 / 1000000000000), orderedInterval (28981438859 / 1000000000000) (28981438875 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_stateChecks5 :
    compactCertificate516.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (89528210054543 / 160000000000)) (orderedInterval (30549050349 / 1000000000000) (30549050351 / 1000000000000), orderedInterval (14272626547 / 1000000000000) (14272626549 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (79100888701403 / 160000000000)) (orderedInterval (-33522593135 / 1000000000000) (-33522567509 / 1000000000000), orderedInterval (12838112183 / 1000000000000) (12838137808 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (22926520650897 / 32000000000)) (orderedInterval (24348366512 / 1000000000000) (24348366513 / 1000000000000), orderedInterval (17179739913 / 1000000000000) (17179739914 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_stateChecks6 :
    compactCertificate516.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (63415962677059 / 160000000000)) (orderedInterval (38553898874 / 1000000000000) (38553898878 / 1000000000000), orderedInterval (10896810437 / 1000000000000) (10896810442 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (53758413873899 / 160000000000)) (orderedInterval (-25457946211 / 1000000000000) (-25457946210 / 1000000000000), orderedInterval (-35270063849 / 1000000000000) (-35270063848 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (33639519319097 / 160000000000)) (orderedInterval (-28531217076 / 1000000000000) (-28531217075 / 1000000000000), orderedInterval (-46984618776 / 1000000000000) (-46984618775 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_stateChecks7 :
    compactCertificate516.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (18091445369799 / 160000000000)) (orderedInterval (51610768636 / 1000000000000) (51610768637 / 1000000000000), orderedInterval (54238016720 / 1000000000000) (54238016721 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (49121793466397 / 160000000000)) (orderedInterval (-3633607931 / 1000000000000) (-3633607926 / 1000000000000), orderedInterval (45397590249 / 1000000000000) (45397590253 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (67071609427069 / 160000000000)) (orderedInterval (-32596163806 / 1000000000000) (-32596057587 / 1000000000000), orderedInterval (21396631551 / 1000000000000) (21396737770 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_stateChecks8 :
    compactCertificate516.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (28360480680903 / 160000000000)) (orderedInterval (51472597755 / 1000000000000) (51472626505 / 1000000000000), orderedInterval (-30839692769 / 1000000000000) (-30839664020 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (115283779441063 / 160000000000)) (orderedInterval (-28277376136 / 1000000000000) (-28277330707 / 1000000000000), orderedInterval (9181621434 / 1000000000000) (9181666863 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (77004221947817 / 160000000000)) (orderedInterval (-35827378483 / 1000000000000) (-35827378440 / 1000000000000), orderedInterval (-6221535349 / 1000000000000) (-6221535305 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_states : ∀ j,
    BesselStateValid (compactCertificate516.point j) (compactCertificate516.state j) :=
  compactCertificate516.statesValid_of_checks3 compactCertificate516_stateChecks0
    compactCertificate516_stateChecks1 compactCertificate516_stateChecks2
    compactCertificate516_stateChecks3 compactCertificate516_stateChecks4
    compactCertificate516_stateChecks5 compactCertificate516_stateChecks6
    compactCertificate516_stateChecks7 compactCertificate516_stateChecks8

theorem compactCertificate516_chunkChecks0_0 :
    compactCertificate516.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (775 / 2) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38741556503 / 1000000000000) (-38741548550 / 1000000000000), orderedInterval (11965550480 / 1000000000000) (11965558433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (45668919384931 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15338161982 / 1000000000000) (-15338161981 / 1000000000000), orderedInterval (-44639966047 / 1000000000000) (-44639966046 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (14768390201923 / 32000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17256098683 / 1000000000000) (-17256098682 / 1000000000000), orderedInterval (-32869735431 / 1000000000000) (-32869735430 / 1000000000000)))) (orderedInterval (-16511326242 / 1000000000000) (-16511323062 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (13326076776617 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (59665404881 / 1000000000000) (59665463202 / 1000000000000), orderedInterval (-64261585653 / 1000000000000) (-64261527331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (35795716689749 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52986505693 / 1000000000000) (-52986505679 / 1000000000000), orderedInterval (-6045328971 / 1000000000000) (-6045328957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (97192334071233 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30529569543 / 1000000000000) (-30529535316 / 1000000000000), orderedInterval (10793703123 / 1000000000000) (10793737350 / 1000000000000)))) (orderedInterval (-411624128 / 1000000000000) (-411621015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (71591433379529 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32065484125 / 1000000000000) (32065593949 / 1000000000000), orderedInterval (-19900047834 / 1000000000000) (-19899938009 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (122673141332717 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23333895583 / 1000000000000) (23333895584 / 1000000000000), orderedInterval (16892149821 / 1000000000000) (16892149822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (90360480680903 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1728442351 / 1000000000000) (1728442352 / 1000000000000), orderedInterval (33528551400 / 1000000000000) (33528551401 / 1000000000000)))) (orderedInterval (-677937668 / 1000000000000) (-677937646 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_chunkChecks0_1 :
    compactCertificate516.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (138636214604969 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4906667070 / 1000000000000) (4906667071 / 1000000000000), orderedInterval (26655138487 / 1000000000000) (26655138488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (80041655821601 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35646709601 / 1000000000000) (-35646709277 / 1000000000000), orderedInterval (-1338558660 / 1000000000000) (-1338558336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (142035322852309 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14331265828 / 1000000000000) (14331265909 / 1000000000000), orderedInterval (-22630064164 / 1000000000000) (-22630064083 / 1000000000000)))) (orderedInterval (-1475709540 / 1000000000000) (-1475709350 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (132707822946121 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20419395173 / 1000000000000) (20419395174 / 1000000000000), orderedInterval (18711814593 / 1000000000000) (18711814594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (94706564362393 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28605751863 / 1000000000000) (28605842869 / 1000000000000), orderedInterval (-16062658519 / 1000000000000) (-16062567513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (107387150069247 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-10442705361 / 1000000000000) (-10442705345 / 1000000000000), orderedInterval (28981438859 / 1000000000000) (28981438875 / 1000000000000)))) (orderedInterval (2389254864 / 1000000000000) (2389263516 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (89528210054543 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30549050349 / 1000000000000) (30549050351 / 1000000000000), orderedInterval (14272626547 / 1000000000000) (14272626549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (79100888701403 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33522593135 / 1000000000000) (-33522567509 / 1000000000000), orderedInterval (12838112183 / 1000000000000) (12838137808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (22926520650897 / 32000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24348366512 / 1000000000000) (24348366513 / 1000000000000), orderedInterval (17179739913 / 1000000000000) (17179739914 / 1000000000000)))) (orderedInterval (2894569835 / 1000000000000) (2894571339 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_chunkChecks0_2 :
    compactCertificate516.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (63415962677059 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38553898874 / 1000000000000) (38553898878 / 1000000000000), orderedInterval (10896810437 / 1000000000000) (10896810442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (53758413873899 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25457946211 / 1000000000000) (-25457946210 / 1000000000000), orderedInterval (-35270063849 / 1000000000000) (-35270063848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (33639519319097 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28531217076 / 1000000000000) (-28531217075 / 1000000000000), orderedInterval (-46984618776 / 1000000000000) (-46984618775 / 1000000000000)))) (orderedInterval (-5652399958 / 1000000000000) (-5652399859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (18091445369799 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (51610768636 / 1000000000000) (51610768637 / 1000000000000), orderedInterval (54238016720 / 1000000000000) (54238016721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (49121793466397 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-3633607931 / 1000000000000) (-3633607926 / 1000000000000), orderedInterval (45397590249 / 1000000000000) (45397590253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (67071609427069 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32596163806 / 1000000000000) (-32596057587 / 1000000000000), orderedInterval (21396631551 / 1000000000000) (21396737770 / 1000000000000)))) (orderedInterval (1627561277 / 1000000000000) (1627569464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (28360480680903 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51472597755 / 1000000000000) (51472626505 / 1000000000000), orderedInterval (-30839692769 / 1000000000000) (-30839664020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (115283779441063 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28277376136 / 1000000000000) (-28277330707 / 1000000000000), orderedInterval (9181621434 / 1000000000000) (9181666863 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (77004221947817 / 160000000000) 0 (IntervalRat.scale (775 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35827378483 / 1000000000000) (-35827378440 / 1000000000000), orderedInterval (-6221535349 / 1000000000000) (-6221535305 / 1000000000000)))) (orderedInterval (9334285205 / 1000000000000) (9334289192 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_chunkChecks0 :
    compactCertificate516.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate516.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate516_chunkChecks0_0
    compactCertificate516_chunkChecks0_1 compactCertificate516_chunkChecks0_2

theorem compactCertificate516_chunkChecks1_0 :
    compactCertificate516.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (775 / 2) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38741556503 / 1000000000000) (-38741548550 / 1000000000000), orderedInterval (11965550480 / 1000000000000) (11965558433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (45668919384931 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15338161982 / 1000000000000) (-15338161981 / 1000000000000), orderedInterval (-44639966047 / 1000000000000) (-44639966046 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (14768390201923 / 32000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17256098683 / 1000000000000) (-17256098682 / 1000000000000), orderedInterval (-32869735431 / 1000000000000) (-32869735430 / 1000000000000)))) (orderedInterval (2139093394 / 1000000000000) (2139096577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (13326076776617 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (59665404881 / 1000000000000) (59665463202 / 1000000000000), orderedInterval (-64261585653 / 1000000000000) (-64261527331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (35795716689749 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52986505693 / 1000000000000) (-52986505679 / 1000000000000), orderedInterval (-6045328971 / 1000000000000) (-6045328957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (97192334071233 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30529569543 / 1000000000000) (-30529535316 / 1000000000000), orderedInterval (10793703123 / 1000000000000) (10793737350 / 1000000000000)))) (orderedInterval (-1180453232 / 1000000000000) (-1180449228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (71591433379529 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32065484125 / 1000000000000) (32065593949 / 1000000000000), orderedInterval (-19900047834 / 1000000000000) (-19899938009 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (122673141332717 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23333895583 / 1000000000000) (23333895584 / 1000000000000), orderedInterval (16892149821 / 1000000000000) (16892149822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (90360480680903 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1728442351 / 1000000000000) (1728442352 / 1000000000000), orderedInterval (33528551400 / 1000000000000) (33528551401 / 1000000000000)))) (orderedInterval (150088144 / 1000000000000) (150088183 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_chunkChecks1_1 :
    compactCertificate516.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (138636214604969 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4906667070 / 1000000000000) (4906667071 / 1000000000000), orderedInterval (26655138487 / 1000000000000) (26655138488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (80041655821601 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35646709601 / 1000000000000) (-35646709277 / 1000000000000), orderedInterval (-1338558660 / 1000000000000) (-1338558336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (142035322852309 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14331265828 / 1000000000000) (14331265909 / 1000000000000), orderedInterval (-22630064164 / 1000000000000) (-22630064083 / 1000000000000)))) (orderedInterval (-18088510064 / 1000000000000) (-18088509688 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (132707822946121 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20419395173 / 1000000000000) (20419395174 / 1000000000000), orderedInterval (18711814593 / 1000000000000) (18711814594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (94706564362393 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28605751863 / 1000000000000) (28605842869 / 1000000000000), orderedInterval (-16062658519 / 1000000000000) (-16062567513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (107387150069247 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-10442705361 / 1000000000000) (-10442705345 / 1000000000000), orderedInterval (28981438859 / 1000000000000) (28981438875 / 1000000000000)))) (orderedInterval (-3297289309 / 1000000000000) (-3297276088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (89528210054543 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30549050349 / 1000000000000) (30549050351 / 1000000000000), orderedInterval (14272626547 / 1000000000000) (14272626549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (79100888701403 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33522593135 / 1000000000000) (-33522567509 / 1000000000000), orderedInterval (12838112183 / 1000000000000) (12838137808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (22926520650897 / 32000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24348366512 / 1000000000000) (24348366513 / 1000000000000), orderedInterval (17179739913 / 1000000000000) (17179739914 / 1000000000000)))) (orderedInterval (113949023 / 1000000000000) (113950948 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_chunkChecks1_2 :
    compactCertificate516.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (63415962677059 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38553898874 / 1000000000000) (38553898878 / 1000000000000), orderedInterval (10896810437 / 1000000000000) (10896810442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (53758413873899 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25457946211 / 1000000000000) (-25457946210 / 1000000000000), orderedInterval (-35270063849 / 1000000000000) (-35270063848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (33639519319097 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28531217076 / 1000000000000) (-28531217075 / 1000000000000), orderedInterval (-46984618776 / 1000000000000) (-46984618775 / 1000000000000)))) (orderedInterval (-881106381 / 1000000000000) (-881106290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (18091445369799 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (51610768636 / 1000000000000) (51610768637 / 1000000000000), orderedInterval (54238016720 / 1000000000000) (54238016721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (49121793466397 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-3633607931 / 1000000000000) (-3633607926 / 1000000000000), orderedInterval (45397590249 / 1000000000000) (45397590253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (67071609427069 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32596163806 / 1000000000000) (-32596057587 / 1000000000000), orderedInterval (21396631551 / 1000000000000) (21396737770 / 1000000000000)))) (orderedInterval (-2882197247 / 1000000000000) (-2882188398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (28360480680903 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51472597755 / 1000000000000) (51472626505 / 1000000000000), orderedInterval (-30839692769 / 1000000000000) (-30839664020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (115283779441063 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28277376136 / 1000000000000) (-28277330707 / 1000000000000), orderedInterval (9181621434 / 1000000000000) (9181666863 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (77004221947817 / 160000000000) 1 (IntervalRat.scale (775 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35827378483 / 1000000000000) (-35827378440 / 1000000000000), orderedInterval (-6221535349 / 1000000000000) (-6221535305 / 1000000000000)))) (orderedInterval (-24954061 / 1000000000000) (-24946944 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_chunkChecks1 :
    compactCertificate516.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate516.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate516_chunkChecks1_0
    compactCertificate516_chunkChecks1_1 compactCertificate516_chunkChecks1_2

theorem compactCertificate516_chunkChecks2_0 :
    compactCertificate516.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (775 / 2) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38741556503 / 1000000000000) (-38741548550 / 1000000000000), orderedInterval (11965550480 / 1000000000000) (11965558433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (45668919384931 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15338161982 / 1000000000000) (-15338161981 / 1000000000000), orderedInterval (-44639966047 / 1000000000000) (-44639966046 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (14768390201923 / 32000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17256098683 / 1000000000000) (-17256098682 / 1000000000000), orderedInterval (-32869735431 / 1000000000000) (-32869735430 / 1000000000000)))) (orderedInterval (16864181563 / 1000000000000) (16864184759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (13326076776617 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (59665404881 / 1000000000000) (59665463202 / 1000000000000), orderedInterval (-64261585653 / 1000000000000) (-64261527331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (35795716689749 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52986505693 / 1000000000000) (-52986505679 / 1000000000000), orderedInterval (-6045328971 / 1000000000000) (-6045328957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (97192334071233 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30529569543 / 1000000000000) (-30529535316 / 1000000000000), orderedInterval (10793703123 / 1000000000000) (10793737350 / 1000000000000)))) (orderedInterval (-4655614869 / 1000000000000) (-4655608776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (71591433379529 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32065484125 / 1000000000000) (32065593949 / 1000000000000), orderedInterval (-19900047834 / 1000000000000) (-19899938009 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (122673141332717 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23333895583 / 1000000000000) (23333895584 / 1000000000000), orderedInterval (16892149821 / 1000000000000) (16892149822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (90360480680903 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1728442351 / 1000000000000) (1728442352 / 1000000000000), orderedInterval (33528551400 / 1000000000000) (33528551401 / 1000000000000)))) (orderedInterval (2728445247 / 1000000000000) (2728445315 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_chunkChecks2_1 :
    compactCertificate516.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (138636214604969 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4906667070 / 1000000000000) (4906667071 / 1000000000000), orderedInterval (26655138487 / 1000000000000) (26655138488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (80041655821601 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35646709601 / 1000000000000) (-35646709277 / 1000000000000), orderedInterval (-1338558660 / 1000000000000) (-1338558336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (142035322852309 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14331265828 / 1000000000000) (14331265909 / 1000000000000), orderedInterval (-22630064164 / 1000000000000) (-22630064083 / 1000000000000)))) (orderedInterval (-1884158595 / 1000000000000) (-1884157811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (132707822946121 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20419395173 / 1000000000000) (20419395174 / 1000000000000), orderedInterval (18711814593 / 1000000000000) (18711814594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (94706564362393 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28605751863 / 1000000000000) (28605842869 / 1000000000000), orderedInterval (-16062658519 / 1000000000000) (-16062567513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (107387150069247 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-10442705361 / 1000000000000) (-10442705345 / 1000000000000), orderedInterval (28981438859 / 1000000000000) (28981438875 / 1000000000000)))) (orderedInterval (-4772913510 / 1000000000000) (-4772893271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (89528210054543 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30549050349 / 1000000000000) (30549050351 / 1000000000000), orderedInterval (14272626547 / 1000000000000) (14272626549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (79100888701403 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33522593135 / 1000000000000) (-33522567509 / 1000000000000), orderedInterval (12838112183 / 1000000000000) (12838137808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (22926520650897 / 32000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24348366512 / 1000000000000) (24348366513 / 1000000000000), orderedInterval (17179739913 / 1000000000000) (17179739914 / 1000000000000)))) (orderedInterval (-5989594401 / 1000000000000) (-5989591928 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_chunkChecks2_2 :
    compactCertificate516.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (63415962677059 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38553898874 / 1000000000000) (38553898878 / 1000000000000), orderedInterval (10896810437 / 1000000000000) (10896810442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (53758413873899 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25457946211 / 1000000000000) (-25457946210 / 1000000000000), orderedInterval (-35270063849 / 1000000000000) (-35270063848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (33639519319097 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28531217076 / 1000000000000) (-28531217075 / 1000000000000), orderedInterval (-46984618776 / 1000000000000) (-46984618775 / 1000000000000)))) (orderedInterval (5641672817 / 1000000000000) (5641672904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (18091445369799 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (51610768636 / 1000000000000) (51610768637 / 1000000000000), orderedInterval (54238016720 / 1000000000000) (54238016721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (49121793466397 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-3633607931 / 1000000000000) (-3633607926 / 1000000000000), orderedInterval (45397590249 / 1000000000000) (45397590253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (67071609427069 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32596163806 / 1000000000000) (-32596057587 / 1000000000000), orderedInterval (21396631551 / 1000000000000) (21396737770 / 1000000000000)))) (orderedInterval (-2886708544 / 1000000000000) (-2886698953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (28360480680903 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51472597755 / 1000000000000) (51472626505 / 1000000000000), orderedInterval (-30839692769 / 1000000000000) (-30839664020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (115283779441063 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28277376136 / 1000000000000) (-28277330707 / 1000000000000), orderedInterval (9181621434 / 1000000000000) (9181666863 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (77004221947817 / 160000000000) 2 (IntervalRat.scale (775 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35827378483 / 1000000000000) (-35827378440 / 1000000000000), orderedInterval (-6221535349 / 1000000000000) (-6221535305 / 1000000000000)))) (orderedInterval (-18392698283 / 1000000000000) (-18392685208 / 1000000000000))) = true
  rfl'

theorem compactCertificate516_chunkChecks2 :
    compactCertificate516.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate516.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate516_chunkChecks2_0
    compactCertificate516_chunkChecks2_1 compactCertificate516_chunkChecks2_2

theorem compactCertificate516_chunkChecks3_0 :
    compactCertificate516.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (775 / 2) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38741556503 / 1000000000000) (-38741548550 / 1000000000000), orderedInterval (11965550480 / 1000000000000) (11965558433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (45668919384931 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15338161982 / 1000000000000) (-15338161981 / 1000000000000), orderedInterval (-44639966047 / 1000000000000) (-44639966046 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (14768390201923 / 32000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17256098683 / 1000000000000) (-17256098682 / 1000000000000), orderedInterval (-32869735431 / 1000000000000) (-32869735430 / 1000000000000)))) (orderedInterval (-1361408490 / 1000000000000) (-1361405289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (13326076776617 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (59665404881 / 1000000000000) (59665463202 / 1000000000000), orderedInterval (-64261585653 / 1000000000000) (-64261527331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (35795716689749 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52986505693 / 1000000000000) (-52986505679 / 1000000000000), orderedInterval (-6045328971 / 1000000000000) (-6045328957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (97192334071233 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30529569543 / 1000000000000) (-30529535316 / 1000000000000), orderedInterval (10793703123 / 1000000000000) (10793737350 / 1000000000000)))) (orderedInterval (3003516939 / 1000000000000) (3003526444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (71591433379529 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32065484125 / 1000000000000) (32065593949 / 1000000000000), orderedInterval (-19900047834 / 1000000000000) (-19899938009 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (122673141332717 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23333895583 / 1000000000000) (23333895584 / 1000000000000), orderedInterval (16892149821 / 1000000000000) (16892149822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (90360480680903 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1728442351 / 1000000000000) (1728442352 / 1000000000000), orderedInterval (33528551400 / 1000000000000) (33528551401 / 1000000000000)))) (orderedInterval (1520240177 / 1000000000000) (1520240300 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate516_chunkChecks3_1 :
    compactCertificate516.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (138636214604969 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4906667070 / 1000000000000) (4906667071 / 1000000000000), orderedInterval (26655138487 / 1000000000000) (26655138488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (80041655821601 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35646709601 / 1000000000000) (-35646709277 / 1000000000000), orderedInterval (-1338558660 / 1000000000000) (-1338558336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (142035322852309 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14331265828 / 1000000000000) (14331265909 / 1000000000000), orderedInterval (-22630064164 / 1000000000000) (-22630064083 / 1000000000000)))) (orderedInterval (91849595130 / 1000000000000) (91849596818 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (132707822946121 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20419395173 / 1000000000000) (20419395174 / 1000000000000), orderedInterval (18711814593 / 1000000000000) (18711814594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (94706564362393 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28605751863 / 1000000000000) (28605842869 / 1000000000000), orderedInterval (-16062658519 / 1000000000000) (-16062567513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (107387150069247 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-10442705361 / 1000000000000) (-10442705345 / 1000000000000), orderedInterval (28981438859 / 1000000000000) (28981438875 / 1000000000000)))) (orderedInterval (9500857416 / 1000000000000) (9500888352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (89528210054543 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30549050349 / 1000000000000) (30549050351 / 1000000000000), orderedInterval (14272626547 / 1000000000000) (14272626549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (79100888701403 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33522593135 / 1000000000000) (-33522567509 / 1000000000000), orderedInterval (12838112183 / 1000000000000) (12838137808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (22926520650897 / 32000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24348366512 / 1000000000000) (24348366513 / 1000000000000), orderedInterval (17179739913 / 1000000000000) (17179739914 / 1000000000000)))) (orderedInterval (-1735276770 / 1000000000000) (-1735273595 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate516_chunkChecks3_2 :
    compactCertificate516.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (63415962677059 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38553898874 / 1000000000000) (38553898878 / 1000000000000), orderedInterval (10896810437 / 1000000000000) (10896810442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (53758413873899 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25457946211 / 1000000000000) (-25457946210 / 1000000000000), orderedInterval (-35270063849 / 1000000000000) (-35270063848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (33639519319097 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28531217076 / 1000000000000) (-28531217075 / 1000000000000), orderedInterval (-46984618776 / 1000000000000) (-46984618775 / 1000000000000)))) (orderedInterval (792861450 / 1000000000000) (792861534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (18091445369799 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (51610768636 / 1000000000000) (51610768637 / 1000000000000), orderedInterval (54238016720 / 1000000000000) (54238016721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (49121793466397 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-3633607931 / 1000000000000) (-3633607926 / 1000000000000), orderedInterval (45397590249 / 1000000000000) (45397590253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (67071609427069 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32596163806 / 1000000000000) (-32596057587 / 1000000000000), orderedInterval (21396631551 / 1000000000000) (21396737770 / 1000000000000)))) (orderedInterval (2620570685 / 1000000000000) (2620581059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (28360480680903 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51472597755 / 1000000000000) (51472626505 / 1000000000000), orderedInterval (-30839692769 / 1000000000000) (-30839664020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (115283779441063 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28277376136 / 1000000000000) (-28277330707 / 1000000000000), orderedInterval (9181621434 / 1000000000000) (9181666863 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (77004221947817 / 160000000000) 3 (IntervalRat.scale (775 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35827378483 / 1000000000000) (-35827378440 / 1000000000000), orderedInterval (-6221535349 / 1000000000000) (-6221535305 / 1000000000000)))) (orderedInterval (2633685617 / 1000000000000) (2633709799 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate516_chunkChecks3 :
    compactCertificate516.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate516.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate516_chunkChecks3_0
    compactCertificate516_chunkChecks3_1 compactCertificate516_chunkChecks3_2

theorem compactCertificate516_chunkChecks4_0 :
    compactCertificate516.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (775 / 2) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38741556503 / 1000000000000) (-38741548550 / 1000000000000), orderedInterval (11965550480 / 1000000000000) (11965558433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (45668919384931 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15338161982 / 1000000000000) (-15338161981 / 1000000000000), orderedInterval (-44639966047 / 1000000000000) (-44639966046 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (14768390201923 / 32000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17256098683 / 1000000000000) (-17256098682 / 1000000000000), orderedInterval (-32869735431 / 1000000000000) (-32869735430 / 1000000000000)))) (orderedInterval (-17428182460 / 1000000000000) (-17428179244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (13326076776617 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (59665404881 / 1000000000000) (59665463202 / 1000000000000), orderedInterval (-64261585653 / 1000000000000) (-64261527331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (35795716689749 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52986505693 / 1000000000000) (-52986505679 / 1000000000000), orderedInterval (-6045328971 / 1000000000000) (-6045328957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (97192334071233 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30529569543 / 1000000000000) (-30529535316 / 1000000000000), orderedInterval (10793703123 / 1000000000000) (10793737350 / 1000000000000)))) (orderedInterval (12874658806 / 1000000000000) (12874673718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (71591433379529 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32065484125 / 1000000000000) (32065593949 / 1000000000000), orderedInterval (-19900047834 / 1000000000000) (-19899938009 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (122673141332717 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23333895583 / 1000000000000) (23333895584 / 1000000000000), orderedInterval (16892149821 / 1000000000000) (16892149822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (90360480680903 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1728442351 / 1000000000000) (1728442352 / 1000000000000), orderedInterval (33528551400 / 1000000000000) (33528551401 / 1000000000000)))) (orderedInterval (-10849704094 / 1000000000000) (-10849703867 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate516_chunkChecks4_1 :
    compactCertificate516.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (138636214604969 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4906667070 / 1000000000000) (4906667071 / 1000000000000), orderedInterval (26655138487 / 1000000000000) (26655138488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (80041655821601 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35646709601 / 1000000000000) (-35646709277 / 1000000000000), orderedInterval (-1338558660 / 1000000000000) (-1338558336 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (142035322852309 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14331265828 / 1000000000000) (14331265909 / 1000000000000), orderedInterval (-22630064164 / 1000000000000) (-22630064083 / 1000000000000)))) (orderedInterval (26506667162 / 1000000000000) (26506670871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (132707822946121 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20419395173 / 1000000000000) (20419395174 / 1000000000000), orderedInterval (18711814593 / 1000000000000) (18711814594 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (94706564362393 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28605751863 / 1000000000000) (28605842869 / 1000000000000), orderedInterval (-16062658519 / 1000000000000) (-16062567513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (107387150069247 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-10442705361 / 1000000000000) (-10442705345 / 1000000000000), orderedInterval (28981438859 / 1000000000000) (28981438875 / 1000000000000)))) (orderedInterval (7416264736 / 1000000000000) (7416312114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (89528210054543 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30549050349 / 1000000000000) (30549050351 / 1000000000000), orderedInterval (14272626547 / 1000000000000) (14272626549 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (79100888701403 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33522593135 / 1000000000000) (-33522567509 / 1000000000000), orderedInterval (12838112183 / 1000000000000) (12838137808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (22926520650897 / 32000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24348366512 / 1000000000000) (24348366513 / 1000000000000), orderedInterval (17179739913 / 1000000000000) (17179739914 / 1000000000000)))) (orderedInterval (13910622915 / 1000000000000) (13910627011 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate516_chunkChecks4_2 :
    compactCertificate516.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (63415962677059 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38553898874 / 1000000000000) (38553898878 / 1000000000000), orderedInterval (10896810437 / 1000000000000) (10896810442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (53758413873899 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-25457946211 / 1000000000000) (-25457946210 / 1000000000000), orderedInterval (-35270063849 / 1000000000000) (-35270063848 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (33639519319097 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28531217076 / 1000000000000) (-28531217075 / 1000000000000), orderedInterval (-46984618776 / 1000000000000) (-46984618775 / 1000000000000)))) (orderedInterval (-6017315704 / 1000000000000) (-6017315620 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (18091445369799 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (51610768636 / 1000000000000) (51610768637 / 1000000000000), orderedInterval (54238016720 / 1000000000000) (54238016721 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (49121793466397 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-3633607931 / 1000000000000) (-3633607926 / 1000000000000), orderedInterval (45397590249 / 1000000000000) (45397590253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (67071609427069 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-32596163806 / 1000000000000) (-32596057587 / 1000000000000), orderedInterval (21396631551 / 1000000000000) (21396737770 / 1000000000000)))) (orderedInterval (3433416106 / 1000000000000) (3433427353 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (28360480680903 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (51472597755 / 1000000000000) (51472626505 / 1000000000000), orderedInterval (-30839692769 / 1000000000000) (-30839664020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (115283779441063 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-28277376136 / 1000000000000) (-28277330707 / 1000000000000), orderedInterval (9181621434 / 1000000000000) (9181666863 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (77004221947817 / 160000000000) 4 (IntervalRat.scale (775 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35827378483 / 1000000000000) (-35827378440 / 1000000000000), orderedInterval (-6221535349 / 1000000000000) (-6221535305 / 1000000000000)))) (orderedInterval (43511033950 / 1000000000000) (43511078856 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate516_chunkChecks4 :
    compactCertificate516.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate516.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate516_chunkChecks4_0
    compactCertificate516_chunkChecks4_1 compactCertificate516_chunkChecks4_2

theorem compactCertificate516_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate516.chunkCheck r b = true :=
  compactCertificate516.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate516_chunkChecks0
    · exact compactCertificate516_chunkChecks1
    · exact compactCertificate516_chunkChecks2
    · exact compactCertificate516_chunkChecks3
    · exact compactCertificate516_chunkChecks4)

theorem compactCertificate516_coefficient0 :
    compactCertificate516.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate516_coefficient1 :
    compactCertificate516.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate516_coefficient2 :
    compactCertificate516.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate516_coefficient3 :
    compactCertificate516.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate516_coefficient4 :
    compactCertificate516.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate516_coefficients : ∀ r : Fin 5,
    compactCertificate516.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate516_coefficient0
  · exact compactCertificate516_coefficient1
  · exact compactCertificate516_coefficient2
  · exact compactCertificate516_coefficient3
  · exact compactCertificate516_coefficient4

theorem compactCertificate516_lower : (1 : ℚ) ≤ compactCertificate516.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate516, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate516_proves {t : ℝ} (ht : t ∈ compactCertificate516.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate516.proves compactCertificate516_states compactCertificate516_chunks
    compactCertificate516_coefficients compactCertificate516_lower ht

end Erdos232
