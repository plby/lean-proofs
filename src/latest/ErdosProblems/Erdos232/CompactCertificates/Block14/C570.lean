/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate570 : CompactCertificate where
  left := 441
  right := 442
  center := 883 / 2
  grid := fun i =>
    match i.val with
    | 0 => 141
    | 1 => 104
    | 2 => 167
    | 3 => 30
    | 4 => 81
    | 5 => 220
    | 6 => 162
    | 7 => 278
    | 8 => 205
    | 9 => 314
    | 10 => 182
    | 11 => 322
    | 12 => 301
    | 13 => 215
    | 14 => 244
    | 15 => 203
    | 16 => 179
    | 17 => 260
    | 18 => 144
    | 19 => 122
    | 20 => 76
    | 21 => 41
    | 22 => 111
    | 23 => 152
    | 24 => 64
    | 25 => 261
    | _ => 175
  point := fun i =>
    match i.val with
    | 0 => 883 / 2
    | 1 => 1300827606996583 / 4000000000000
    | 2 => 420660920912839 / 800000000000
    | 3 => 379578251411381 / 4000000000000
    | 4 => 1019600575388657 / 4000000000000
    | 5 => 2768413902738669 / 4000000000000
    | 6 => 2039201150778197 / 4000000000000
    | 7 => 3494205928928681 / 4000000000000
    | 8 => 2573816272297979 / 4000000000000
    | 9 => 3948896048264117 / 4000000000000
    | 10 => 2279896196466893 / 4000000000000
    | 11 => 4045715808986737 / 4000000000000
    | 12 => 3780032505207253 / 4000000000000
    | 13 => 2697609559096549 / 4000000000000
    | 14 => 3058801726165971 / 4000000000000
    | 15 => 2550109983166499 / 4000000000000
    | 16 => 2253099507204479 / 4000000000000
    | 17 => 653036055959421 / 800000000000
    | 18 => 1806332098188487 / 4000000000000
    | 19 => 1531247724214607 / 4000000000000
    | 20 => 958183727702021 / 4000000000000
    | 21 => 515314395533307 / 4000000000000
    | 22 => 1399178826800921 / 4000000000000
    | 23 => 1910459068519417 / 4000000000000
    | 24 => 807816272297979 / 4000000000000
    | 25 => 3283728298272859 / 4000000000000
    | _ => 2193378321932981 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (23860866650 / 1000000000000) (23860871914 / 1000000000000), orderedInterval (-29566938673 / 1000000000000) (-29566933409 / 1000000000000))
    | 1 => (orderedInterval (-29627822445 / 1000000000000) (-29627806075 / 1000000000000), orderedInterval (32905499236 / 1000000000000) (32905515606 / 1000000000000))
    | 2 => (orderedInterval (-32121962169 / 1000000000000) (-32121923305 / 1000000000000), orderedInterval (13405287025 / 1000000000000) (13405325889 / 1000000000000))
    | 3 => (orderedInterval (81105531701 / 1000000000000) (81105531705 / 1000000000000), orderedInterval (10996753204 / 1000000000000) (10996753208 / 1000000000000))
    | 4 => (orderedInterval (-46863425055 / 1000000000000) (-46863425054 / 1000000000000), orderedInterval (-17267277082 / 1000000000000) (-17267277081 / 1000000000000))
    | 5 => (orderedInterval (29904215293 / 1000000000000) (29904225365 / 1000000000000), orderedInterval (-5078346639 / 1000000000000) (-5078336566 / 1000000000000))
    | 6 => (orderedInterval (35234116732 / 1000000000000) (35234118139 / 1000000000000), orderedInterval (-2740004458 / 1000000000000) (-2740003051 / 1000000000000))
    | 7 => (orderedInterval (22328982800 / 1000000000000) (22328982802 / 1000000000000), orderedInterval (15159179810 / 1000000000000) (15159179812 / 1000000000000))
    | 8 => (orderedInterval (-6642413129 / 1000000000000) (-6642413128 / 1000000000000), orderedInterval (-30739876377 / 1000000000000) (-30739876376 / 1000000000000))
    | 9 => (orderedInterval (25388131763 / 1000000000000) (25388138517 / 1000000000000), orderedInterval (535758335 / 1000000000000) (535765089 / 1000000000000))
    | 10 => (orderedInterval (-28312823659 / 1000000000000) (-28312757849 / 1000000000000), orderedInterval (17781866398 / 1000000000000) (17781932209 / 1000000000000))
    | 11 => (orderedInterval (14605638107 / 1000000000000) (14605638108 / 1000000000000), orderedInterval (20391344649 / 1000000000000) (20391344650 / 1000000000000))
    | 12 => (orderedInterval (-4493517035 / 1000000000000) (-4493517034 / 1000000000000), orderedInterval (-25560766223 / 1000000000000) (-25560766222 / 1000000000000))
    | 13 => (orderedInterval (7744622934 / 1000000000000) (7744622938 / 1000000000000), orderedInterval (-29737832137 / 1000000000000) (-29737832133 / 1000000000000))
    | 14 => (orderedInterval (-25211668196 / 1000000000000) (-25211624376 / 1000000000000), orderedInterval (14047908695 / 1000000000000) (14047952515 / 1000000000000))
    | 15 => (orderedInterval (-17036255383 / 1000000000000) (-17036255382 / 1000000000000), orderedInterval (-26601339879 / 1000000000000) (-26601339878 / 1000000000000))
    | 16 => (orderedInterval (-33269829600 / 1000000000000) (-33269825565 / 1000000000000), orderedInterval (4859612551 / 1000000000000) (4859616585 / 1000000000000))
    | 17 => (orderedInterval (7347219490 / 1000000000000) (7347219491 / 1000000000000), orderedInterval (26938175272 / 1000000000000) (26938175273 / 1000000000000))
    | 18 => (orderedInterval (-795786949 / 1000000000000) (-795786948 / 1000000000000), orderedInterval (37539113922 / 1000000000000) (37539113923 / 1000000000000))
    | 19 => (orderedInterval (12932451018 / 1000000000000) (12932451019 / 1000000000000), orderedInterval (38658191932 / 1000000000000) (38658191933 / 1000000000000))
    | 20 => (orderedInterval (51551933426 / 1000000000000) (51551933516 / 1000000000000), orderedInterval (-54518486 / 1000000000000) (-54518396 / 1000000000000))
    | 21 => (orderedInterval (-50804433777 / 1000000000000) (-50804433776 / 1000000000000), orderedInterval (-48387911839 / 1000000000000) (-48387911838 / 1000000000000))
    | 22 => (orderedInterval (-40853324353 / 1000000000000) (-40853318218 / 1000000000000), orderedInterval (12346017965 / 1000000000000) (12346024101 / 1000000000000))
    | 23 => (orderedInterval (28088206882 / 1000000000000) (28088206883 / 1000000000000), orderedInterval (23293701058 / 1000000000000) (23293701059 / 1000000000000))
    | 24 => (orderedInterval (55829410467 / 1000000000000) (55829410766 / 1000000000000), orderedInterval (-6085262370 / 1000000000000) (-6085262072 / 1000000000000))
    | 25 => (orderedInterval (-27341951239 / 1000000000000) (-27341927560 / 1000000000000), orderedInterval (5298903958 / 1000000000000) (5298927638 / 1000000000000))
    | _ => (orderedInterval (20592528104 / 1000000000000) (20592530206 / 1000000000000), orderedInterval (-27165283530 / 1000000000000) (-27165281429 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (7296585041 / 1000000000000) (7296589591 / 1000000000000)
      | 1 => orderedInterval (-4716883660 / 1000000000000) (-4716882890 / 1000000000000)
      | 2 => orderedInterval (-849249200 / 1000000000000) (-849249175 / 1000000000000)
      | 3 => orderedInterval (-4532635499 / 1000000000000) (-4532629248 / 1000000000000)
      | 4 => orderedInterval (941060905 / 1000000000000) (941061180 / 1000000000000)
      | 5 => orderedInterval (1895310325 / 1000000000000) (1895310599 / 1000000000000)
      | 6 => orderedInterval (1073551268 / 1000000000000) (1073551382 / 1000000000000)
      | 7 => orderedInterval (-287705056 / 1000000000000) (-287704864 / 1000000000000)
      | _ => orderedInterval (-1301465498 / 1000000000000) (-1301463051 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-10556563259 / 1000000000000) (-10556558310 / 1000000000000)
      | 1 => orderedInterval (176298218 / 1000000000000) (176299402 / 1000000000000)
      | 2 => orderedInterval (-2007887999 / 1000000000000) (-2007887956 / 1000000000000)
      | 3 => orderedInterval (8128724233 / 1000000000000) (8128733574 / 1000000000000)
      | 4 => orderedInterval (-3430966711 / 1000000000000) (-3430966240 / 1000000000000)
      | 5 => orderedInterval (476859645 / 1000000000000) (476860001 / 1000000000000)
      | 6 => orderedInterval (-8037459823 / 1000000000000) (-8037459718 / 1000000000000)
      | 7 => orderedInterval (-1892428800 / 1000000000000) (-1892428641 / 1000000000000)
      | _ => orderedInterval (5511577403 / 1000000000000) (5511581650 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-6610149850 / 1000000000000) (-6610144394 / 1000000000000)
      | 1 => orderedInterval (5834801936 / 1000000000000) (5834803782 / 1000000000000)
      | 2 => orderedInterval (3041756629 / 1000000000000) (3041756707 / 1000000000000)
      | 3 => orderedInterval (15136953865 / 1000000000000) (15136968790 / 1000000000000)
      | 4 => orderedInterval (-2455472445 / 1000000000000) (-2455471636 / 1000000000000)
      | 5 => orderedInterval (-3332997346 / 1000000000000) (-3332996878 / 1000000000000)
      | 6 => orderedInterval (-58668051 / 1000000000000) (-58667953 / 1000000000000)
      | 7 => orderedInterval (1861845713 / 1000000000000) (1861845849 / 1000000000000)
      | _ => orderedInterval (-1817997447 / 1000000000000) (-1817989911 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10282719016 / 1000000000000) (10282725075 / 1000000000000)
      | 1 => orderedInterval (-1281450365 / 1000000000000) (-1281447478 / 1000000000000)
      | 2 => orderedInterval (5914734107 / 1000000000000) (5914734247 / 1000000000000)
      | 3 => orderedInterval (-36656461219 / 1000000000000) (-36656435573 / 1000000000000)
      | 4 => orderedInterval (5872659257 / 1000000000000) (5872660652 / 1000000000000)
      | 5 => orderedInterval (-2849387154 / 1000000000000) (-2849386533 / 1000000000000)
      | 6 => orderedInterval (7849633359 / 1000000000000) (7849633455 / 1000000000000)
      | 7 => orderedInterval (2372978916 / 1000000000000) (2372979034 / 1000000000000)
      | _ => orderedInterval (-6984452957 / 1000000000000) (-6984439402 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (5537042853 / 1000000000000) (5537049655 / 1000000000000)
      | 1 => orderedInterval (-13024244224 / 1000000000000) (-13024239695 / 1000000000000)
      | 2 => orderedInterval (-11306377779 / 1000000000000) (-11306377520 / 1000000000000)
      | 3 => orderedInterval (-61252195205 / 1000000000000) (-61252147764 / 1000000000000)
      | 4 => orderedInterval (6811686024 / 1000000000000) (6811688443 / 1000000000000)
      | 5 => orderedInterval (6400269881 / 1000000000000) (6400270717 / 1000000000000)
      | 6 => orderedInterval (-164574911 / 1000000000000) (-164574817 / 1000000000000)
      | 7 => orderedInterval (-2586967354 / 1000000000000) (-2586967248 / 1000000000000)
      | _ => orderedInterval (17457914963 / 1000000000000) (17457939630 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-481431374 / 1000000000000) (-481416476 / 1000000000000)
    | 1 => orderedInterval (-11631847093 / 1000000000000) (-11631826238 / 1000000000000)
    | 2 => orderedInterval (11600073004 / 1000000000000) (11600104356 / 1000000000000)
    | 3 => orderedInterval (-15479027040 / 1000000000000) (-15478976523 / 1000000000000)
    | _ => orderedInterval (-52127445752 / 1000000000000) (-52127358599 / 1000000000000)

theorem compactCertificate570_stateChecks0 :
    compactCertificate570.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (883 / 2)) (orderedInterval (23860866650 / 1000000000000) (23860871914 / 1000000000000), orderedInterval (-29566938673 / 1000000000000) (-29566933409 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1300827606996583 / 4000000000000)) (orderedInterval (-29627822445 / 1000000000000) (-29627806075 / 1000000000000), orderedInterval (32905499236 / 1000000000000) (32905515606 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (420660920912839 / 800000000000)) (orderedInterval (-32121962169 / 1000000000000) (-32121923305 / 1000000000000), orderedInterval (13405287025 / 1000000000000) (13405325889 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_stateChecks1 :
    compactCertificate570.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (379578251411381 / 4000000000000)) (orderedInterval (81105531701 / 1000000000000) (81105531705 / 1000000000000), orderedInterval (10996753204 / 1000000000000) (10996753208 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1019600575388657 / 4000000000000)) (orderedInterval (-46863425055 / 1000000000000) (-46863425054 / 1000000000000), orderedInterval (-17267277082 / 1000000000000) (-17267277081 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2768413902738669 / 4000000000000)) (orderedInterval (29904215293 / 1000000000000) (29904225365 / 1000000000000), orderedInterval (-5078346639 / 1000000000000) (-5078336566 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_stateChecks2 :
    compactCertificate570.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2039201150778197 / 4000000000000)) (orderedInterval (35234116732 / 1000000000000) (35234118139 / 1000000000000), orderedInterval (-2740004458 / 1000000000000) (-2740003051 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 278 12 (3494205928928681 / 4000000000000)) (orderedInterval (22328982800 / 1000000000000) (22328982802 / 1000000000000), orderedInterval (15159179810 / 1000000000000) (15159179812 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2573816272297979 / 4000000000000)) (orderedInterval (-6642413129 / 1000000000000) (-6642413128 / 1000000000000), orderedInterval (-30739876377 / 1000000000000) (-30739876376 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_stateChecks3 :
    compactCertificate570.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 314 12 (3948896048264117 / 4000000000000)) (orderedInterval (25388131763 / 1000000000000) (25388138517 / 1000000000000), orderedInterval (535758335 / 1000000000000) (535765089 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2279896196466893 / 4000000000000)) (orderedInterval (-28312823659 / 1000000000000) (-28312757849 / 1000000000000), orderedInterval (17781866398 / 1000000000000) (17781932209 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 322 12 (4045715808986737 / 4000000000000)) (orderedInterval (14605638107 / 1000000000000) (14605638108 / 1000000000000), orderedInterval (20391344649 / 1000000000000) (20391344650 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_stateChecks4 :
    compactCertificate570.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 301 12 (3780032505207253 / 4000000000000)) (orderedInterval (-4493517035 / 1000000000000) (-4493517034 / 1000000000000), orderedInterval (-25560766223 / 1000000000000) (-25560766222 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2697609559096549 / 4000000000000)) (orderedInterval (7744622934 / 1000000000000) (7744622938 / 1000000000000), orderedInterval (-29737832137 / 1000000000000) (-29737832133 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (3058801726165971 / 4000000000000)) (orderedInterval (-25211668196 / 1000000000000) (-25211624376 / 1000000000000), orderedInterval (14047908695 / 1000000000000) (14047952515 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_stateChecks5 :
    compactCertificate570.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2550109983166499 / 4000000000000)) (orderedInterval (-17036255383 / 1000000000000) (-17036255382 / 1000000000000), orderedInterval (-26601339879 / 1000000000000) (-26601339878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2253099507204479 / 4000000000000)) (orderedInterval (-33269829600 / 1000000000000) (-33269825565 / 1000000000000), orderedInterval (4859612551 / 1000000000000) (4859616585 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 260 12 (653036055959421 / 800000000000)) (orderedInterval (7347219490 / 1000000000000) (7347219491 / 1000000000000), orderedInterval (26938175272 / 1000000000000) (26938175273 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_stateChecks6 :
    compactCertificate570.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1806332098188487 / 4000000000000)) (orderedInterval (-795786949 / 1000000000000) (-795786948 / 1000000000000), orderedInterval (37539113922 / 1000000000000) (37539113923 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1531247724214607 / 4000000000000)) (orderedInterval (12932451018 / 1000000000000) (12932451019 / 1000000000000), orderedInterval (38658191932 / 1000000000000) (38658191933 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (958183727702021 / 4000000000000)) (orderedInterval (51551933426 / 1000000000000) (51551933516 / 1000000000000), orderedInterval (-54518486 / 1000000000000) (-54518396 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_stateChecks7 :
    compactCertificate570.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (515314395533307 / 4000000000000)) (orderedInterval (-50804433777 / 1000000000000) (-50804433776 / 1000000000000), orderedInterval (-48387911839 / 1000000000000) (-48387911838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1399178826800921 / 4000000000000)) (orderedInterval (-40853324353 / 1000000000000) (-40853318218 / 1000000000000), orderedInterval (12346017965 / 1000000000000) (12346024101 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1910459068519417 / 4000000000000)) (orderedInterval (28088206882 / 1000000000000) (28088206883 / 1000000000000), orderedInterval (23293701058 / 1000000000000) (23293701059 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_stateChecks8 :
    compactCertificate570.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (807816272297979 / 4000000000000)) (orderedInterval (55829410467 / 1000000000000) (55829410766 / 1000000000000), orderedInterval (-6085262370 / 1000000000000) (-6085262072 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 261 12 (3283728298272859 / 4000000000000)) (orderedInterval (-27341951239 / 1000000000000) (-27341927560 / 1000000000000), orderedInterval (5298903958 / 1000000000000) (5298927638 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2193378321932981 / 4000000000000)) (orderedInterval (20592528104 / 1000000000000) (20592530206 / 1000000000000), orderedInterval (-27165283530 / 1000000000000) (-27165281429 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_states : ∀ j,
    BesselStateValid (compactCertificate570.point j) (compactCertificate570.state j) :=
  compactCertificate570.statesValid_of_checks3 compactCertificate570_stateChecks0
    compactCertificate570_stateChecks1 compactCertificate570_stateChecks2
    compactCertificate570_stateChecks3 compactCertificate570_stateChecks4
    compactCertificate570_stateChecks5 compactCertificate570_stateChecks6
    compactCertificate570_stateChecks7 compactCertificate570_stateChecks8

theorem compactCertificate570_chunkChecks0_0 :
    compactCertificate570.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (883 / 2) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23860866650 / 1000000000000) (23860871914 / 1000000000000), orderedInterval (-29566938673 / 1000000000000) (-29566933409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1300827606996583 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29627822445 / 1000000000000) (-29627806075 / 1000000000000), orderedInterval (32905499236 / 1000000000000) (32905515606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (420660920912839 / 800000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32121962169 / 1000000000000) (-32121923305 / 1000000000000), orderedInterval (13405287025 / 1000000000000) (13405325889 / 1000000000000)))) (orderedInterval (7296585041 / 1000000000000) (7296589591 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (379578251411381 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81105531701 / 1000000000000) (81105531705 / 1000000000000), orderedInterval (10996753204 / 1000000000000) (10996753208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1019600575388657 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46863425055 / 1000000000000) (-46863425054 / 1000000000000), orderedInterval (-17267277082 / 1000000000000) (-17267277081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2768413902738669 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29904215293 / 1000000000000) (29904225365 / 1000000000000), orderedInterval (-5078346639 / 1000000000000) (-5078336566 / 1000000000000)))) (orderedInterval (-4716883660 / 1000000000000) (-4716882890 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2039201150778197 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35234116732 / 1000000000000) (35234118139 / 1000000000000), orderedInterval (-2740004458 / 1000000000000) (-2740003051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3494205928928681 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22328982800 / 1000000000000) (22328982802 / 1000000000000), orderedInterval (15159179810 / 1000000000000) (15159179812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2573816272297979 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6642413129 / 1000000000000) (-6642413128 / 1000000000000), orderedInterval (-30739876377 / 1000000000000) (-30739876376 / 1000000000000)))) (orderedInterval (-849249200 / 1000000000000) (-849249175 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_chunkChecks0_1 :
    compactCertificate570.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3948896048264117 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25388131763 / 1000000000000) (25388138517 / 1000000000000), orderedInterval (535758335 / 1000000000000) (535765089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2279896196466893 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28312823659 / 1000000000000) (-28312757849 / 1000000000000), orderedInterval (17781866398 / 1000000000000) (17781932209 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4045715808986737 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14605638107 / 1000000000000) (14605638108 / 1000000000000), orderedInterval (20391344649 / 1000000000000) (20391344650 / 1000000000000)))) (orderedInterval (-4532635499 / 1000000000000) (-4532629248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3780032505207253 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4493517035 / 1000000000000) (-4493517034 / 1000000000000), orderedInterval (-25560766223 / 1000000000000) (-25560766222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2697609559096549 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (7744622934 / 1000000000000) (7744622938 / 1000000000000), orderedInterval (-29737832137 / 1000000000000) (-29737832133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3058801726165971 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25211668196 / 1000000000000) (-25211624376 / 1000000000000), orderedInterval (14047908695 / 1000000000000) (14047952515 / 1000000000000)))) (orderedInterval (941060905 / 1000000000000) (941061180 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2550109983166499 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17036255383 / 1000000000000) (-17036255382 / 1000000000000), orderedInterval (-26601339879 / 1000000000000) (-26601339878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2253099507204479 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33269829600 / 1000000000000) (-33269825565 / 1000000000000), orderedInterval (4859612551 / 1000000000000) (4859616585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (653036055959421 / 800000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7347219490 / 1000000000000) (7347219491 / 1000000000000), orderedInterval (26938175272 / 1000000000000) (26938175273 / 1000000000000)))) (orderedInterval (1895310325 / 1000000000000) (1895310599 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_chunkChecks0_2 :
    compactCertificate570.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1806332098188487 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-795786949 / 1000000000000) (-795786948 / 1000000000000), orderedInterval (37539113922 / 1000000000000) (37539113923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1531247724214607 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12932451018 / 1000000000000) (12932451019 / 1000000000000), orderedInterval (38658191932 / 1000000000000) (38658191933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (958183727702021 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51551933426 / 1000000000000) (51551933516 / 1000000000000), orderedInterval (-54518486 / 1000000000000) (-54518396 / 1000000000000)))) (orderedInterval (1073551268 / 1000000000000) (1073551382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (515314395533307 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50804433777 / 1000000000000) (-50804433776 / 1000000000000), orderedInterval (-48387911839 / 1000000000000) (-48387911838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1399178826800921 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40853324353 / 1000000000000) (-40853318218 / 1000000000000), orderedInterval (12346017965 / 1000000000000) (12346024101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1910459068519417 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28088206882 / 1000000000000) (28088206883 / 1000000000000), orderedInterval (23293701058 / 1000000000000) (23293701059 / 1000000000000)))) (orderedInterval (-287705056 / 1000000000000) (-287704864 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (807816272297979 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55829410467 / 1000000000000) (55829410766 / 1000000000000), orderedInterval (-6085262370 / 1000000000000) (-6085262072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3283728298272859 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27341951239 / 1000000000000) (-27341927560 / 1000000000000), orderedInterval (5298903958 / 1000000000000) (5298927638 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2193378321932981 / 4000000000000) 0 (IntervalRat.scale (883 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20592528104 / 1000000000000) (20592530206 / 1000000000000), orderedInterval (-27165283530 / 1000000000000) (-27165281429 / 1000000000000)))) (orderedInterval (-1301465498 / 1000000000000) (-1301463051 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_chunkChecks0 :
    compactCertificate570.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate570.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate570_chunkChecks0_0
    compactCertificate570_chunkChecks0_1 compactCertificate570_chunkChecks0_2

theorem compactCertificate570_chunkChecks1_0 :
    compactCertificate570.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (883 / 2) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23860866650 / 1000000000000) (23860871914 / 1000000000000), orderedInterval (-29566938673 / 1000000000000) (-29566933409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1300827606996583 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29627822445 / 1000000000000) (-29627806075 / 1000000000000), orderedInterval (32905499236 / 1000000000000) (32905515606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (420660920912839 / 800000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32121962169 / 1000000000000) (-32121923305 / 1000000000000), orderedInterval (13405287025 / 1000000000000) (13405325889 / 1000000000000)))) (orderedInterval (-10556563259 / 1000000000000) (-10556558310 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (379578251411381 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81105531701 / 1000000000000) (81105531705 / 1000000000000), orderedInterval (10996753204 / 1000000000000) (10996753208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1019600575388657 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46863425055 / 1000000000000) (-46863425054 / 1000000000000), orderedInterval (-17267277082 / 1000000000000) (-17267277081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2768413902738669 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29904215293 / 1000000000000) (29904225365 / 1000000000000), orderedInterval (-5078346639 / 1000000000000) (-5078336566 / 1000000000000)))) (orderedInterval (176298218 / 1000000000000) (176299402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2039201150778197 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35234116732 / 1000000000000) (35234118139 / 1000000000000), orderedInterval (-2740004458 / 1000000000000) (-2740003051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3494205928928681 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22328982800 / 1000000000000) (22328982802 / 1000000000000), orderedInterval (15159179810 / 1000000000000) (15159179812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2573816272297979 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6642413129 / 1000000000000) (-6642413128 / 1000000000000), orderedInterval (-30739876377 / 1000000000000) (-30739876376 / 1000000000000)))) (orderedInterval (-2007887999 / 1000000000000) (-2007887956 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_chunkChecks1_1 :
    compactCertificate570.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3948896048264117 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25388131763 / 1000000000000) (25388138517 / 1000000000000), orderedInterval (535758335 / 1000000000000) (535765089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2279896196466893 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28312823659 / 1000000000000) (-28312757849 / 1000000000000), orderedInterval (17781866398 / 1000000000000) (17781932209 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4045715808986737 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14605638107 / 1000000000000) (14605638108 / 1000000000000), orderedInterval (20391344649 / 1000000000000) (20391344650 / 1000000000000)))) (orderedInterval (8128724233 / 1000000000000) (8128733574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3780032505207253 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4493517035 / 1000000000000) (-4493517034 / 1000000000000), orderedInterval (-25560766223 / 1000000000000) (-25560766222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2697609559096549 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (7744622934 / 1000000000000) (7744622938 / 1000000000000), orderedInterval (-29737832137 / 1000000000000) (-29737832133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3058801726165971 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25211668196 / 1000000000000) (-25211624376 / 1000000000000), orderedInterval (14047908695 / 1000000000000) (14047952515 / 1000000000000)))) (orderedInterval (-3430966711 / 1000000000000) (-3430966240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2550109983166499 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17036255383 / 1000000000000) (-17036255382 / 1000000000000), orderedInterval (-26601339879 / 1000000000000) (-26601339878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2253099507204479 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33269829600 / 1000000000000) (-33269825565 / 1000000000000), orderedInterval (4859612551 / 1000000000000) (4859616585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (653036055959421 / 800000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7347219490 / 1000000000000) (7347219491 / 1000000000000), orderedInterval (26938175272 / 1000000000000) (26938175273 / 1000000000000)))) (orderedInterval (476859645 / 1000000000000) (476860001 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_chunkChecks1_2 :
    compactCertificate570.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1806332098188487 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-795786949 / 1000000000000) (-795786948 / 1000000000000), orderedInterval (37539113922 / 1000000000000) (37539113923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1531247724214607 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12932451018 / 1000000000000) (12932451019 / 1000000000000), orderedInterval (38658191932 / 1000000000000) (38658191933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (958183727702021 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51551933426 / 1000000000000) (51551933516 / 1000000000000), orderedInterval (-54518486 / 1000000000000) (-54518396 / 1000000000000)))) (orderedInterval (-8037459823 / 1000000000000) (-8037459718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (515314395533307 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50804433777 / 1000000000000) (-50804433776 / 1000000000000), orderedInterval (-48387911839 / 1000000000000) (-48387911838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1399178826800921 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40853324353 / 1000000000000) (-40853318218 / 1000000000000), orderedInterval (12346017965 / 1000000000000) (12346024101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1910459068519417 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28088206882 / 1000000000000) (28088206883 / 1000000000000), orderedInterval (23293701058 / 1000000000000) (23293701059 / 1000000000000)))) (orderedInterval (-1892428800 / 1000000000000) (-1892428641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (807816272297979 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55829410467 / 1000000000000) (55829410766 / 1000000000000), orderedInterval (-6085262370 / 1000000000000) (-6085262072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3283728298272859 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27341951239 / 1000000000000) (-27341927560 / 1000000000000), orderedInterval (5298903958 / 1000000000000) (5298927638 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2193378321932981 / 4000000000000) 1 (IntervalRat.scale (883 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20592528104 / 1000000000000) (20592530206 / 1000000000000), orderedInterval (-27165283530 / 1000000000000) (-27165281429 / 1000000000000)))) (orderedInterval (5511577403 / 1000000000000) (5511581650 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_chunkChecks1 :
    compactCertificate570.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate570.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate570_chunkChecks1_0
    compactCertificate570_chunkChecks1_1 compactCertificate570_chunkChecks1_2

theorem compactCertificate570_chunkChecks2_0 :
    compactCertificate570.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (883 / 2) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23860866650 / 1000000000000) (23860871914 / 1000000000000), orderedInterval (-29566938673 / 1000000000000) (-29566933409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1300827606996583 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29627822445 / 1000000000000) (-29627806075 / 1000000000000), orderedInterval (32905499236 / 1000000000000) (32905515606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (420660920912839 / 800000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32121962169 / 1000000000000) (-32121923305 / 1000000000000), orderedInterval (13405287025 / 1000000000000) (13405325889 / 1000000000000)))) (orderedInterval (-6610149850 / 1000000000000) (-6610144394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (379578251411381 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81105531701 / 1000000000000) (81105531705 / 1000000000000), orderedInterval (10996753204 / 1000000000000) (10996753208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1019600575388657 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46863425055 / 1000000000000) (-46863425054 / 1000000000000), orderedInterval (-17267277082 / 1000000000000) (-17267277081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2768413902738669 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29904215293 / 1000000000000) (29904225365 / 1000000000000), orderedInterval (-5078346639 / 1000000000000) (-5078336566 / 1000000000000)))) (orderedInterval (5834801936 / 1000000000000) (5834803782 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2039201150778197 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35234116732 / 1000000000000) (35234118139 / 1000000000000), orderedInterval (-2740004458 / 1000000000000) (-2740003051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3494205928928681 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22328982800 / 1000000000000) (22328982802 / 1000000000000), orderedInterval (15159179810 / 1000000000000) (15159179812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2573816272297979 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6642413129 / 1000000000000) (-6642413128 / 1000000000000), orderedInterval (-30739876377 / 1000000000000) (-30739876376 / 1000000000000)))) (orderedInterval (3041756629 / 1000000000000) (3041756707 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_chunkChecks2_1 :
    compactCertificate570.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3948896048264117 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25388131763 / 1000000000000) (25388138517 / 1000000000000), orderedInterval (535758335 / 1000000000000) (535765089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2279896196466893 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28312823659 / 1000000000000) (-28312757849 / 1000000000000), orderedInterval (17781866398 / 1000000000000) (17781932209 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4045715808986737 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14605638107 / 1000000000000) (14605638108 / 1000000000000), orderedInterval (20391344649 / 1000000000000) (20391344650 / 1000000000000)))) (orderedInterval (15136953865 / 1000000000000) (15136968790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3780032505207253 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4493517035 / 1000000000000) (-4493517034 / 1000000000000), orderedInterval (-25560766223 / 1000000000000) (-25560766222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2697609559096549 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (7744622934 / 1000000000000) (7744622938 / 1000000000000), orderedInterval (-29737832137 / 1000000000000) (-29737832133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3058801726165971 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25211668196 / 1000000000000) (-25211624376 / 1000000000000), orderedInterval (14047908695 / 1000000000000) (14047952515 / 1000000000000)))) (orderedInterval (-2455472445 / 1000000000000) (-2455471636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2550109983166499 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17036255383 / 1000000000000) (-17036255382 / 1000000000000), orderedInterval (-26601339879 / 1000000000000) (-26601339878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2253099507204479 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33269829600 / 1000000000000) (-33269825565 / 1000000000000), orderedInterval (4859612551 / 1000000000000) (4859616585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (653036055959421 / 800000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7347219490 / 1000000000000) (7347219491 / 1000000000000), orderedInterval (26938175272 / 1000000000000) (26938175273 / 1000000000000)))) (orderedInterval (-3332997346 / 1000000000000) (-3332996878 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_chunkChecks2_2 :
    compactCertificate570.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1806332098188487 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-795786949 / 1000000000000) (-795786948 / 1000000000000), orderedInterval (37539113922 / 1000000000000) (37539113923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1531247724214607 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12932451018 / 1000000000000) (12932451019 / 1000000000000), orderedInterval (38658191932 / 1000000000000) (38658191933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (958183727702021 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51551933426 / 1000000000000) (51551933516 / 1000000000000), orderedInterval (-54518486 / 1000000000000) (-54518396 / 1000000000000)))) (orderedInterval (-58668051 / 1000000000000) (-58667953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (515314395533307 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50804433777 / 1000000000000) (-50804433776 / 1000000000000), orderedInterval (-48387911839 / 1000000000000) (-48387911838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1399178826800921 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40853324353 / 1000000000000) (-40853318218 / 1000000000000), orderedInterval (12346017965 / 1000000000000) (12346024101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1910459068519417 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28088206882 / 1000000000000) (28088206883 / 1000000000000), orderedInterval (23293701058 / 1000000000000) (23293701059 / 1000000000000)))) (orderedInterval (1861845713 / 1000000000000) (1861845849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (807816272297979 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55829410467 / 1000000000000) (55829410766 / 1000000000000), orderedInterval (-6085262370 / 1000000000000) (-6085262072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3283728298272859 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27341951239 / 1000000000000) (-27341927560 / 1000000000000), orderedInterval (5298903958 / 1000000000000) (5298927638 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2193378321932981 / 4000000000000) 2 (IntervalRat.scale (883 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20592528104 / 1000000000000) (20592530206 / 1000000000000), orderedInterval (-27165283530 / 1000000000000) (-27165281429 / 1000000000000)))) (orderedInterval (-1817997447 / 1000000000000) (-1817989911 / 1000000000000))) = true
  rfl'

theorem compactCertificate570_chunkChecks2 :
    compactCertificate570.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate570.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate570_chunkChecks2_0
    compactCertificate570_chunkChecks2_1 compactCertificate570_chunkChecks2_2

theorem compactCertificate570_chunkChecks3_0 :
    compactCertificate570.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (883 / 2) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23860866650 / 1000000000000) (23860871914 / 1000000000000), orderedInterval (-29566938673 / 1000000000000) (-29566933409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1300827606996583 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29627822445 / 1000000000000) (-29627806075 / 1000000000000), orderedInterval (32905499236 / 1000000000000) (32905515606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (420660920912839 / 800000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32121962169 / 1000000000000) (-32121923305 / 1000000000000), orderedInterval (13405287025 / 1000000000000) (13405325889 / 1000000000000)))) (orderedInterval (10282719016 / 1000000000000) (10282725075 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (379578251411381 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81105531701 / 1000000000000) (81105531705 / 1000000000000), orderedInterval (10996753204 / 1000000000000) (10996753208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1019600575388657 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46863425055 / 1000000000000) (-46863425054 / 1000000000000), orderedInterval (-17267277082 / 1000000000000) (-17267277081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2768413902738669 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29904215293 / 1000000000000) (29904225365 / 1000000000000), orderedInterval (-5078346639 / 1000000000000) (-5078336566 / 1000000000000)))) (orderedInterval (-1281450365 / 1000000000000) (-1281447478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2039201150778197 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35234116732 / 1000000000000) (35234118139 / 1000000000000), orderedInterval (-2740004458 / 1000000000000) (-2740003051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3494205928928681 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22328982800 / 1000000000000) (22328982802 / 1000000000000), orderedInterval (15159179810 / 1000000000000) (15159179812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2573816272297979 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6642413129 / 1000000000000) (-6642413128 / 1000000000000), orderedInterval (-30739876377 / 1000000000000) (-30739876376 / 1000000000000)))) (orderedInterval (5914734107 / 1000000000000) (5914734247 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate570_chunkChecks3_1 :
    compactCertificate570.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3948896048264117 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25388131763 / 1000000000000) (25388138517 / 1000000000000), orderedInterval (535758335 / 1000000000000) (535765089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2279896196466893 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28312823659 / 1000000000000) (-28312757849 / 1000000000000), orderedInterval (17781866398 / 1000000000000) (17781932209 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4045715808986737 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14605638107 / 1000000000000) (14605638108 / 1000000000000), orderedInterval (20391344649 / 1000000000000) (20391344650 / 1000000000000)))) (orderedInterval (-36656461219 / 1000000000000) (-36656435573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3780032505207253 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4493517035 / 1000000000000) (-4493517034 / 1000000000000), orderedInterval (-25560766223 / 1000000000000) (-25560766222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2697609559096549 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (7744622934 / 1000000000000) (7744622938 / 1000000000000), orderedInterval (-29737832137 / 1000000000000) (-29737832133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3058801726165971 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25211668196 / 1000000000000) (-25211624376 / 1000000000000), orderedInterval (14047908695 / 1000000000000) (14047952515 / 1000000000000)))) (orderedInterval (5872659257 / 1000000000000) (5872660652 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2550109983166499 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17036255383 / 1000000000000) (-17036255382 / 1000000000000), orderedInterval (-26601339879 / 1000000000000) (-26601339878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2253099507204479 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33269829600 / 1000000000000) (-33269825565 / 1000000000000), orderedInterval (4859612551 / 1000000000000) (4859616585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (653036055959421 / 800000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7347219490 / 1000000000000) (7347219491 / 1000000000000), orderedInterval (26938175272 / 1000000000000) (26938175273 / 1000000000000)))) (orderedInterval (-2849387154 / 1000000000000) (-2849386533 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate570_chunkChecks3_2 :
    compactCertificate570.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1806332098188487 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-795786949 / 1000000000000) (-795786948 / 1000000000000), orderedInterval (37539113922 / 1000000000000) (37539113923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1531247724214607 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12932451018 / 1000000000000) (12932451019 / 1000000000000), orderedInterval (38658191932 / 1000000000000) (38658191933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (958183727702021 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51551933426 / 1000000000000) (51551933516 / 1000000000000), orderedInterval (-54518486 / 1000000000000) (-54518396 / 1000000000000)))) (orderedInterval (7849633359 / 1000000000000) (7849633455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (515314395533307 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50804433777 / 1000000000000) (-50804433776 / 1000000000000), orderedInterval (-48387911839 / 1000000000000) (-48387911838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1399178826800921 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40853324353 / 1000000000000) (-40853318218 / 1000000000000), orderedInterval (12346017965 / 1000000000000) (12346024101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1910459068519417 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28088206882 / 1000000000000) (28088206883 / 1000000000000), orderedInterval (23293701058 / 1000000000000) (23293701059 / 1000000000000)))) (orderedInterval (2372978916 / 1000000000000) (2372979034 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (807816272297979 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55829410467 / 1000000000000) (55829410766 / 1000000000000), orderedInterval (-6085262370 / 1000000000000) (-6085262072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3283728298272859 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27341951239 / 1000000000000) (-27341927560 / 1000000000000), orderedInterval (5298903958 / 1000000000000) (5298927638 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2193378321932981 / 4000000000000) 3 (IntervalRat.scale (883 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20592528104 / 1000000000000) (20592530206 / 1000000000000), orderedInterval (-27165283530 / 1000000000000) (-27165281429 / 1000000000000)))) (orderedInterval (-6984452957 / 1000000000000) (-6984439402 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate570_chunkChecks3 :
    compactCertificate570.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate570.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate570_chunkChecks3_0
    compactCertificate570_chunkChecks3_1 compactCertificate570_chunkChecks3_2

theorem compactCertificate570_chunkChecks4_0 :
    compactCertificate570.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (883 / 2) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (23860866650 / 1000000000000) (23860871914 / 1000000000000), orderedInterval (-29566938673 / 1000000000000) (-29566933409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1300827606996583 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29627822445 / 1000000000000) (-29627806075 / 1000000000000), orderedInterval (32905499236 / 1000000000000) (32905515606 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (420660920912839 / 800000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32121962169 / 1000000000000) (-32121923305 / 1000000000000), orderedInterval (13405287025 / 1000000000000) (13405325889 / 1000000000000)))) (orderedInterval (5537042853 / 1000000000000) (5537049655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (379578251411381 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81105531701 / 1000000000000) (81105531705 / 1000000000000), orderedInterval (10996753204 / 1000000000000) (10996753208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1019600575388657 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-46863425055 / 1000000000000) (-46863425054 / 1000000000000), orderedInterval (-17267277082 / 1000000000000) (-17267277081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2768413902738669 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29904215293 / 1000000000000) (29904225365 / 1000000000000), orderedInterval (-5078346639 / 1000000000000) (-5078336566 / 1000000000000)))) (orderedInterval (-13024244224 / 1000000000000) (-13024239695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2039201150778197 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (35234116732 / 1000000000000) (35234118139 / 1000000000000), orderedInterval (-2740004458 / 1000000000000) (-2740003051 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3494205928928681 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22328982800 / 1000000000000) (22328982802 / 1000000000000), orderedInterval (15159179810 / 1000000000000) (15159179812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2573816272297979 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6642413129 / 1000000000000) (-6642413128 / 1000000000000), orderedInterval (-30739876377 / 1000000000000) (-30739876376 / 1000000000000)))) (orderedInterval (-11306377779 / 1000000000000) (-11306377520 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate570_chunkChecks4_1 :
    compactCertificate570.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3948896048264117 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25388131763 / 1000000000000) (25388138517 / 1000000000000), orderedInterval (535758335 / 1000000000000) (535765089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2279896196466893 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28312823659 / 1000000000000) (-28312757849 / 1000000000000), orderedInterval (17781866398 / 1000000000000) (17781932209 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4045715808986737 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14605638107 / 1000000000000) (14605638108 / 1000000000000), orderedInterval (20391344649 / 1000000000000) (20391344650 / 1000000000000)))) (orderedInterval (-61252195205 / 1000000000000) (-61252147764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3780032505207253 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4493517035 / 1000000000000) (-4493517034 / 1000000000000), orderedInterval (-25560766223 / 1000000000000) (-25560766222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2697609559096549 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (7744622934 / 1000000000000) (7744622938 / 1000000000000), orderedInterval (-29737832137 / 1000000000000) (-29737832133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3058801726165971 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25211668196 / 1000000000000) (-25211624376 / 1000000000000), orderedInterval (14047908695 / 1000000000000) (14047952515 / 1000000000000)))) (orderedInterval (6811686024 / 1000000000000) (6811688443 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2550109983166499 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17036255383 / 1000000000000) (-17036255382 / 1000000000000), orderedInterval (-26601339879 / 1000000000000) (-26601339878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2253099507204479 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33269829600 / 1000000000000) (-33269825565 / 1000000000000), orderedInterval (4859612551 / 1000000000000) (4859616585 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (653036055959421 / 800000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7347219490 / 1000000000000) (7347219491 / 1000000000000), orderedInterval (26938175272 / 1000000000000) (26938175273 / 1000000000000)))) (orderedInterval (6400269881 / 1000000000000) (6400270717 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate570_chunkChecks4_2 :
    compactCertificate570.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1806332098188487 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-795786949 / 1000000000000) (-795786948 / 1000000000000), orderedInterval (37539113922 / 1000000000000) (37539113923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1531247724214607 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12932451018 / 1000000000000) (12932451019 / 1000000000000), orderedInterval (38658191932 / 1000000000000) (38658191933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (958183727702021 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51551933426 / 1000000000000) (51551933516 / 1000000000000), orderedInterval (-54518486 / 1000000000000) (-54518396 / 1000000000000)))) (orderedInterval (-164574911 / 1000000000000) (-164574817 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (515314395533307 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-50804433777 / 1000000000000) (-50804433776 / 1000000000000), orderedInterval (-48387911839 / 1000000000000) (-48387911838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1399178826800921 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40853324353 / 1000000000000) (-40853318218 / 1000000000000), orderedInterval (12346017965 / 1000000000000) (12346024101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1910459068519417 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28088206882 / 1000000000000) (28088206883 / 1000000000000), orderedInterval (23293701058 / 1000000000000) (23293701059 / 1000000000000)))) (orderedInterval (-2586967354 / 1000000000000) (-2586967248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (807816272297979 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (55829410467 / 1000000000000) (55829410766 / 1000000000000), orderedInterval (-6085262370 / 1000000000000) (-6085262072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3283728298272859 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27341951239 / 1000000000000) (-27341927560 / 1000000000000), orderedInterval (5298903958 / 1000000000000) (5298927638 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2193378321932981 / 4000000000000) 4 (IntervalRat.scale (883 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20592528104 / 1000000000000) (20592530206 / 1000000000000), orderedInterval (-27165283530 / 1000000000000) (-27165281429 / 1000000000000)))) (orderedInterval (17457914963 / 1000000000000) (17457939630 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate570_chunkChecks4 :
    compactCertificate570.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate570.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate570_chunkChecks4_0
    compactCertificate570_chunkChecks4_1 compactCertificate570_chunkChecks4_2

theorem compactCertificate570_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate570.chunkCheck r b = true :=
  compactCertificate570.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate570_chunkChecks0
    · exact compactCertificate570_chunkChecks1
    · exact compactCertificate570_chunkChecks2
    · exact compactCertificate570_chunkChecks3
    · exact compactCertificate570_chunkChecks4)

theorem compactCertificate570_coefficient0 :
    compactCertificate570.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate570_coefficient1 :
    compactCertificate570.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate570_coefficient2 :
    compactCertificate570.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate570_coefficient3 :
    compactCertificate570.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate570_coefficient4 :
    compactCertificate570.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate570_coefficients : ∀ r : Fin 5,
    compactCertificate570.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate570_coefficient0
  · exact compactCertificate570_coefficient1
  · exact compactCertificate570_coefficient2
  · exact compactCertificate570_coefficient3
  · exact compactCertificate570_coefficient4

theorem compactCertificate570_lower : (1 : ℚ) ≤ compactCertificate570.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate570, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate570_proves {t : ℝ} (ht : t ∈ compactCertificate570.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate570.proves compactCertificate570_states compactCertificate570_chunks
    compactCertificate570_coefficients compactCertificate570_lower ht

end Erdos232
