/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate586 : CompactCertificate where
  left := 457
  right := 458
  center := 915 / 2
  grid := fun i =>
    match i.val with
    | 0 => 146
    | 1 => 107
    | 2 => 174
    | 3 => 31
    | 4 => 84
    | 5 => 228
    | 6 => 168
    | 7 => 288
    | 8 => 212
    | 9 => 326
    | 10 => 188
    | 11 => 334
    | 12 => 312
    | 13 => 223
    | 14 => 252
    | 15 => 210
    | 16 => 186
    | 17 => 269
    | 18 => 149
    | 19 => 126
    | 20 => 79
    | 21 => 43
    | 22 => 115
    | 23 => 158
    | 24 => 67
    | 25 => 271
    | _ => 181
  point := fun i =>
    match i.val with
    | 0 => 915 / 2
    | 1 => 269593943465883 / 800000000000
    | 2 => 87181142159739 / 160000000000
    | 3 => 78666840326481 / 800000000000
    | 4 => 211310198523357 / 800000000000
    | 5 => 573748294678569 / 800000000000
    | 6 => 422620397046897 / 800000000000
    | 7 => 724167253673781 / 800000000000
    | 8 => 533418321438879 / 800000000000
    | 9 => 818400879764817 / 800000000000
    | 10 => 472503968237193 / 800000000000
    | 11 => 838466583289437 / 800000000000
    | 12 => 783404245133553 / 800000000000
    | 13 => 559074234784449 / 800000000000
    | 14 => 633930595570071 / 800000000000
    | 15 => 528505239999399 / 800000000000
    | 16 => 466950407495379 / 800000000000
    | 17 => 135340428358521 / 160000000000
    | 18 => 374358747416187 / 800000000000
    | 19 => 317348056094307 / 800000000000
    | 20 => 198581678561121 / 800000000000
    | 21 => 106797887183007 / 800000000000
    | 22 => 289977038850021 / 800000000000
    | 23 => 395938855650117 / 800000000000
    | 24 => 167418321438879 / 800000000000
    | 25 => 680546181861759 / 800000000000
    | _ => 454573310208081 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-14092521781 / 1000000000000) (-14092521636 / 1000000000000), orderedInterval (34554076325 / 1000000000000) (34554076470 / 1000000000000))
    | 1 => (orderedInterval (-43395271747 / 1000000000000) (-43395271369 / 1000000000000), orderedInterval (2507789530 / 1000000000000) (2507789908 / 1000000000000))
    | 2 => (orderedInterval (-28192112593 / 1000000000000) (-28192061071 / 1000000000000), orderedInterval (19353760389 / 1000000000000) (19353811911 / 1000000000000))
    | 3 => (orderedInterval (-79465158962 / 1000000000000) (-79465158665 / 1000000000000), orderedInterval (13025223775 / 1000000000000) (13025224071 / 1000000000000))
    | 4 => (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000))
    | 5 => (orderedInterval (29591139415 / 1000000000000) (29591146264 / 1000000000000), orderedInterval (-3488809442 / 1000000000000) (-3488802592 / 1000000000000))
    | 6 => (orderedInterval (33187402144 / 1000000000000) (33187402153 / 1000000000000), orderedInterval (10151239564 / 1000000000000) (10151239573 / 1000000000000))
    | 7 => (orderedInterval (24864516010 / 1000000000000) (24864516081 / 1000000000000), orderedInterval (9208009414 / 1000000000000) (9208009485 / 1000000000000))
    | 8 => (orderedInterval (30885261553 / 1000000000000) (30885262573 / 1000000000000), orderedInterval (913765444 / 1000000000000) (913766464 / 1000000000000))
    | 9 => (orderedInterval (-9086650202 / 1000000000000) (-9086650200 / 1000000000000), orderedInterval (23236722411 / 1000000000000) (23236722413 / 1000000000000))
    | 10 => (orderedInterval (23453485399 / 1000000000000) (23453485400 / 1000000000000), orderedInterval (22954037281 / 1000000000000) (22954037282 / 1000000000000))
    | 11 => (orderedInterval (-10126879686 / 1000000000000) (-10126879683 / 1000000000000), orderedInterval (22473915000 / 1000000000000) (22473915003 / 1000000000000))
    | 12 => (orderedInterval (-3465297325 / 1000000000000) (-3465297324 / 1000000000000), orderedInterval (25262367498 / 1000000000000) (25262367499 / 1000000000000))
    | 13 => (orderedInterval (24500469507 / 1000000000000) (24500490102 / 1000000000000), orderedInterval (-17643916863 / 1000000000000) (-17643896268 / 1000000000000))
    | 14 => (orderedInterval (28303398487 / 1000000000000) (28303400121 / 1000000000000), orderedInterval (1502364601 / 1000000000000) (1502366235 / 1000000000000))
    | 15 => (orderedInterval (30849974327 / 1000000000000) (30849979144 / 1000000000000), orderedInterval (-3477618280 / 1000000000000) (-3477613464 / 1000000000000))
    | 16 => (orderedInterval (4509040555 / 1000000000000) (4509040556 / 1000000000000), orderedInterval (32712402003 / 1000000000000) (32712402004 / 1000000000000))
    | 17 => (orderedInterval (-27433630749 / 1000000000000) (-27433626592 / 1000000000000), orderedInterval (117924251 / 1000000000000) (117928408 / 1000000000000))
    | 18 => (orderedInterval (-21916302243 / 1000000000000) (-21916302242 / 1000000000000), orderedInterval (-29643474607 / 1000000000000) (-29643474606 / 1000000000000))
    | 19 => (orderedInterval (39991597496 / 1000000000000) (39991598067 / 1000000000000), orderedInterval (-2399913476 / 1000000000000) (-2399912905 / 1000000000000))
    | 20 => (orderedInterval (-37239615348 / 1000000000000) (-37239615347 / 1000000000000), orderedInterval (-34245206537 / 1000000000000) (-34245206536 / 1000000000000))
    | 21 => (orderedInterval (49857272366 / 1000000000000) (49857348315 / 1000000000000), orderedInterval (-47967819116 / 1000000000000) (-47967743167 / 1000000000000))
    | 22 => (orderedInterval (-38561091080 / 1000000000000) (-38561071605 / 1000000000000), orderedInterval (16465779377 / 1000000000000) (16465798852 / 1000000000000))
    | 23 => (orderedInterval (-22072194641 / 1000000000000) (-22072191334 / 1000000000000), orderedInterval (28290965313 / 1000000000000) (28290968620 / 1000000000000))
    | 24 => (orderedInterval (22942517401 / 1000000000000) (22942518608 / 1000000000000), orderedInterval (-50211589307 / 1000000000000) (-50211588100 / 1000000000000))
    | 25 => (orderedInterval (-2632225337 / 1000000000000) (-2632225336 / 1000000000000), orderedInterval (-27227754425 / 1000000000000) (-27227754424 / 1000000000000))
    | _ => (orderedInterval (-12214601375 / 1000000000000) (-12214601374 / 1000000000000), orderedInterval (-31153108625 / 1000000000000) (-31153108624 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-7644487365 / 1000000000000) (-7644484248 / 1000000000000)
      | 1 => orderedInterval (294192459 / 1000000000000) (294193004 / 1000000000000)
      | 2 => orderedInterval (-20485337 / 1000000000000) (-20485284 / 1000000000000)
      | 3 => orderedInterval (1912702592 / 1000000000000) (1912702774 / 1000000000000)
      | 4 => orderedInterval (2236162391 / 1000000000000) (2236164401 / 1000000000000)
      | 5 => orderedInterval (-604201417 / 1000000000000) (-604201210 / 1000000000000)
      | 6 => orderedInterval (28382567 / 1000000000000) (28382715 / 1000000000000)
      | 7 => orderedInterval (1645795715 / 1000000000000) (1645797868 / 1000000000000)
      | _ => orderedInterval (2644356011 / 1000000000000) (2644356145 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15065857433 / 1000000000000) (15065861130 / 1000000000000)
      | 1 => orderedInterval (890513971 / 1000000000000) (890514798 / 1000000000000)
      | 2 => orderedInterval (-529759922 / 1000000000000) (-529759836 / 1000000000000)
      | 3 => orderedInterval (282074755 / 1000000000000) (282075133 / 1000000000000)
      | 4 => orderedInterval (-3537963261 / 1000000000000) (-3537960183 / 1000000000000)
      | 5 => orderedInterval (-2440771068 / 1000000000000) (-2440770727 / 1000000000000)
      | 6 => orderedInterval (4360899509 / 1000000000000) (4360899643 / 1000000000000)
      | 7 => orderedInterval (-2383056781 / 1000000000000) (-2383055697 / 1000000000000)
      | _ => orderedInterval (11242423221 / 1000000000000) (11242423402 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (8118895991 / 1000000000000) (8118900389 / 1000000000000)
      | 1 => orderedInterval (4615833899 / 1000000000000) (4615835184 / 1000000000000)
      | 2 => orderedInterval (1418042666 / 1000000000000) (1418042806 / 1000000000000)
      | 3 => orderedInterval (-3414473106 / 1000000000000) (-3414472297 / 1000000000000)
      | 4 => orderedInterval (-5255141097 / 1000000000000) (-5255136374 / 1000000000000)
      | 5 => orderedInterval (2083694923 / 1000000000000) (2083695498 / 1000000000000)
      | 6 => orderedInterval (-1617030485 / 1000000000000) (-1617030359 / 1000000000000)
      | 7 => orderedInterval (-2445202681 / 1000000000000) (-2445201936 / 1000000000000)
      | _ => orderedInterval (-4329570679 / 1000000000000) (-4329570414 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-15641706062 / 1000000000000) (-15641700838 / 1000000000000)
      | 1 => orderedInterval (-1141487845 / 1000000000000) (-1141485837 / 1000000000000)
      | 2 => orderedInterval (2128467384 / 1000000000000) (2128467622 / 1000000000000)
      | 3 => orderedInterval (4099289157 / 1000000000000) (4099290932 / 1000000000000)
      | 4 => orderedInterval (10470127023 / 1000000000000) (10470134266 / 1000000000000)
      | 5 => orderedInterval (3984850302 / 1000000000000) (3984851289 / 1000000000000)
      | 6 => orderedInterval (-4978902715 / 1000000000000) (-4978902595 / 1000000000000)
      | 7 => orderedInterval (2914081635 / 1000000000000) (2914082262 / 1000000000000)
      | _ => orderedInterval (-25408823635 / 1000000000000) (-25408823228 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-8965082334 / 1000000000000) (-8965076114 / 1000000000000)
      | 1 => orderedInterval (-12526193008 / 1000000000000) (-12526189860 / 1000000000000)
      | 2 => orderedInterval (-8395445806 / 1000000000000) (-8395445393 / 1000000000000)
      | 3 => orderedInterval (5522272709 / 1000000000000) (5522276649 / 1000000000000)
      | 4 => orderedInterval (12592138217 / 1000000000000) (12592149356 / 1000000000000)
      | 5 => orderedInterval (-7360531806 / 1000000000000) (-7360530086 / 1000000000000)
      | 6 => orderedInterval (2472807273 / 1000000000000) (2472807388 / 1000000000000)
      | 7 => orderedInterval (2642053434 / 1000000000000) (2642054021 / 1000000000000)
      | _ => orderedInterval (8131795536 / 1000000000000) (8131796189 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (492417616 / 1000000000000) (492426165 / 1000000000000)
    | 1 => orderedInterval (22950217857 / 1000000000000) (22950227663 / 1000000000000)
    | 2 => orderedInterval (-824950569 / 1000000000000) (-824937503 / 1000000000000)
    | 3 => orderedInterval (-23574104756 / 1000000000000) (-23574086127 / 1000000000000)
    | _ => orderedInterval (-5886185785 / 1000000000000) (-5886157850 / 1000000000000)

theorem compactCertificate586_stateChecks0 :
    compactCertificate586.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (915 / 2)) (orderedInterval (-14092521781 / 1000000000000) (-14092521636 / 1000000000000), orderedInterval (34554076325 / 1000000000000) (34554076470 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (269593943465883 / 800000000000)) (orderedInterval (-43395271747 / 1000000000000) (-43395271369 / 1000000000000), orderedInterval (2507789530 / 1000000000000) (2507789908 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (87181142159739 / 160000000000)) (orderedInterval (-28192112593 / 1000000000000) (-28192061071 / 1000000000000), orderedInterval (19353760389 / 1000000000000) (19353811911 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_stateChecks1 :
    compactCertificate586.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (78666840326481 / 800000000000)) (orderedInterval (-79465158962 / 1000000000000) (-79465158665 / 1000000000000), orderedInterval (13025223775 / 1000000000000) (13025224071 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (211310198523357 / 800000000000)) (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (573748294678569 / 800000000000)) (orderedInterval (29591139415 / 1000000000000) (29591146264 / 1000000000000), orderedInterval (-3488809442 / 1000000000000) (-3488802592 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_stateChecks2 :
    compactCertificate586.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (422620397046897 / 800000000000)) (orderedInterval (33187402144 / 1000000000000) (33187402153 / 1000000000000), orderedInterval (10151239564 / 1000000000000) (10151239573 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 288 12 (724167253673781 / 800000000000)) (orderedInterval (24864516010 / 1000000000000) (24864516081 / 1000000000000), orderedInterval (9208009414 / 1000000000000) (9208009485 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (533418321438879 / 800000000000)) (orderedInterval (30885261553 / 1000000000000) (30885262573 / 1000000000000), orderedInterval (913765444 / 1000000000000) (913766464 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_stateChecks3 :
    compactCertificate586.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 326 12 (818400879764817 / 800000000000)) (orderedInterval (-9086650202 / 1000000000000) (-9086650200 / 1000000000000), orderedInterval (23236722411 / 1000000000000) (23236722413 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (472503968237193 / 800000000000)) (orderedInterval (23453485399 / 1000000000000) (23453485400 / 1000000000000), orderedInterval (22954037281 / 1000000000000) (22954037282 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 334 12 (838466583289437 / 800000000000)) (orderedInterval (-10126879686 / 1000000000000) (-10126879683 / 1000000000000), orderedInterval (22473915000 / 1000000000000) (22473915003 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_stateChecks4 :
    compactCertificate586.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 312 12 (783404245133553 / 800000000000)) (orderedInterval (-3465297325 / 1000000000000) (-3465297324 / 1000000000000), orderedInterval (25262367498 / 1000000000000) (25262367499 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (559074234784449 / 800000000000)) (orderedInterval (24500469507 / 1000000000000) (24500490102 / 1000000000000), orderedInterval (-17643916863 / 1000000000000) (-17643896268 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 252 12 (633930595570071 / 800000000000)) (orderedInterval (28303398487 / 1000000000000) (28303400121 / 1000000000000), orderedInterval (1502364601 / 1000000000000) (1502366235 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_stateChecks5 :
    compactCertificate586.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (528505239999399 / 800000000000)) (orderedInterval (30849974327 / 1000000000000) (30849979144 / 1000000000000), orderedInterval (-3477618280 / 1000000000000) (-3477613464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (466950407495379 / 800000000000)) (orderedInterval (4509040555 / 1000000000000) (4509040556 / 1000000000000), orderedInterval (32712402003 / 1000000000000) (32712402004 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 269 12 (135340428358521 / 160000000000)) (orderedInterval (-27433630749 / 1000000000000) (-27433626592 / 1000000000000), orderedInterval (117924251 / 1000000000000) (117928408 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_stateChecks6 :
    compactCertificate586.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (374358747416187 / 800000000000)) (orderedInterval (-21916302243 / 1000000000000) (-21916302242 / 1000000000000), orderedInterval (-29643474607 / 1000000000000) (-29643474606 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (317348056094307 / 800000000000)) (orderedInterval (39991597496 / 1000000000000) (39991598067 / 1000000000000), orderedInterval (-2399913476 / 1000000000000) (-2399912905 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (198581678561121 / 800000000000)) (orderedInterval (-37239615348 / 1000000000000) (-37239615347 / 1000000000000), orderedInterval (-34245206537 / 1000000000000) (-34245206536 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_stateChecks7 :
    compactCertificate586.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (106797887183007 / 800000000000)) (orderedInterval (49857272366 / 1000000000000) (49857348315 / 1000000000000), orderedInterval (-47967819116 / 1000000000000) (-47967743167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (289977038850021 / 800000000000)) (orderedInterval (-38561091080 / 1000000000000) (-38561071605 / 1000000000000), orderedInterval (16465779377 / 1000000000000) (16465798852 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (395938855650117 / 800000000000)) (orderedInterval (-22072194641 / 1000000000000) (-22072191334 / 1000000000000), orderedInterval (28290965313 / 1000000000000) (28290968620 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_stateChecks8 :
    compactCertificate586.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (167418321438879 / 800000000000)) (orderedInterval (22942517401 / 1000000000000) (22942518608 / 1000000000000), orderedInterval (-50211589307 / 1000000000000) (-50211588100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 271 12 (680546181861759 / 800000000000)) (orderedInterval (-2632225337 / 1000000000000) (-2632225336 / 1000000000000), orderedInterval (-27227754425 / 1000000000000) (-27227754424 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (454573310208081 / 800000000000)) (orderedInterval (-12214601375 / 1000000000000) (-12214601374 / 1000000000000), orderedInterval (-31153108625 / 1000000000000) (-31153108624 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_states : ∀ j,
    BesselStateValid (compactCertificate586.point j) (compactCertificate586.state j) :=
  compactCertificate586.statesValid_of_checks3 compactCertificate586_stateChecks0
    compactCertificate586_stateChecks1 compactCertificate586_stateChecks2
    compactCertificate586_stateChecks3 compactCertificate586_stateChecks4
    compactCertificate586_stateChecks5 compactCertificate586_stateChecks6
    compactCertificate586_stateChecks7 compactCertificate586_stateChecks8

theorem compactCertificate586_chunkChecks0_0 :
    compactCertificate586.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (915 / 2) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-14092521781 / 1000000000000) (-14092521636 / 1000000000000), orderedInterval (34554076325 / 1000000000000) (34554076470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (269593943465883 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43395271747 / 1000000000000) (-43395271369 / 1000000000000), orderedInterval (2507789530 / 1000000000000) (2507789908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (87181142159739 / 160000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28192112593 / 1000000000000) (-28192061071 / 1000000000000), orderedInterval (19353760389 / 1000000000000) (19353811911 / 1000000000000)))) (orderedInterval (-7644487365 / 1000000000000) (-7644484248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (78666840326481 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79465158962 / 1000000000000) (-79465158665 / 1000000000000), orderedInterval (13025223775 / 1000000000000) (13025224071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (211310198523357 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (573748294678569 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29591139415 / 1000000000000) (29591146264 / 1000000000000), orderedInterval (-3488809442 / 1000000000000) (-3488802592 / 1000000000000)))) (orderedInterval (294192459 / 1000000000000) (294193004 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (422620397046897 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33187402144 / 1000000000000) (33187402153 / 1000000000000), orderedInterval (10151239564 / 1000000000000) (10151239573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (724167253673781 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24864516010 / 1000000000000) (24864516081 / 1000000000000), orderedInterval (9208009414 / 1000000000000) (9208009485 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (533418321438879 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30885261553 / 1000000000000) (30885262573 / 1000000000000), orderedInterval (913765444 / 1000000000000) (913766464 / 1000000000000)))) (orderedInterval (-20485337 / 1000000000000) (-20485284 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_chunkChecks0_1 :
    compactCertificate586.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (818400879764817 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9086650202 / 1000000000000) (-9086650200 / 1000000000000), orderedInterval (23236722411 / 1000000000000) (23236722413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (472503968237193 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23453485399 / 1000000000000) (23453485400 / 1000000000000), orderedInterval (22954037281 / 1000000000000) (22954037282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (838466583289437 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10126879686 / 1000000000000) (-10126879683 / 1000000000000), orderedInterval (22473915000 / 1000000000000) (22473915003 / 1000000000000)))) (orderedInterval (1912702592 / 1000000000000) (1912702774 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (783404245133553 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3465297325 / 1000000000000) (-3465297324 / 1000000000000), orderedInterval (25262367498 / 1000000000000) (25262367499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (559074234784449 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24500469507 / 1000000000000) (24500490102 / 1000000000000), orderedInterval (-17643916863 / 1000000000000) (-17643896268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (633930595570071 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28303398487 / 1000000000000) (28303400121 / 1000000000000), orderedInterval (1502364601 / 1000000000000) (1502366235 / 1000000000000)))) (orderedInterval (2236162391 / 1000000000000) (2236164401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (528505239999399 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30849974327 / 1000000000000) (30849979144 / 1000000000000), orderedInterval (-3477618280 / 1000000000000) (-3477613464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (466950407495379 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4509040555 / 1000000000000) (4509040556 / 1000000000000), orderedInterval (32712402003 / 1000000000000) (32712402004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (135340428358521 / 160000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27433630749 / 1000000000000) (-27433626592 / 1000000000000), orderedInterval (117924251 / 1000000000000) (117928408 / 1000000000000)))) (orderedInterval (-604201417 / 1000000000000) (-604201210 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_chunkChecks0_2 :
    compactCertificate586.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (374358747416187 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21916302243 / 1000000000000) (-21916302242 / 1000000000000), orderedInterval (-29643474607 / 1000000000000) (-29643474606 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (317348056094307 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39991597496 / 1000000000000) (39991598067 / 1000000000000), orderedInterval (-2399913476 / 1000000000000) (-2399912905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (198581678561121 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37239615348 / 1000000000000) (-37239615347 / 1000000000000), orderedInterval (-34245206537 / 1000000000000) (-34245206536 / 1000000000000)))) (orderedInterval (28382567 / 1000000000000) (28382715 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (106797887183007 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49857272366 / 1000000000000) (49857348315 / 1000000000000), orderedInterval (-47967819116 / 1000000000000) (-47967743167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (289977038850021 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38561091080 / 1000000000000) (-38561071605 / 1000000000000), orderedInterval (16465779377 / 1000000000000) (16465798852 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (395938855650117 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22072194641 / 1000000000000) (-22072191334 / 1000000000000), orderedInterval (28290965313 / 1000000000000) (28290968620 / 1000000000000)))) (orderedInterval (1645795715 / 1000000000000) (1645797868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (167418321438879 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (22942517401 / 1000000000000) (22942518608 / 1000000000000), orderedInterval (-50211589307 / 1000000000000) (-50211588100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (680546181861759 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2632225337 / 1000000000000) (-2632225336 / 1000000000000), orderedInterval (-27227754425 / 1000000000000) (-27227754424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (454573310208081 / 800000000000) 0 (IntervalRat.scale (915 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12214601375 / 1000000000000) (-12214601374 / 1000000000000), orderedInterval (-31153108625 / 1000000000000) (-31153108624 / 1000000000000)))) (orderedInterval (2644356011 / 1000000000000) (2644356145 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_chunkChecks0 :
    compactCertificate586.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate586.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate586_chunkChecks0_0
    compactCertificate586_chunkChecks0_1 compactCertificate586_chunkChecks0_2

theorem compactCertificate586_chunkChecks1_0 :
    compactCertificate586.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (915 / 2) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-14092521781 / 1000000000000) (-14092521636 / 1000000000000), orderedInterval (34554076325 / 1000000000000) (34554076470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (269593943465883 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43395271747 / 1000000000000) (-43395271369 / 1000000000000), orderedInterval (2507789530 / 1000000000000) (2507789908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (87181142159739 / 160000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28192112593 / 1000000000000) (-28192061071 / 1000000000000), orderedInterval (19353760389 / 1000000000000) (19353811911 / 1000000000000)))) (orderedInterval (15065857433 / 1000000000000) (15065861130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (78666840326481 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79465158962 / 1000000000000) (-79465158665 / 1000000000000), orderedInterval (13025223775 / 1000000000000) (13025224071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (211310198523357 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (573748294678569 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29591139415 / 1000000000000) (29591146264 / 1000000000000), orderedInterval (-3488809442 / 1000000000000) (-3488802592 / 1000000000000)))) (orderedInterval (890513971 / 1000000000000) (890514798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (422620397046897 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33187402144 / 1000000000000) (33187402153 / 1000000000000), orderedInterval (10151239564 / 1000000000000) (10151239573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (724167253673781 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24864516010 / 1000000000000) (24864516081 / 1000000000000), orderedInterval (9208009414 / 1000000000000) (9208009485 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (533418321438879 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30885261553 / 1000000000000) (30885262573 / 1000000000000), orderedInterval (913765444 / 1000000000000) (913766464 / 1000000000000)))) (orderedInterval (-529759922 / 1000000000000) (-529759836 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_chunkChecks1_1 :
    compactCertificate586.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (818400879764817 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9086650202 / 1000000000000) (-9086650200 / 1000000000000), orderedInterval (23236722411 / 1000000000000) (23236722413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (472503968237193 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23453485399 / 1000000000000) (23453485400 / 1000000000000), orderedInterval (22954037281 / 1000000000000) (22954037282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (838466583289437 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10126879686 / 1000000000000) (-10126879683 / 1000000000000), orderedInterval (22473915000 / 1000000000000) (22473915003 / 1000000000000)))) (orderedInterval (282074755 / 1000000000000) (282075133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (783404245133553 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3465297325 / 1000000000000) (-3465297324 / 1000000000000), orderedInterval (25262367498 / 1000000000000) (25262367499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (559074234784449 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24500469507 / 1000000000000) (24500490102 / 1000000000000), orderedInterval (-17643916863 / 1000000000000) (-17643896268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (633930595570071 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28303398487 / 1000000000000) (28303400121 / 1000000000000), orderedInterval (1502364601 / 1000000000000) (1502366235 / 1000000000000)))) (orderedInterval (-3537963261 / 1000000000000) (-3537960183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (528505239999399 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30849974327 / 1000000000000) (30849979144 / 1000000000000), orderedInterval (-3477618280 / 1000000000000) (-3477613464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (466950407495379 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4509040555 / 1000000000000) (4509040556 / 1000000000000), orderedInterval (32712402003 / 1000000000000) (32712402004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (135340428358521 / 160000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27433630749 / 1000000000000) (-27433626592 / 1000000000000), orderedInterval (117924251 / 1000000000000) (117928408 / 1000000000000)))) (orderedInterval (-2440771068 / 1000000000000) (-2440770727 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_chunkChecks1_2 :
    compactCertificate586.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (374358747416187 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21916302243 / 1000000000000) (-21916302242 / 1000000000000), orderedInterval (-29643474607 / 1000000000000) (-29643474606 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (317348056094307 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39991597496 / 1000000000000) (39991598067 / 1000000000000), orderedInterval (-2399913476 / 1000000000000) (-2399912905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (198581678561121 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37239615348 / 1000000000000) (-37239615347 / 1000000000000), orderedInterval (-34245206537 / 1000000000000) (-34245206536 / 1000000000000)))) (orderedInterval (4360899509 / 1000000000000) (4360899643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (106797887183007 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49857272366 / 1000000000000) (49857348315 / 1000000000000), orderedInterval (-47967819116 / 1000000000000) (-47967743167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (289977038850021 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38561091080 / 1000000000000) (-38561071605 / 1000000000000), orderedInterval (16465779377 / 1000000000000) (16465798852 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (395938855650117 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22072194641 / 1000000000000) (-22072191334 / 1000000000000), orderedInterval (28290965313 / 1000000000000) (28290968620 / 1000000000000)))) (orderedInterval (-2383056781 / 1000000000000) (-2383055697 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (167418321438879 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (22942517401 / 1000000000000) (22942518608 / 1000000000000), orderedInterval (-50211589307 / 1000000000000) (-50211588100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (680546181861759 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2632225337 / 1000000000000) (-2632225336 / 1000000000000), orderedInterval (-27227754425 / 1000000000000) (-27227754424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (454573310208081 / 800000000000) 1 (IntervalRat.scale (915 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12214601375 / 1000000000000) (-12214601374 / 1000000000000), orderedInterval (-31153108625 / 1000000000000) (-31153108624 / 1000000000000)))) (orderedInterval (11242423221 / 1000000000000) (11242423402 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_chunkChecks1 :
    compactCertificate586.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate586.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate586_chunkChecks1_0
    compactCertificate586_chunkChecks1_1 compactCertificate586_chunkChecks1_2

theorem compactCertificate586_chunkChecks2_0 :
    compactCertificate586.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (915 / 2) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-14092521781 / 1000000000000) (-14092521636 / 1000000000000), orderedInterval (34554076325 / 1000000000000) (34554076470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (269593943465883 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43395271747 / 1000000000000) (-43395271369 / 1000000000000), orderedInterval (2507789530 / 1000000000000) (2507789908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (87181142159739 / 160000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28192112593 / 1000000000000) (-28192061071 / 1000000000000), orderedInterval (19353760389 / 1000000000000) (19353811911 / 1000000000000)))) (orderedInterval (8118895991 / 1000000000000) (8118900389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (78666840326481 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79465158962 / 1000000000000) (-79465158665 / 1000000000000), orderedInterval (13025223775 / 1000000000000) (13025224071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (211310198523357 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (573748294678569 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29591139415 / 1000000000000) (29591146264 / 1000000000000), orderedInterval (-3488809442 / 1000000000000) (-3488802592 / 1000000000000)))) (orderedInterval (4615833899 / 1000000000000) (4615835184 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (422620397046897 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33187402144 / 1000000000000) (33187402153 / 1000000000000), orderedInterval (10151239564 / 1000000000000) (10151239573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (724167253673781 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24864516010 / 1000000000000) (24864516081 / 1000000000000), orderedInterval (9208009414 / 1000000000000) (9208009485 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (533418321438879 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30885261553 / 1000000000000) (30885262573 / 1000000000000), orderedInterval (913765444 / 1000000000000) (913766464 / 1000000000000)))) (orderedInterval (1418042666 / 1000000000000) (1418042806 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_chunkChecks2_1 :
    compactCertificate586.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (818400879764817 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9086650202 / 1000000000000) (-9086650200 / 1000000000000), orderedInterval (23236722411 / 1000000000000) (23236722413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (472503968237193 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23453485399 / 1000000000000) (23453485400 / 1000000000000), orderedInterval (22954037281 / 1000000000000) (22954037282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (838466583289437 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10126879686 / 1000000000000) (-10126879683 / 1000000000000), orderedInterval (22473915000 / 1000000000000) (22473915003 / 1000000000000)))) (orderedInterval (-3414473106 / 1000000000000) (-3414472297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (783404245133553 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3465297325 / 1000000000000) (-3465297324 / 1000000000000), orderedInterval (25262367498 / 1000000000000) (25262367499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (559074234784449 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24500469507 / 1000000000000) (24500490102 / 1000000000000), orderedInterval (-17643916863 / 1000000000000) (-17643896268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (633930595570071 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28303398487 / 1000000000000) (28303400121 / 1000000000000), orderedInterval (1502364601 / 1000000000000) (1502366235 / 1000000000000)))) (orderedInterval (-5255141097 / 1000000000000) (-5255136374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (528505239999399 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30849974327 / 1000000000000) (30849979144 / 1000000000000), orderedInterval (-3477618280 / 1000000000000) (-3477613464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (466950407495379 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4509040555 / 1000000000000) (4509040556 / 1000000000000), orderedInterval (32712402003 / 1000000000000) (32712402004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (135340428358521 / 160000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27433630749 / 1000000000000) (-27433626592 / 1000000000000), orderedInterval (117924251 / 1000000000000) (117928408 / 1000000000000)))) (orderedInterval (2083694923 / 1000000000000) (2083695498 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_chunkChecks2_2 :
    compactCertificate586.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (374358747416187 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21916302243 / 1000000000000) (-21916302242 / 1000000000000), orderedInterval (-29643474607 / 1000000000000) (-29643474606 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (317348056094307 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39991597496 / 1000000000000) (39991598067 / 1000000000000), orderedInterval (-2399913476 / 1000000000000) (-2399912905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (198581678561121 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37239615348 / 1000000000000) (-37239615347 / 1000000000000), orderedInterval (-34245206537 / 1000000000000) (-34245206536 / 1000000000000)))) (orderedInterval (-1617030485 / 1000000000000) (-1617030359 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (106797887183007 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49857272366 / 1000000000000) (49857348315 / 1000000000000), orderedInterval (-47967819116 / 1000000000000) (-47967743167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (289977038850021 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38561091080 / 1000000000000) (-38561071605 / 1000000000000), orderedInterval (16465779377 / 1000000000000) (16465798852 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (395938855650117 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22072194641 / 1000000000000) (-22072191334 / 1000000000000), orderedInterval (28290965313 / 1000000000000) (28290968620 / 1000000000000)))) (orderedInterval (-2445202681 / 1000000000000) (-2445201936 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (167418321438879 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (22942517401 / 1000000000000) (22942518608 / 1000000000000), orderedInterval (-50211589307 / 1000000000000) (-50211588100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (680546181861759 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2632225337 / 1000000000000) (-2632225336 / 1000000000000), orderedInterval (-27227754425 / 1000000000000) (-27227754424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (454573310208081 / 800000000000) 2 (IntervalRat.scale (915 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12214601375 / 1000000000000) (-12214601374 / 1000000000000), orderedInterval (-31153108625 / 1000000000000) (-31153108624 / 1000000000000)))) (orderedInterval (-4329570679 / 1000000000000) (-4329570414 / 1000000000000))) = true
  rfl'

theorem compactCertificate586_chunkChecks2 :
    compactCertificate586.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate586.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate586_chunkChecks2_0
    compactCertificate586_chunkChecks2_1 compactCertificate586_chunkChecks2_2

theorem compactCertificate586_chunkChecks3_0 :
    compactCertificate586.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (915 / 2) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-14092521781 / 1000000000000) (-14092521636 / 1000000000000), orderedInterval (34554076325 / 1000000000000) (34554076470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (269593943465883 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43395271747 / 1000000000000) (-43395271369 / 1000000000000), orderedInterval (2507789530 / 1000000000000) (2507789908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (87181142159739 / 160000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28192112593 / 1000000000000) (-28192061071 / 1000000000000), orderedInterval (19353760389 / 1000000000000) (19353811911 / 1000000000000)))) (orderedInterval (-15641706062 / 1000000000000) (-15641700838 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (78666840326481 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79465158962 / 1000000000000) (-79465158665 / 1000000000000), orderedInterval (13025223775 / 1000000000000) (13025224071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (211310198523357 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (573748294678569 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29591139415 / 1000000000000) (29591146264 / 1000000000000), orderedInterval (-3488809442 / 1000000000000) (-3488802592 / 1000000000000)))) (orderedInterval (-1141487845 / 1000000000000) (-1141485837 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (422620397046897 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33187402144 / 1000000000000) (33187402153 / 1000000000000), orderedInterval (10151239564 / 1000000000000) (10151239573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (724167253673781 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24864516010 / 1000000000000) (24864516081 / 1000000000000), orderedInterval (9208009414 / 1000000000000) (9208009485 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (533418321438879 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30885261553 / 1000000000000) (30885262573 / 1000000000000), orderedInterval (913765444 / 1000000000000) (913766464 / 1000000000000)))) (orderedInterval (2128467384 / 1000000000000) (2128467622 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate586_chunkChecks3_1 :
    compactCertificate586.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (818400879764817 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9086650202 / 1000000000000) (-9086650200 / 1000000000000), orderedInterval (23236722411 / 1000000000000) (23236722413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (472503968237193 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23453485399 / 1000000000000) (23453485400 / 1000000000000), orderedInterval (22954037281 / 1000000000000) (22954037282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (838466583289437 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10126879686 / 1000000000000) (-10126879683 / 1000000000000), orderedInterval (22473915000 / 1000000000000) (22473915003 / 1000000000000)))) (orderedInterval (4099289157 / 1000000000000) (4099290932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (783404245133553 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3465297325 / 1000000000000) (-3465297324 / 1000000000000), orderedInterval (25262367498 / 1000000000000) (25262367499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (559074234784449 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24500469507 / 1000000000000) (24500490102 / 1000000000000), orderedInterval (-17643916863 / 1000000000000) (-17643896268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (633930595570071 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28303398487 / 1000000000000) (28303400121 / 1000000000000), orderedInterval (1502364601 / 1000000000000) (1502366235 / 1000000000000)))) (orderedInterval (10470127023 / 1000000000000) (10470134266 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (528505239999399 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30849974327 / 1000000000000) (30849979144 / 1000000000000), orderedInterval (-3477618280 / 1000000000000) (-3477613464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (466950407495379 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4509040555 / 1000000000000) (4509040556 / 1000000000000), orderedInterval (32712402003 / 1000000000000) (32712402004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (135340428358521 / 160000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27433630749 / 1000000000000) (-27433626592 / 1000000000000), orderedInterval (117924251 / 1000000000000) (117928408 / 1000000000000)))) (orderedInterval (3984850302 / 1000000000000) (3984851289 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate586_chunkChecks3_2 :
    compactCertificate586.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (374358747416187 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21916302243 / 1000000000000) (-21916302242 / 1000000000000), orderedInterval (-29643474607 / 1000000000000) (-29643474606 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (317348056094307 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39991597496 / 1000000000000) (39991598067 / 1000000000000), orderedInterval (-2399913476 / 1000000000000) (-2399912905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (198581678561121 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37239615348 / 1000000000000) (-37239615347 / 1000000000000), orderedInterval (-34245206537 / 1000000000000) (-34245206536 / 1000000000000)))) (orderedInterval (-4978902715 / 1000000000000) (-4978902595 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (106797887183007 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49857272366 / 1000000000000) (49857348315 / 1000000000000), orderedInterval (-47967819116 / 1000000000000) (-47967743167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (289977038850021 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38561091080 / 1000000000000) (-38561071605 / 1000000000000), orderedInterval (16465779377 / 1000000000000) (16465798852 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (395938855650117 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22072194641 / 1000000000000) (-22072191334 / 1000000000000), orderedInterval (28290965313 / 1000000000000) (28290968620 / 1000000000000)))) (orderedInterval (2914081635 / 1000000000000) (2914082262 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (167418321438879 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (22942517401 / 1000000000000) (22942518608 / 1000000000000), orderedInterval (-50211589307 / 1000000000000) (-50211588100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (680546181861759 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2632225337 / 1000000000000) (-2632225336 / 1000000000000), orderedInterval (-27227754425 / 1000000000000) (-27227754424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (454573310208081 / 800000000000) 3 (IntervalRat.scale (915 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12214601375 / 1000000000000) (-12214601374 / 1000000000000), orderedInterval (-31153108625 / 1000000000000) (-31153108624 / 1000000000000)))) (orderedInterval (-25408823635 / 1000000000000) (-25408823228 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate586_chunkChecks3 :
    compactCertificate586.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate586.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate586_chunkChecks3_0
    compactCertificate586_chunkChecks3_1 compactCertificate586_chunkChecks3_2

theorem compactCertificate586_chunkChecks4_0 :
    compactCertificate586.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (915 / 2) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-14092521781 / 1000000000000) (-14092521636 / 1000000000000), orderedInterval (34554076325 / 1000000000000) (34554076470 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (269593943465883 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43395271747 / 1000000000000) (-43395271369 / 1000000000000), orderedInterval (2507789530 / 1000000000000) (2507789908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (87181142159739 / 160000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28192112593 / 1000000000000) (-28192061071 / 1000000000000), orderedInterval (19353760389 / 1000000000000) (19353811911 / 1000000000000)))) (orderedInterval (-8965082334 / 1000000000000) (-8965076114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (78666840326481 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79465158962 / 1000000000000) (-79465158665 / 1000000000000), orderedInterval (13025223775 / 1000000000000) (13025224071 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (211310198523357 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (573748294678569 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29591139415 / 1000000000000) (29591146264 / 1000000000000), orderedInterval (-3488809442 / 1000000000000) (-3488802592 / 1000000000000)))) (orderedInterval (-12526193008 / 1000000000000) (-12526189860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (422620397046897 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33187402144 / 1000000000000) (33187402153 / 1000000000000), orderedInterval (10151239564 / 1000000000000) (10151239573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (724167253673781 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24864516010 / 1000000000000) (24864516081 / 1000000000000), orderedInterval (9208009414 / 1000000000000) (9208009485 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (533418321438879 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30885261553 / 1000000000000) (30885262573 / 1000000000000), orderedInterval (913765444 / 1000000000000) (913766464 / 1000000000000)))) (orderedInterval (-8395445806 / 1000000000000) (-8395445393 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate586_chunkChecks4_1 :
    compactCertificate586.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (818400879764817 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9086650202 / 1000000000000) (-9086650200 / 1000000000000), orderedInterval (23236722411 / 1000000000000) (23236722413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (472503968237193 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (23453485399 / 1000000000000) (23453485400 / 1000000000000), orderedInterval (22954037281 / 1000000000000) (22954037282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (838466583289437 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10126879686 / 1000000000000) (-10126879683 / 1000000000000), orderedInterval (22473915000 / 1000000000000) (22473915003 / 1000000000000)))) (orderedInterval (5522272709 / 1000000000000) (5522276649 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (783404245133553 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3465297325 / 1000000000000) (-3465297324 / 1000000000000), orderedInterval (25262367498 / 1000000000000) (25262367499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (559074234784449 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24500469507 / 1000000000000) (24500490102 / 1000000000000), orderedInterval (-17643916863 / 1000000000000) (-17643896268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (633930595570071 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28303398487 / 1000000000000) (28303400121 / 1000000000000), orderedInterval (1502364601 / 1000000000000) (1502366235 / 1000000000000)))) (orderedInterval (12592138217 / 1000000000000) (12592149356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (528505239999399 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30849974327 / 1000000000000) (30849979144 / 1000000000000), orderedInterval (-3477618280 / 1000000000000) (-3477613464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (466950407495379 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4509040555 / 1000000000000) (4509040556 / 1000000000000), orderedInterval (32712402003 / 1000000000000) (32712402004 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (135340428358521 / 160000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27433630749 / 1000000000000) (-27433626592 / 1000000000000), orderedInterval (117924251 / 1000000000000) (117928408 / 1000000000000)))) (orderedInterval (-7360531806 / 1000000000000) (-7360530086 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate586_chunkChecks4_2 :
    compactCertificate586.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (374358747416187 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21916302243 / 1000000000000) (-21916302242 / 1000000000000), orderedInterval (-29643474607 / 1000000000000) (-29643474606 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (317348056094307 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (39991597496 / 1000000000000) (39991598067 / 1000000000000), orderedInterval (-2399913476 / 1000000000000) (-2399912905 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (198581678561121 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37239615348 / 1000000000000) (-37239615347 / 1000000000000), orderedInterval (-34245206537 / 1000000000000) (-34245206536 / 1000000000000)))) (orderedInterval (2472807273 / 1000000000000) (2472807388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (106797887183007 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49857272366 / 1000000000000) (49857348315 / 1000000000000), orderedInterval (-47967819116 / 1000000000000) (-47967743167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (289977038850021 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38561091080 / 1000000000000) (-38561071605 / 1000000000000), orderedInterval (16465779377 / 1000000000000) (16465798852 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (395938855650117 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22072194641 / 1000000000000) (-22072191334 / 1000000000000), orderedInterval (28290965313 / 1000000000000) (28290968620 / 1000000000000)))) (orderedInterval (2642053434 / 1000000000000) (2642054021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (167418321438879 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (22942517401 / 1000000000000) (22942518608 / 1000000000000), orderedInterval (-50211589307 / 1000000000000) (-50211588100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (680546181861759 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2632225337 / 1000000000000) (-2632225336 / 1000000000000), orderedInterval (-27227754425 / 1000000000000) (-27227754424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (454573310208081 / 800000000000) 4 (IntervalRat.scale (915 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-12214601375 / 1000000000000) (-12214601374 / 1000000000000), orderedInterval (-31153108625 / 1000000000000) (-31153108624 / 1000000000000)))) (orderedInterval (8131795536 / 1000000000000) (8131796189 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate586_chunkChecks4 :
    compactCertificate586.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate586.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate586_chunkChecks4_0
    compactCertificate586_chunkChecks4_1 compactCertificate586_chunkChecks4_2

theorem compactCertificate586_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate586.chunkCheck r b = true :=
  compactCertificate586.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate586_chunkChecks0
    · exact compactCertificate586_chunkChecks1
    · exact compactCertificate586_chunkChecks2
    · exact compactCertificate586_chunkChecks3
    · exact compactCertificate586_chunkChecks4)

theorem compactCertificate586_coefficient0 :
    compactCertificate586.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate586_coefficient1 :
    compactCertificate586.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate586_coefficient2 :
    compactCertificate586.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate586_coefficient3 :
    compactCertificate586.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate586_coefficient4 :
    compactCertificate586.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate586_coefficients : ∀ r : Fin 5,
    compactCertificate586.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate586_coefficient0
  · exact compactCertificate586_coefficient1
  · exact compactCertificate586_coefficient2
  · exact compactCertificate586_coefficient3
  · exact compactCertificate586_coefficient4

theorem compactCertificate586_lower : (1 : ℚ) ≤ compactCertificate586.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate586, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate586_proves {t : ℝ} (ht : t ∈ compactCertificate586.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate586.proves compactCertificate586_states compactCertificate586_chunks
    compactCertificate586_coefficients compactCertificate586_lower ht

end Erdos232
