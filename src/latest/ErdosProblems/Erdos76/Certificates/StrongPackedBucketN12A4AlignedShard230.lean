/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard230

/-! Decode-only alignment checks for n=12, a=4, records 29440--29567. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard230

open PackedBucketCertificate

def missing29440 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5621337173553840128
theorem maskCheck29440 :
    checkMaskFor missing29440 StrongPackedBucketN12A4Shard230.record29440 = true := by
  decide

def missing29441 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5873538752686587904
theorem maskCheck29441 :
    checkMaskFor missing29441 StrongPackedBucketN12A4Shard230.record29441 = true := by
  decide

def missing29442 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5945596346724515840
theorem maskCheck29442 :
    checkMaskFor missing29442 StrongPackedBucketN12A4Shard230.record29442 = true := by
  decide

def missing29443 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6089711534800371712
theorem maskCheck29443 :
    checkMaskFor missing29443 StrongPackedBucketN12A4Shard230.record29443 = true := by
  decide

def missing29444 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6197797925857263616
theorem maskCheck29444 :
    checkMaskFor missing29444 StrongPackedBucketN12A4Shard230.record29444 = true := by
  decide

def missing29445 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8107324167862353920
theorem maskCheck29445 :
    checkMaskFor missing29445 StrongPackedBucketN12A4Shard230.record29445 = true := by
  decide

def missing29446 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8215410558919245824
theorem maskCheck29446 :
    checkMaskFor missing29446 StrongPackedBucketN12A4Shard230.record29446 = true := by
  decide

def missing29447 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13943989284934516736
theorem maskCheck29447 :
    checkMaskFor missing29447 StrongPackedBucketN12A4Shard230.record29447 = true := by
  decide

def missing29448 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14052075675991408640
theorem maskCheck29448 :
    checkMaskFor missing29448 StrongPackedBucketN12A4Shard230.record29448 = true := by
  decide

def missing29449 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37146534565147312128
theorem maskCheck29449 :
    checkMaskFor missing29449 StrongPackedBucketN12A4Shard230.record29449 = true := by
  decide

def missing29450 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37290649753223168000
theorem maskCheck29450 :
    checkMaskFor missing29450 StrongPackedBucketN12A4Shard230.record29450 = true := by
  decide

def missing29451 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37795052911488663552
theorem maskCheck29451 :
    checkMaskFor missing29451 StrongPackedBucketN12A4Shard230.record29451 = true := by
  decide

def missing29452 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38155340881678303232
theorem maskCheck29452 :
    checkMaskFor missing29452 StrongPackedBucketN12A4Shard230.record29452 = true := by
  decide

def missing29453 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38371513663792087040
theorem maskCheck29453 :
    checkMaskFor missing29453 StrongPackedBucketN12A4Shard230.record29453 = true := by
  decide

def missing29454 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38911945619076546560
theorem maskCheck29454 :
    checkMaskFor missing29454 StrongPackedBucketN12A4Shard230.record29454 = true := by
  decide

def missing29455 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40389126296854069248
theorem maskCheck29455 :
    checkMaskFor missing29455 StrongPackedBucketN12A4Shard230.record29455 = true := by
  decide

def missing29456 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40641327875986817024
theorem maskCheck29456 :
    checkMaskFor missing29456 StrongPackedBucketN12A4Shard230.record29456 = true := by
  decide

def missing29457 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41614105395498844160
theorem maskCheck29457 :
    checkMaskFor missing29457 StrongPackedBucketN12A4Shard230.record29457 = true := by
  decide

def missing29458 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41686162989536772096
theorem maskCheck29458 :
    checkMaskFor missing29458 StrongPackedBucketN12A4Shard230.record29458 = true := by
  decide

def missing29459 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41830278177612627968
theorem maskCheck29459 :
    checkMaskFor missing29459 StrongPackedBucketN12A4Shard230.record29459 = true := by
  decide

def missing29460 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41938364568669519872
theorem maskCheck29460 :
    checkMaskFor missing29460 StrongPackedBucketN12A4Shard230.record29460 = true := by
  decide

def missing29461 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42694969306067763200
theorem maskCheck29461 :
    checkMaskFor missing29461 StrongPackedBucketN12A4Shard230.record29461 = true := by
  decide

def missing29462 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42803055697124655104
theorem maskCheck29462 :
    checkMaskFor missing29462 StrongPackedBucketN12A4Shard230.record29462 = true := by
  decide

def missing29463 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 254172317635051520
theorem maskCheck29463 :
    checkMaskFor missing29463 StrongPackedBucketN12A4Shard230.record29463 = true := by
  decide

def missing29464 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 398287505710907392
theorem maskCheck29464 :
    checkMaskFor missing29464 StrongPackedBucketN12A4Shard230.record29464 = true := by
  decide

def missing29465 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2019583371564285952
theorem maskCheck29465 :
    checkMaskFor missing29465 StrongPackedBucketN12A4Shard230.record29465 = true := by
  decide

def missing29466 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2415900138772889600
theorem maskCheck29466 :
    checkMaskFor missing29466 StrongPackedBucketN12A4Shard230.record29466 = true := by
  decide

def missing29467 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3172504876171132928
theorem maskCheck29467 :
    checkMaskFor missing29467 StrongPackedBucketN12A4Shard230.record29467 = true := by
  decide

def missing29468 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4721743147986583552
theorem maskCheck29468 :
    checkMaskFor missing29468 StrongPackedBucketN12A4Shard230.record29468 = true := by
  decide

def missing29469 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4793800742024511488
theorem maskCheck29469 :
    checkMaskFor missing29469 StrongPackedBucketN12A4Shard230.record29469 = true := by
  decide

def missing29470 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5046002321157259264
theorem maskCheck29470 :
    checkMaskFor missing29470 StrongPackedBucketN12A4Shard230.record29470 = true := by
  decide

def missing29471 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7063614954219241472
theorem maskCheck29471 :
    checkMaskFor missing29471 StrongPackedBucketN12A4Shard230.record29471 = true := by
  decide

def missing29472 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 540854856292761600
theorem maskCheck29472 :
    checkMaskFor missing29472 StrongPackedBucketN12A4Shard230.record29472 = true := by
  decide

def missing29473 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 829085232444473344
theorem maskCheck29473 :
    checkMaskFor missing29473 StrongPackedBucketN12A4Shard230.record29473 = true := by
  decide

def missing29474 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1837891548975464448
theorem maskCheck29474 :
    checkMaskFor missing29474 StrongPackedBucketN12A4Shard230.record29474 = true := by
  decide

def missing29475 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1945977940032356352
theorem maskCheck29475 :
    checkMaskFor missing29475 StrongPackedBucketN12A4Shard230.record29475 = true := by
  decide

def missing29476 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4071676964151230464
theorem maskCheck29476 :
    checkMaskFor missing29476 StrongPackedBucketN12A4Shard230.record29476 = true := by
  decide

def missing29477 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4864310498568437760
theorem maskCheck29477 :
    checkMaskFor missing29477 StrongPackedBucketN12A4Shard230.record29477 = true := by
  decide

def missing29478 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5080483280682221568
theorem maskCheck29478 :
    checkMaskFor missing29478 StrongPackedBucketN12A4Shard230.record29478 = true := by
  decide

def missing29479 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5296656062796005376
theorem maskCheck29479 :
    checkMaskFor missing29479 StrongPackedBucketN12A4Shard230.record29479 = true := by
  decide

def missing29480 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5368713656833933312
theorem maskCheck29480 :
    checkMaskFor missing29480 StrongPackedBucketN12A4Shard230.record29480 = true := by
  decide

def missing29481 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5404742453852897280
theorem maskCheck29481 :
    checkMaskFor missing29481 StrongPackedBucketN12A4Shard230.record29481 = true := by
  decide

def missing29482 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5620915235966681088
theorem maskCheck29482 :
    checkMaskFor missing29482 StrongPackedBucketN12A4Shard230.record29482 = true := by
  decide

def missing29483 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6377519973364924416
theorem maskCheck29483 :
    checkMaskFor missing29483 StrongPackedBucketN12A4Shard230.record29483 = true := by
  decide

def missing29484 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6485606364421816320
theorem maskCheck29484 :
    checkMaskFor missing29484 StrongPackedBucketN12A4Shard230.record29484 = true := by
  decide

def missing29485 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13943567347347357696
theorem maskCheck29485 :
    checkMaskFor missing29485 StrongPackedBucketN12A4Shard230.record29485 = true := by
  decide

def missing29486 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14051653738404249600
theorem maskCheck29486 :
    checkMaskFor missing29486 StrongPackedBucketN12A4Shard230.record29486 = true := by
  decide

def missing29487 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14159740129461141504
theorem maskCheck29487 :
    checkMaskFor missing29487 StrongPackedBucketN12A4Shard230.record29487 = true := by
  decide

def missing29488 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14195768926480105472
theorem maskCheck29488 :
    checkMaskFor missing29488 StrongPackedBucketN12A4Shard230.record29488 = true := by
  decide

def missing29489 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27886711793686413312
theorem maskCheck29489 :
    checkMaskFor missing29489 StrongPackedBucketN12A4Shard230.record29489 = true := by
  decide

def missing29490 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 541136331269472256
theorem maskCheck29490 :
    checkMaskFor missing29490 StrongPackedBucketN12A4Shard230.record29490 = true := by
  decide

def missing29491 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 973481895497039872
theorem maskCheck29491 :
    checkMaskFor missing29491 StrongPackedBucketN12A4Shard230.record29491 = true := by
  decide

def missing29492 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081568286553931776
theorem maskCheck29492 :
    checkMaskFor missing29492 StrongPackedBucketN12A4Shard230.record29492 = true := by
  decide

def missing29493 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1405827459724607488
theorem maskCheck29493 :
    checkMaskFor missing29493 StrongPackedBucketN12A4Shard230.record29493 = true := by
  decide

def missing29494 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1549942647800463360
theorem maskCheck29494 :
    checkMaskFor missing29494 StrongPackedBucketN12A4Shard230.record29494 = true := by
  decide

def missing29495 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1622000241838391296
theorem maskCheck29495 :
    checkMaskFor missing29495 StrongPackedBucketN12A4Shard230.record29495 = true := by
  decide

def missing29496 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1658029038857355264
theorem maskCheck29496 :
    checkMaskFor missing29496 StrongPackedBucketN12A4Shard230.record29496 = true := by
  decide

def missing29497 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2054345806065958912
theorem maskCheck29497 :
    checkMaskFor missing29497 StrongPackedBucketN12A4Shard230.record29497 = true := by
  decide

def missing29498 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2090374603084922880
theorem maskCheck29498 :
    checkMaskFor missing29498 StrongPackedBucketN12A4Shard230.record29498 = true := by
  decide

def missing29499 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3567555280862445568
theorem maskCheck29499 :
    checkMaskFor missing29499 StrongPackedBucketN12A4Shard230.record29499 = true := by
  decide

def missing29500 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3675641671919337472
theorem maskCheck29500 :
    checkMaskFor missing29500 StrongPackedBucketN12A4Shard230.record29500 = true := by
  decide

def missing29501 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3783728062976229376
theorem maskCheck29501 :
    checkMaskFor missing29501 StrongPackedBucketN12A4Shard230.record29501 = true := by
  decide

def missing29502 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3819756859995193344
theorem maskCheck29502 :
    checkMaskFor missing29502 StrongPackedBucketN12A4Shard230.record29502 = true := by
  decide

def missing29503 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3891814454033121280
theorem maskCheck29503 :
    checkMaskFor missing29503 StrongPackedBucketN12A4Shard230.record29503 = true := by
  decide

def missing29504 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4324160018260688896
theorem maskCheck29504 :
    checkMaskFor missing29504 StrongPackedBucketN12A4Shard230.record29504 = true := by
  decide

def missing29505 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4864591973545148416
theorem maskCheck29505 :
    checkMaskFor missing29505 StrongPackedBucketN12A4Shard230.record29505 = true := by
  decide

def missing29506 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5008707161621004288
theorem maskCheck29506 :
    checkMaskFor missing29506 StrongPackedBucketN12A4Shard230.record29506 = true := by
  decide

def missing29507 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5080764755658932224
theorem maskCheck29507 :
    checkMaskFor missing29507 StrongPackedBucketN12A4Shard230.record29507 = true := by
  decide

def missing29508 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5116793552677896192
theorem maskCheck29508 :
    checkMaskFor missing29508 StrongPackedBucketN12A4Shard230.record29508 = true := by
  decide

def missing29509 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5296937537772716032
theorem maskCheck29509 :
    checkMaskFor missing29509 StrongPackedBucketN12A4Shard230.record29509 = true := by
  decide

def missing29510 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5368995131810643968
theorem maskCheck29510 :
    checkMaskFor missing29510 StrongPackedBucketN12A4Shard230.record29510 = true := by
  decide

def missing29511 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5405023928829607936
theorem maskCheck29511 :
    checkMaskFor missing29511 StrongPackedBucketN12A4Shard230.record29511 = true := by
  decide

def missing29512 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5513110319886499840
theorem maskCheck29512 :
    checkMaskFor missing29512 StrongPackedBucketN12A4Shard230.record29512 = true := by
  decide

def missing29513 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5549139116905463808
theorem maskCheck29513 :
    checkMaskFor missing29513 StrongPackedBucketN12A4Shard230.record29513 = true := by
  decide

def missing29514 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5621196710943391744
theorem maskCheck29514 :
    checkMaskFor missing29514 StrongPackedBucketN12A4Shard230.record29514 = true := by
  decide

def missing29515 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5873398290076139520
theorem maskCheck29515 :
    checkMaskFor missing29515 StrongPackedBucketN12A4Shard230.record29515 = true := by
  decide

def missing29516 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5945455884114067456
theorem maskCheck29516 :
    checkMaskFor missing29516 StrongPackedBucketN12A4Shard230.record29516 = true := by
  decide

def missing29517 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5981484681133031424
theorem maskCheck29517 :
    checkMaskFor missing29517 StrongPackedBucketN12A4Shard230.record29517 = true := by
  decide

def missing29518 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6089571072189923328
theorem maskCheck29518 :
    checkMaskFor missing29518 StrongPackedBucketN12A4Shard230.record29518 = true := by
  decide

def missing29519 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6125599869208887296
theorem maskCheck29519 :
    checkMaskFor missing29519 StrongPackedBucketN12A4Shard230.record29519 = true := by
  decide

def missing29520 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6197657463246815232
theorem maskCheck29520 :
    checkMaskFor missing29520 StrongPackedBucketN12A4Shard230.record29520 = true := by
  decide

def missing29521 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6377801448341635072
theorem maskCheck29521 :
    checkMaskFor missing29521 StrongPackedBucketN12A4Shard230.record29521 = true := by
  decide

def missing29522 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6413830245360599040
theorem maskCheck29522 :
    checkMaskFor missing29522 StrongPackedBucketN12A4Shard230.record29522 = true := by
  decide

def missing29523 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6485887839398526976
theorem maskCheck29523 :
    checkMaskFor missing29523 StrongPackedBucketN12A4Shard230.record29523 = true := by
  decide

def missing29524 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6630003027474382848
theorem maskCheck29524 :
    checkMaskFor missing29524 StrongPackedBucketN12A4Shard230.record29524 = true := by
  decide

def missing29525 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8107183705251905536
theorem maskCheck29525 :
    checkMaskFor missing29525 StrongPackedBucketN12A4Shard230.record29525 = true := by
  decide

def missing29526 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8143212502270869504
theorem maskCheck29526 :
    checkMaskFor missing29526 StrongPackedBucketN12A4Shard230.record29526 = true := by
  decide

def missing29527 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8215270096308797440
theorem maskCheck29527 :
    checkMaskFor missing29527 StrongPackedBucketN12A4Shard230.record29527 = true := by
  decide

def missing29528 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8359385284384653312
theorem maskCheck29528 :
    checkMaskFor missing29528 StrongPackedBucketN12A4Shard230.record29528 = true := by
  decide

def missing29529 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8647615660536365056
theorem maskCheck29529 :
    checkMaskFor missing29529 StrongPackedBucketN12A4Shard230.record29529 = true := by
  decide

def missing29530 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13943848822324068352
theorem maskCheck29530 :
    checkMaskFor missing29530 StrongPackedBucketN12A4Shard230.record29530 = true := by
  decide

def missing29531 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14051935213380960256
theorem maskCheck29531 :
    checkMaskFor missing29531 StrongPackedBucketN12A4Shard230.record29531 = true := by
  decide

def missing29532 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14160021604437852160
theorem maskCheck29532 :
    checkMaskFor missing29532 StrongPackedBucketN12A4Shard230.record29532 = true := by
  decide

def missing29533 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14196050401456816128
theorem maskCheck29533 :
    checkMaskFor missing29533 StrongPackedBucketN12A4Shard230.record29533 = true := by
  decide

def missing29534 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14268107995494744064
theorem maskCheck29534 :
    checkMaskFor missing29534 StrongPackedBucketN12A4Shard230.record29534 = true := by
  decide

def missing29535 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14700453559722311680
theorem maskCheck29535 :
    checkMaskFor missing29535 StrongPackedBucketN12A4Shard230.record29535 = true := by
  decide

def missing29536 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15024712732892987392
theorem maskCheck29536 :
    checkMaskFor missing29536 StrongPackedBucketN12A4Shard230.record29536 = true := by
  decide

def missing29537 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15060741529911951360
theorem maskCheck29537 :
    checkMaskFor missing29537 StrongPackedBucketN12A4Shard230.record29537 = true := by
  decide

def missing29538 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15276914312025735168
theorem maskCheck29538 :
    checkMaskFor missing29538 StrongPackedBucketN12A4Shard230.record29538 = true := by
  decide

def missing29539 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17294526945087717376
theorem maskCheck29539 :
    checkMaskFor missing29539 StrongPackedBucketN12A4Shard230.record29539 = true := by
  decide

def missing29540 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699650028827312128
theorem maskCheck29540 :
    checkMaskFor missing29540 StrongPackedBucketN12A4Shard230.record29540 = true := by
  decide

def missing29541 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18843765216903168000
theorem maskCheck29541 :
    checkMaskFor missing29541 StrongPackedBucketN12A4Shard230.record29541 = true := by
  decide

def missing29542 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18915822810941095936
theorem maskCheck29542 :
    checkMaskFor missing29542 StrongPackedBucketN12A4Shard230.record29542 = true := by
  decide

def missing29543 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18951851607960059904
theorem maskCheck29543 :
    checkMaskFor missing29543 StrongPackedBucketN12A4Shard230.record29543 = true := by
  decide

def missing29544 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19131995593054879744
theorem maskCheck29544 :
    checkMaskFor missing29544 StrongPackedBucketN12A4Shard230.record29544 = true := by
  decide

def missing29545 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19204053187092807680
theorem maskCheck29545 :
    checkMaskFor missing29545 StrongPackedBucketN12A4Shard230.record29545 = true := by
  decide

def missing29546 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19240081984111771648
theorem maskCheck29546 :
    checkMaskFor missing29546 StrongPackedBucketN12A4Shard230.record29546 = true := by
  decide

def missing29547 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19348168375168663552
theorem maskCheck29547 :
    checkMaskFor missing29547 StrongPackedBucketN12A4Shard230.record29547 = true := by
  decide

def missing29548 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19384197172187627520
theorem maskCheck29548 :
    checkMaskFor missing29548 StrongPackedBucketN12A4Shard230.record29548 = true := by
  decide

def missing29549 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19456254766225555456
theorem maskCheck29549 :
    checkMaskFor missing29549 StrongPackedBucketN12A4Shard230.record29549 = true := by
  decide

def missing29550 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19708456345358303232
theorem maskCheck29550 :
    checkMaskFor missing29550 StrongPackedBucketN12A4Shard230.record29550 = true := by
  decide

def missing29551 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19780513939396231168
theorem maskCheck29551 :
    checkMaskFor missing29551 StrongPackedBucketN12A4Shard230.record29551 = true := by
  decide

def missing29552 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19816542736415195136
theorem maskCheck29552 :
    checkMaskFor missing29552 StrongPackedBucketN12A4Shard230.record29552 = true := by
  decide

def missing29553 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19924629127472087040
theorem maskCheck29553 :
    checkMaskFor missing29553 StrongPackedBucketN12A4Shard230.record29553 = true := by
  decide

def missing29554 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19960657924491051008
theorem maskCheck29554 :
    checkMaskFor missing29554 StrongPackedBucketN12A4Shard230.record29554 = true := by
  decide

def missing29555 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20032715518528978944
theorem maskCheck29555 :
    checkMaskFor missing29555 StrongPackedBucketN12A4Shard230.record29555 = true := by
  decide

def missing29556 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20212859503623798784
theorem maskCheck29556 :
    checkMaskFor missing29556 StrongPackedBucketN12A4Shard230.record29556 = true := by
  decide

def missing29557 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20248888300642762752
theorem maskCheck29557 :
    checkMaskFor missing29557 StrongPackedBucketN12A4Shard230.record29557 = true := by
  decide

def missing29558 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20320945894680690688
theorem maskCheck29558 :
    checkMaskFor missing29558 StrongPackedBucketN12A4Shard230.record29558 = true := by
  decide

def missing29559 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20465061082756546560
theorem maskCheck29559 :
    checkMaskFor missing29559 StrongPackedBucketN12A4Shard230.record29559 = true := by
  decide

def missing29560 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21942241760534069248
theorem maskCheck29560 :
    checkMaskFor missing29560 StrongPackedBucketN12A4Shard230.record29560 = true := by
  decide

def missing29561 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21978270557553033216
theorem maskCheck29561 :
    checkMaskFor missing29561 StrongPackedBucketN12A4Shard230.record29561 = true := by
  decide

def missing29562 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22050328151590961152
theorem maskCheck29562 :
    checkMaskFor missing29562 StrongPackedBucketN12A4Shard230.record29562 = true := by
  decide

def missing29563 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22194443339666817024
theorem maskCheck29563 :
    checkMaskFor missing29563 StrongPackedBucketN12A4Shard230.record29563 = true := by
  decide

def missing29564 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22482673715818528768
theorem maskCheck29564 :
    checkMaskFor missing29564 StrongPackedBucketN12A4Shard230.record29564 = true := by
  decide

def missing29565 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23167220859178844160
theorem maskCheck29565 :
    checkMaskFor missing29565 StrongPackedBucketN12A4Shard230.record29565 = true := by
  decide

def missing29566 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23239278453216772096
theorem maskCheck29566 :
    checkMaskFor missing29566 StrongPackedBucketN12A4Shard230.record29566 = true := by
  decide

def missing29567 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23275307250235736064
theorem maskCheck29567 :
    checkMaskFor missing29567 StrongPackedBucketN12A4Shard230.record29567 = true := by
  decide

def missing29440_29441 : List (BitVec (edgeCount 12)) :=
  [missing29440]
abbrev records29440_29441 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29440]
theorem aligned29440_29441 :
    AlignedValid 12 4 missing29440_29441 records29440_29441 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29440
    maskCheck29440 AlignedValid.nil

def missing29441_29442 : List (BitVec (edgeCount 12)) :=
  [missing29441]
abbrev records29441_29442 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29441]
theorem aligned29441_29442 :
    AlignedValid 12 4 missing29441_29442 records29441_29442 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29441
    maskCheck29441 AlignedValid.nil

def missing29440_29442 : List (BitVec (edgeCount 12)) :=
  missing29440_29441 ++ missing29441_29442
abbrev records29440_29442 : List Blob :=
  records29440_29441 ++ records29441_29442
theorem aligned29440_29442 :
    AlignedValid 12 4 missing29440_29442 records29440_29442 :=
  aligned29440_29441.append aligned29441_29442

def missing29442_29443 : List (BitVec (edgeCount 12)) :=
  [missing29442]
abbrev records29442_29443 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29442]
theorem aligned29442_29443 :
    AlignedValid 12 4 missing29442_29443 records29442_29443 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29442
    maskCheck29442 AlignedValid.nil

def missing29443_29444 : List (BitVec (edgeCount 12)) :=
  [missing29443]
abbrev records29443_29444 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29443]
theorem aligned29443_29444 :
    AlignedValid 12 4 missing29443_29444 records29443_29444 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29443
    maskCheck29443 AlignedValid.nil

def missing29442_29444 : List (BitVec (edgeCount 12)) :=
  missing29442_29443 ++ missing29443_29444
abbrev records29442_29444 : List Blob :=
  records29442_29443 ++ records29443_29444
theorem aligned29442_29444 :
    AlignedValid 12 4 missing29442_29444 records29442_29444 :=
  aligned29442_29443.append aligned29443_29444

def missing29440_29444 : List (BitVec (edgeCount 12)) :=
  missing29440_29442 ++ missing29442_29444
abbrev records29440_29444 : List Blob :=
  records29440_29442 ++ records29442_29444
theorem aligned29440_29444 :
    AlignedValid 12 4 missing29440_29444 records29440_29444 :=
  aligned29440_29442.append aligned29442_29444

def missing29444_29445 : List (BitVec (edgeCount 12)) :=
  [missing29444]
abbrev records29444_29445 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29444]
theorem aligned29444_29445 :
    AlignedValid 12 4 missing29444_29445 records29444_29445 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29444
    maskCheck29444 AlignedValid.nil

def missing29445_29446 : List (BitVec (edgeCount 12)) :=
  [missing29445]
abbrev records29445_29446 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29445]
theorem aligned29445_29446 :
    AlignedValid 12 4 missing29445_29446 records29445_29446 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29445
    maskCheck29445 AlignedValid.nil

def missing29444_29446 : List (BitVec (edgeCount 12)) :=
  missing29444_29445 ++ missing29445_29446
abbrev records29444_29446 : List Blob :=
  records29444_29445 ++ records29445_29446
theorem aligned29444_29446 :
    AlignedValid 12 4 missing29444_29446 records29444_29446 :=
  aligned29444_29445.append aligned29445_29446

def missing29446_29447 : List (BitVec (edgeCount 12)) :=
  [missing29446]
abbrev records29446_29447 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29446]
theorem aligned29446_29447 :
    AlignedValid 12 4 missing29446_29447 records29446_29447 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29446
    maskCheck29446 AlignedValid.nil

def missing29447_29448 : List (BitVec (edgeCount 12)) :=
  [missing29447]
abbrev records29447_29448 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29447]
theorem aligned29447_29448 :
    AlignedValid 12 4 missing29447_29448 records29447_29448 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29447
    maskCheck29447 AlignedValid.nil

def missing29446_29448 : List (BitVec (edgeCount 12)) :=
  missing29446_29447 ++ missing29447_29448
abbrev records29446_29448 : List Blob :=
  records29446_29447 ++ records29447_29448
theorem aligned29446_29448 :
    AlignedValid 12 4 missing29446_29448 records29446_29448 :=
  aligned29446_29447.append aligned29447_29448

def missing29444_29448 : List (BitVec (edgeCount 12)) :=
  missing29444_29446 ++ missing29446_29448
abbrev records29444_29448 : List Blob :=
  records29444_29446 ++ records29446_29448
theorem aligned29444_29448 :
    AlignedValid 12 4 missing29444_29448 records29444_29448 :=
  aligned29444_29446.append aligned29446_29448

def missing29440_29448 : List (BitVec (edgeCount 12)) :=
  missing29440_29444 ++ missing29444_29448
abbrev records29440_29448 : List Blob :=
  records29440_29444 ++ records29444_29448
theorem aligned29440_29448 :
    AlignedValid 12 4 missing29440_29448 records29440_29448 :=
  aligned29440_29444.append aligned29444_29448

def missing29448_29449 : List (BitVec (edgeCount 12)) :=
  [missing29448]
abbrev records29448_29449 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29448]
theorem aligned29448_29449 :
    AlignedValid 12 4 missing29448_29449 records29448_29449 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29448
    maskCheck29448 AlignedValid.nil

def missing29449_29450 : List (BitVec (edgeCount 12)) :=
  [missing29449]
abbrev records29449_29450 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29449]
theorem aligned29449_29450 :
    AlignedValid 12 4 missing29449_29450 records29449_29450 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29449
    maskCheck29449 AlignedValid.nil

def missing29448_29450 : List (BitVec (edgeCount 12)) :=
  missing29448_29449 ++ missing29449_29450
abbrev records29448_29450 : List Blob :=
  records29448_29449 ++ records29449_29450
theorem aligned29448_29450 :
    AlignedValid 12 4 missing29448_29450 records29448_29450 :=
  aligned29448_29449.append aligned29449_29450

def missing29450_29451 : List (BitVec (edgeCount 12)) :=
  [missing29450]
abbrev records29450_29451 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29450]
theorem aligned29450_29451 :
    AlignedValid 12 4 missing29450_29451 records29450_29451 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29450
    maskCheck29450 AlignedValid.nil

def missing29451_29452 : List (BitVec (edgeCount 12)) :=
  [missing29451]
abbrev records29451_29452 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29451]
theorem aligned29451_29452 :
    AlignedValid 12 4 missing29451_29452 records29451_29452 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29451
    maskCheck29451 AlignedValid.nil

def missing29450_29452 : List (BitVec (edgeCount 12)) :=
  missing29450_29451 ++ missing29451_29452
abbrev records29450_29452 : List Blob :=
  records29450_29451 ++ records29451_29452
theorem aligned29450_29452 :
    AlignedValid 12 4 missing29450_29452 records29450_29452 :=
  aligned29450_29451.append aligned29451_29452

def missing29448_29452 : List (BitVec (edgeCount 12)) :=
  missing29448_29450 ++ missing29450_29452
abbrev records29448_29452 : List Blob :=
  records29448_29450 ++ records29450_29452
theorem aligned29448_29452 :
    AlignedValid 12 4 missing29448_29452 records29448_29452 :=
  aligned29448_29450.append aligned29450_29452

def missing29452_29453 : List (BitVec (edgeCount 12)) :=
  [missing29452]
abbrev records29452_29453 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29452]
theorem aligned29452_29453 :
    AlignedValid 12 4 missing29452_29453 records29452_29453 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29452
    maskCheck29452 AlignedValid.nil

def missing29453_29454 : List (BitVec (edgeCount 12)) :=
  [missing29453]
abbrev records29453_29454 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29453]
theorem aligned29453_29454 :
    AlignedValid 12 4 missing29453_29454 records29453_29454 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29453
    maskCheck29453 AlignedValid.nil

def missing29452_29454 : List (BitVec (edgeCount 12)) :=
  missing29452_29453 ++ missing29453_29454
abbrev records29452_29454 : List Blob :=
  records29452_29453 ++ records29453_29454
theorem aligned29452_29454 :
    AlignedValid 12 4 missing29452_29454 records29452_29454 :=
  aligned29452_29453.append aligned29453_29454

def missing29454_29455 : List (BitVec (edgeCount 12)) :=
  [missing29454]
abbrev records29454_29455 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29454]
theorem aligned29454_29455 :
    AlignedValid 12 4 missing29454_29455 records29454_29455 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29454
    maskCheck29454 AlignedValid.nil

def missing29455_29456 : List (BitVec (edgeCount 12)) :=
  [missing29455]
abbrev records29455_29456 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29455]
theorem aligned29455_29456 :
    AlignedValid 12 4 missing29455_29456 records29455_29456 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29455
    maskCheck29455 AlignedValid.nil

def missing29454_29456 : List (BitVec (edgeCount 12)) :=
  missing29454_29455 ++ missing29455_29456
abbrev records29454_29456 : List Blob :=
  records29454_29455 ++ records29455_29456
theorem aligned29454_29456 :
    AlignedValid 12 4 missing29454_29456 records29454_29456 :=
  aligned29454_29455.append aligned29455_29456

def missing29452_29456 : List (BitVec (edgeCount 12)) :=
  missing29452_29454 ++ missing29454_29456
abbrev records29452_29456 : List Blob :=
  records29452_29454 ++ records29454_29456
theorem aligned29452_29456 :
    AlignedValid 12 4 missing29452_29456 records29452_29456 :=
  aligned29452_29454.append aligned29454_29456

def missing29448_29456 : List (BitVec (edgeCount 12)) :=
  missing29448_29452 ++ missing29452_29456
abbrev records29448_29456 : List Blob :=
  records29448_29452 ++ records29452_29456
theorem aligned29448_29456 :
    AlignedValid 12 4 missing29448_29456 records29448_29456 :=
  aligned29448_29452.append aligned29452_29456

def missing29440_29456 : List (BitVec (edgeCount 12)) :=
  missing29440_29448 ++ missing29448_29456
abbrev records29440_29456 : List Blob :=
  records29440_29448 ++ records29448_29456
theorem aligned29440_29456 :
    AlignedValid 12 4 missing29440_29456 records29440_29456 :=
  aligned29440_29448.append aligned29448_29456

def missing29456_29457 : List (BitVec (edgeCount 12)) :=
  [missing29456]
abbrev records29456_29457 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29456]
theorem aligned29456_29457 :
    AlignedValid 12 4 missing29456_29457 records29456_29457 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29456
    maskCheck29456 AlignedValid.nil

def missing29457_29458 : List (BitVec (edgeCount 12)) :=
  [missing29457]
abbrev records29457_29458 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29457]
theorem aligned29457_29458 :
    AlignedValid 12 4 missing29457_29458 records29457_29458 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29457
    maskCheck29457 AlignedValid.nil

def missing29456_29458 : List (BitVec (edgeCount 12)) :=
  missing29456_29457 ++ missing29457_29458
abbrev records29456_29458 : List Blob :=
  records29456_29457 ++ records29457_29458
theorem aligned29456_29458 :
    AlignedValid 12 4 missing29456_29458 records29456_29458 :=
  aligned29456_29457.append aligned29457_29458

def missing29458_29459 : List (BitVec (edgeCount 12)) :=
  [missing29458]
abbrev records29458_29459 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29458]
theorem aligned29458_29459 :
    AlignedValid 12 4 missing29458_29459 records29458_29459 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29458
    maskCheck29458 AlignedValid.nil

def missing29459_29460 : List (BitVec (edgeCount 12)) :=
  [missing29459]
abbrev records29459_29460 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29459]
theorem aligned29459_29460 :
    AlignedValid 12 4 missing29459_29460 records29459_29460 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29459
    maskCheck29459 AlignedValid.nil

def missing29458_29460 : List (BitVec (edgeCount 12)) :=
  missing29458_29459 ++ missing29459_29460
abbrev records29458_29460 : List Blob :=
  records29458_29459 ++ records29459_29460
theorem aligned29458_29460 :
    AlignedValid 12 4 missing29458_29460 records29458_29460 :=
  aligned29458_29459.append aligned29459_29460

def missing29456_29460 : List (BitVec (edgeCount 12)) :=
  missing29456_29458 ++ missing29458_29460
abbrev records29456_29460 : List Blob :=
  records29456_29458 ++ records29458_29460
theorem aligned29456_29460 :
    AlignedValid 12 4 missing29456_29460 records29456_29460 :=
  aligned29456_29458.append aligned29458_29460

def missing29460_29461 : List (BitVec (edgeCount 12)) :=
  [missing29460]
abbrev records29460_29461 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29460]
theorem aligned29460_29461 :
    AlignedValid 12 4 missing29460_29461 records29460_29461 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29460
    maskCheck29460 AlignedValid.nil

def missing29461_29462 : List (BitVec (edgeCount 12)) :=
  [missing29461]
abbrev records29461_29462 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29461]
theorem aligned29461_29462 :
    AlignedValid 12 4 missing29461_29462 records29461_29462 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29461
    maskCheck29461 AlignedValid.nil

def missing29460_29462 : List (BitVec (edgeCount 12)) :=
  missing29460_29461 ++ missing29461_29462
abbrev records29460_29462 : List Blob :=
  records29460_29461 ++ records29461_29462
theorem aligned29460_29462 :
    AlignedValid 12 4 missing29460_29462 records29460_29462 :=
  aligned29460_29461.append aligned29461_29462

def missing29462_29463 : List (BitVec (edgeCount 12)) :=
  [missing29462]
abbrev records29462_29463 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29462]
theorem aligned29462_29463 :
    AlignedValid 12 4 missing29462_29463 records29462_29463 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29462
    maskCheck29462 AlignedValid.nil

def missing29463_29464 : List (BitVec (edgeCount 12)) :=
  [missing29463]
abbrev records29463_29464 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29463]
theorem aligned29463_29464 :
    AlignedValid 12 4 missing29463_29464 records29463_29464 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29463
    maskCheck29463 AlignedValid.nil

def missing29462_29464 : List (BitVec (edgeCount 12)) :=
  missing29462_29463 ++ missing29463_29464
abbrev records29462_29464 : List Blob :=
  records29462_29463 ++ records29463_29464
theorem aligned29462_29464 :
    AlignedValid 12 4 missing29462_29464 records29462_29464 :=
  aligned29462_29463.append aligned29463_29464

def missing29460_29464 : List (BitVec (edgeCount 12)) :=
  missing29460_29462 ++ missing29462_29464
abbrev records29460_29464 : List Blob :=
  records29460_29462 ++ records29462_29464
theorem aligned29460_29464 :
    AlignedValid 12 4 missing29460_29464 records29460_29464 :=
  aligned29460_29462.append aligned29462_29464

def missing29456_29464 : List (BitVec (edgeCount 12)) :=
  missing29456_29460 ++ missing29460_29464
abbrev records29456_29464 : List Blob :=
  records29456_29460 ++ records29460_29464
theorem aligned29456_29464 :
    AlignedValid 12 4 missing29456_29464 records29456_29464 :=
  aligned29456_29460.append aligned29460_29464

def missing29464_29465 : List (BitVec (edgeCount 12)) :=
  [missing29464]
abbrev records29464_29465 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29464]
theorem aligned29464_29465 :
    AlignedValid 12 4 missing29464_29465 records29464_29465 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29464
    maskCheck29464 AlignedValid.nil

def missing29465_29466 : List (BitVec (edgeCount 12)) :=
  [missing29465]
abbrev records29465_29466 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29465]
theorem aligned29465_29466 :
    AlignedValid 12 4 missing29465_29466 records29465_29466 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29465
    maskCheck29465 AlignedValid.nil

def missing29464_29466 : List (BitVec (edgeCount 12)) :=
  missing29464_29465 ++ missing29465_29466
abbrev records29464_29466 : List Blob :=
  records29464_29465 ++ records29465_29466
theorem aligned29464_29466 :
    AlignedValid 12 4 missing29464_29466 records29464_29466 :=
  aligned29464_29465.append aligned29465_29466

def missing29466_29467 : List (BitVec (edgeCount 12)) :=
  [missing29466]
abbrev records29466_29467 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29466]
theorem aligned29466_29467 :
    AlignedValid 12 4 missing29466_29467 records29466_29467 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29466
    maskCheck29466 AlignedValid.nil

def missing29467_29468 : List (BitVec (edgeCount 12)) :=
  [missing29467]
abbrev records29467_29468 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29467]
theorem aligned29467_29468 :
    AlignedValid 12 4 missing29467_29468 records29467_29468 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29467
    maskCheck29467 AlignedValid.nil

def missing29466_29468 : List (BitVec (edgeCount 12)) :=
  missing29466_29467 ++ missing29467_29468
abbrev records29466_29468 : List Blob :=
  records29466_29467 ++ records29467_29468
theorem aligned29466_29468 :
    AlignedValid 12 4 missing29466_29468 records29466_29468 :=
  aligned29466_29467.append aligned29467_29468

def missing29464_29468 : List (BitVec (edgeCount 12)) :=
  missing29464_29466 ++ missing29466_29468
abbrev records29464_29468 : List Blob :=
  records29464_29466 ++ records29466_29468
theorem aligned29464_29468 :
    AlignedValid 12 4 missing29464_29468 records29464_29468 :=
  aligned29464_29466.append aligned29466_29468

def missing29468_29469 : List (BitVec (edgeCount 12)) :=
  [missing29468]
abbrev records29468_29469 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29468]
theorem aligned29468_29469 :
    AlignedValid 12 4 missing29468_29469 records29468_29469 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29468
    maskCheck29468 AlignedValid.nil

def missing29469_29470 : List (BitVec (edgeCount 12)) :=
  [missing29469]
abbrev records29469_29470 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29469]
theorem aligned29469_29470 :
    AlignedValid 12 4 missing29469_29470 records29469_29470 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29469
    maskCheck29469 AlignedValid.nil

def missing29468_29470 : List (BitVec (edgeCount 12)) :=
  missing29468_29469 ++ missing29469_29470
abbrev records29468_29470 : List Blob :=
  records29468_29469 ++ records29469_29470
theorem aligned29468_29470 :
    AlignedValid 12 4 missing29468_29470 records29468_29470 :=
  aligned29468_29469.append aligned29469_29470

def missing29470_29471 : List (BitVec (edgeCount 12)) :=
  [missing29470]
abbrev records29470_29471 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29470]
theorem aligned29470_29471 :
    AlignedValid 12 4 missing29470_29471 records29470_29471 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29470
    maskCheck29470 AlignedValid.nil

def missing29471_29472 : List (BitVec (edgeCount 12)) :=
  [missing29471]
abbrev records29471_29472 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29471]
theorem aligned29471_29472 :
    AlignedValid 12 4 missing29471_29472 records29471_29472 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29471
    maskCheck29471 AlignedValid.nil

def missing29470_29472 : List (BitVec (edgeCount 12)) :=
  missing29470_29471 ++ missing29471_29472
abbrev records29470_29472 : List Blob :=
  records29470_29471 ++ records29471_29472
theorem aligned29470_29472 :
    AlignedValid 12 4 missing29470_29472 records29470_29472 :=
  aligned29470_29471.append aligned29471_29472

def missing29468_29472 : List (BitVec (edgeCount 12)) :=
  missing29468_29470 ++ missing29470_29472
abbrev records29468_29472 : List Blob :=
  records29468_29470 ++ records29470_29472
theorem aligned29468_29472 :
    AlignedValid 12 4 missing29468_29472 records29468_29472 :=
  aligned29468_29470.append aligned29470_29472

def missing29464_29472 : List (BitVec (edgeCount 12)) :=
  missing29464_29468 ++ missing29468_29472
abbrev records29464_29472 : List Blob :=
  records29464_29468 ++ records29468_29472
theorem aligned29464_29472 :
    AlignedValid 12 4 missing29464_29472 records29464_29472 :=
  aligned29464_29468.append aligned29468_29472

def missing29456_29472 : List (BitVec (edgeCount 12)) :=
  missing29456_29464 ++ missing29464_29472
abbrev records29456_29472 : List Blob :=
  records29456_29464 ++ records29464_29472
theorem aligned29456_29472 :
    AlignedValid 12 4 missing29456_29472 records29456_29472 :=
  aligned29456_29464.append aligned29464_29472

def missing29440_29472 : List (BitVec (edgeCount 12)) :=
  missing29440_29456 ++ missing29456_29472
abbrev records29440_29472 : List Blob :=
  records29440_29456 ++ records29456_29472
theorem aligned29440_29472 :
    AlignedValid 12 4 missing29440_29472 records29440_29472 :=
  aligned29440_29456.append aligned29456_29472

def missing29472_29473 : List (BitVec (edgeCount 12)) :=
  [missing29472]
abbrev records29472_29473 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29472]
theorem aligned29472_29473 :
    AlignedValid 12 4 missing29472_29473 records29472_29473 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29472
    maskCheck29472 AlignedValid.nil

def missing29473_29474 : List (BitVec (edgeCount 12)) :=
  [missing29473]
abbrev records29473_29474 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29473]
theorem aligned29473_29474 :
    AlignedValid 12 4 missing29473_29474 records29473_29474 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29473
    maskCheck29473 AlignedValid.nil

def missing29472_29474 : List (BitVec (edgeCount 12)) :=
  missing29472_29473 ++ missing29473_29474
abbrev records29472_29474 : List Blob :=
  records29472_29473 ++ records29473_29474
theorem aligned29472_29474 :
    AlignedValid 12 4 missing29472_29474 records29472_29474 :=
  aligned29472_29473.append aligned29473_29474

def missing29474_29475 : List (BitVec (edgeCount 12)) :=
  [missing29474]
abbrev records29474_29475 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29474]
theorem aligned29474_29475 :
    AlignedValid 12 4 missing29474_29475 records29474_29475 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29474
    maskCheck29474 AlignedValid.nil

def missing29475_29476 : List (BitVec (edgeCount 12)) :=
  [missing29475]
abbrev records29475_29476 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29475]
theorem aligned29475_29476 :
    AlignedValid 12 4 missing29475_29476 records29475_29476 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29475
    maskCheck29475 AlignedValid.nil

def missing29474_29476 : List (BitVec (edgeCount 12)) :=
  missing29474_29475 ++ missing29475_29476
abbrev records29474_29476 : List Blob :=
  records29474_29475 ++ records29475_29476
theorem aligned29474_29476 :
    AlignedValid 12 4 missing29474_29476 records29474_29476 :=
  aligned29474_29475.append aligned29475_29476

def missing29472_29476 : List (BitVec (edgeCount 12)) :=
  missing29472_29474 ++ missing29474_29476
abbrev records29472_29476 : List Blob :=
  records29472_29474 ++ records29474_29476
theorem aligned29472_29476 :
    AlignedValid 12 4 missing29472_29476 records29472_29476 :=
  aligned29472_29474.append aligned29474_29476

def missing29476_29477 : List (BitVec (edgeCount 12)) :=
  [missing29476]
abbrev records29476_29477 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29476]
theorem aligned29476_29477 :
    AlignedValid 12 4 missing29476_29477 records29476_29477 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29476
    maskCheck29476 AlignedValid.nil

def missing29477_29478 : List (BitVec (edgeCount 12)) :=
  [missing29477]
abbrev records29477_29478 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29477]
theorem aligned29477_29478 :
    AlignedValid 12 4 missing29477_29478 records29477_29478 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29477
    maskCheck29477 AlignedValid.nil

def missing29476_29478 : List (BitVec (edgeCount 12)) :=
  missing29476_29477 ++ missing29477_29478
abbrev records29476_29478 : List Blob :=
  records29476_29477 ++ records29477_29478
theorem aligned29476_29478 :
    AlignedValid 12 4 missing29476_29478 records29476_29478 :=
  aligned29476_29477.append aligned29477_29478

def missing29478_29479 : List (BitVec (edgeCount 12)) :=
  [missing29478]
abbrev records29478_29479 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29478]
theorem aligned29478_29479 :
    AlignedValid 12 4 missing29478_29479 records29478_29479 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29478
    maskCheck29478 AlignedValid.nil

def missing29479_29480 : List (BitVec (edgeCount 12)) :=
  [missing29479]
abbrev records29479_29480 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29479]
theorem aligned29479_29480 :
    AlignedValid 12 4 missing29479_29480 records29479_29480 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29479
    maskCheck29479 AlignedValid.nil

def missing29478_29480 : List (BitVec (edgeCount 12)) :=
  missing29478_29479 ++ missing29479_29480
abbrev records29478_29480 : List Blob :=
  records29478_29479 ++ records29479_29480
theorem aligned29478_29480 :
    AlignedValid 12 4 missing29478_29480 records29478_29480 :=
  aligned29478_29479.append aligned29479_29480

def missing29476_29480 : List (BitVec (edgeCount 12)) :=
  missing29476_29478 ++ missing29478_29480
abbrev records29476_29480 : List Blob :=
  records29476_29478 ++ records29478_29480
theorem aligned29476_29480 :
    AlignedValid 12 4 missing29476_29480 records29476_29480 :=
  aligned29476_29478.append aligned29478_29480

def missing29472_29480 : List (BitVec (edgeCount 12)) :=
  missing29472_29476 ++ missing29476_29480
abbrev records29472_29480 : List Blob :=
  records29472_29476 ++ records29476_29480
theorem aligned29472_29480 :
    AlignedValid 12 4 missing29472_29480 records29472_29480 :=
  aligned29472_29476.append aligned29476_29480

def missing29480_29481 : List (BitVec (edgeCount 12)) :=
  [missing29480]
abbrev records29480_29481 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29480]
theorem aligned29480_29481 :
    AlignedValid 12 4 missing29480_29481 records29480_29481 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29480
    maskCheck29480 AlignedValid.nil

def missing29481_29482 : List (BitVec (edgeCount 12)) :=
  [missing29481]
abbrev records29481_29482 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29481]
theorem aligned29481_29482 :
    AlignedValid 12 4 missing29481_29482 records29481_29482 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29481
    maskCheck29481 AlignedValid.nil

def missing29480_29482 : List (BitVec (edgeCount 12)) :=
  missing29480_29481 ++ missing29481_29482
abbrev records29480_29482 : List Blob :=
  records29480_29481 ++ records29481_29482
theorem aligned29480_29482 :
    AlignedValid 12 4 missing29480_29482 records29480_29482 :=
  aligned29480_29481.append aligned29481_29482

def missing29482_29483 : List (BitVec (edgeCount 12)) :=
  [missing29482]
abbrev records29482_29483 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29482]
theorem aligned29482_29483 :
    AlignedValid 12 4 missing29482_29483 records29482_29483 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29482
    maskCheck29482 AlignedValid.nil

def missing29483_29484 : List (BitVec (edgeCount 12)) :=
  [missing29483]
abbrev records29483_29484 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29483]
theorem aligned29483_29484 :
    AlignedValid 12 4 missing29483_29484 records29483_29484 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29483
    maskCheck29483 AlignedValid.nil

def missing29482_29484 : List (BitVec (edgeCount 12)) :=
  missing29482_29483 ++ missing29483_29484
abbrev records29482_29484 : List Blob :=
  records29482_29483 ++ records29483_29484
theorem aligned29482_29484 :
    AlignedValid 12 4 missing29482_29484 records29482_29484 :=
  aligned29482_29483.append aligned29483_29484

def missing29480_29484 : List (BitVec (edgeCount 12)) :=
  missing29480_29482 ++ missing29482_29484
abbrev records29480_29484 : List Blob :=
  records29480_29482 ++ records29482_29484
theorem aligned29480_29484 :
    AlignedValid 12 4 missing29480_29484 records29480_29484 :=
  aligned29480_29482.append aligned29482_29484

def missing29484_29485 : List (BitVec (edgeCount 12)) :=
  [missing29484]
abbrev records29484_29485 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29484]
theorem aligned29484_29485 :
    AlignedValid 12 4 missing29484_29485 records29484_29485 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29484
    maskCheck29484 AlignedValid.nil

def missing29485_29486 : List (BitVec (edgeCount 12)) :=
  [missing29485]
abbrev records29485_29486 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29485]
theorem aligned29485_29486 :
    AlignedValid 12 4 missing29485_29486 records29485_29486 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29485
    maskCheck29485 AlignedValid.nil

def missing29484_29486 : List (BitVec (edgeCount 12)) :=
  missing29484_29485 ++ missing29485_29486
abbrev records29484_29486 : List Blob :=
  records29484_29485 ++ records29485_29486
theorem aligned29484_29486 :
    AlignedValid 12 4 missing29484_29486 records29484_29486 :=
  aligned29484_29485.append aligned29485_29486

def missing29486_29487 : List (BitVec (edgeCount 12)) :=
  [missing29486]
abbrev records29486_29487 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29486]
theorem aligned29486_29487 :
    AlignedValid 12 4 missing29486_29487 records29486_29487 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29486
    maskCheck29486 AlignedValid.nil

def missing29487_29488 : List (BitVec (edgeCount 12)) :=
  [missing29487]
abbrev records29487_29488 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29487]
theorem aligned29487_29488 :
    AlignedValid 12 4 missing29487_29488 records29487_29488 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29487
    maskCheck29487 AlignedValid.nil

def missing29486_29488 : List (BitVec (edgeCount 12)) :=
  missing29486_29487 ++ missing29487_29488
abbrev records29486_29488 : List Blob :=
  records29486_29487 ++ records29487_29488
theorem aligned29486_29488 :
    AlignedValid 12 4 missing29486_29488 records29486_29488 :=
  aligned29486_29487.append aligned29487_29488

def missing29484_29488 : List (BitVec (edgeCount 12)) :=
  missing29484_29486 ++ missing29486_29488
abbrev records29484_29488 : List Blob :=
  records29484_29486 ++ records29486_29488
theorem aligned29484_29488 :
    AlignedValid 12 4 missing29484_29488 records29484_29488 :=
  aligned29484_29486.append aligned29486_29488

def missing29480_29488 : List (BitVec (edgeCount 12)) :=
  missing29480_29484 ++ missing29484_29488
abbrev records29480_29488 : List Blob :=
  records29480_29484 ++ records29484_29488
theorem aligned29480_29488 :
    AlignedValid 12 4 missing29480_29488 records29480_29488 :=
  aligned29480_29484.append aligned29484_29488

def missing29472_29488 : List (BitVec (edgeCount 12)) :=
  missing29472_29480 ++ missing29480_29488
abbrev records29472_29488 : List Blob :=
  records29472_29480 ++ records29480_29488
theorem aligned29472_29488 :
    AlignedValid 12 4 missing29472_29488 records29472_29488 :=
  aligned29472_29480.append aligned29480_29488

def missing29488_29489 : List (BitVec (edgeCount 12)) :=
  [missing29488]
abbrev records29488_29489 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29488]
theorem aligned29488_29489 :
    AlignedValid 12 4 missing29488_29489 records29488_29489 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29488
    maskCheck29488 AlignedValid.nil

def missing29489_29490 : List (BitVec (edgeCount 12)) :=
  [missing29489]
abbrev records29489_29490 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29489]
theorem aligned29489_29490 :
    AlignedValid 12 4 missing29489_29490 records29489_29490 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29489
    maskCheck29489 AlignedValid.nil

def missing29488_29490 : List (BitVec (edgeCount 12)) :=
  missing29488_29489 ++ missing29489_29490
abbrev records29488_29490 : List Blob :=
  records29488_29489 ++ records29489_29490
theorem aligned29488_29490 :
    AlignedValid 12 4 missing29488_29490 records29488_29490 :=
  aligned29488_29489.append aligned29489_29490

def missing29490_29491 : List (BitVec (edgeCount 12)) :=
  [missing29490]
abbrev records29490_29491 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29490]
theorem aligned29490_29491 :
    AlignedValid 12 4 missing29490_29491 records29490_29491 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29490
    maskCheck29490 AlignedValid.nil

def missing29491_29492 : List (BitVec (edgeCount 12)) :=
  [missing29491]
abbrev records29491_29492 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29491]
theorem aligned29491_29492 :
    AlignedValid 12 4 missing29491_29492 records29491_29492 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29491
    maskCheck29491 AlignedValid.nil

def missing29490_29492 : List (BitVec (edgeCount 12)) :=
  missing29490_29491 ++ missing29491_29492
abbrev records29490_29492 : List Blob :=
  records29490_29491 ++ records29491_29492
theorem aligned29490_29492 :
    AlignedValid 12 4 missing29490_29492 records29490_29492 :=
  aligned29490_29491.append aligned29491_29492

def missing29488_29492 : List (BitVec (edgeCount 12)) :=
  missing29488_29490 ++ missing29490_29492
abbrev records29488_29492 : List Blob :=
  records29488_29490 ++ records29490_29492
theorem aligned29488_29492 :
    AlignedValid 12 4 missing29488_29492 records29488_29492 :=
  aligned29488_29490.append aligned29490_29492

def missing29492_29493 : List (BitVec (edgeCount 12)) :=
  [missing29492]
abbrev records29492_29493 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29492]
theorem aligned29492_29493 :
    AlignedValid 12 4 missing29492_29493 records29492_29493 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29492
    maskCheck29492 AlignedValid.nil

def missing29493_29494 : List (BitVec (edgeCount 12)) :=
  [missing29493]
abbrev records29493_29494 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29493]
theorem aligned29493_29494 :
    AlignedValid 12 4 missing29493_29494 records29493_29494 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29493
    maskCheck29493 AlignedValid.nil

def missing29492_29494 : List (BitVec (edgeCount 12)) :=
  missing29492_29493 ++ missing29493_29494
abbrev records29492_29494 : List Blob :=
  records29492_29493 ++ records29493_29494
theorem aligned29492_29494 :
    AlignedValid 12 4 missing29492_29494 records29492_29494 :=
  aligned29492_29493.append aligned29493_29494

def missing29494_29495 : List (BitVec (edgeCount 12)) :=
  [missing29494]
abbrev records29494_29495 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29494]
theorem aligned29494_29495 :
    AlignedValid 12 4 missing29494_29495 records29494_29495 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29494
    maskCheck29494 AlignedValid.nil

def missing29495_29496 : List (BitVec (edgeCount 12)) :=
  [missing29495]
abbrev records29495_29496 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29495]
theorem aligned29495_29496 :
    AlignedValid 12 4 missing29495_29496 records29495_29496 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29495
    maskCheck29495 AlignedValid.nil

def missing29494_29496 : List (BitVec (edgeCount 12)) :=
  missing29494_29495 ++ missing29495_29496
abbrev records29494_29496 : List Blob :=
  records29494_29495 ++ records29495_29496
theorem aligned29494_29496 :
    AlignedValid 12 4 missing29494_29496 records29494_29496 :=
  aligned29494_29495.append aligned29495_29496

def missing29492_29496 : List (BitVec (edgeCount 12)) :=
  missing29492_29494 ++ missing29494_29496
abbrev records29492_29496 : List Blob :=
  records29492_29494 ++ records29494_29496
theorem aligned29492_29496 :
    AlignedValid 12 4 missing29492_29496 records29492_29496 :=
  aligned29492_29494.append aligned29494_29496

def missing29488_29496 : List (BitVec (edgeCount 12)) :=
  missing29488_29492 ++ missing29492_29496
abbrev records29488_29496 : List Blob :=
  records29488_29492 ++ records29492_29496
theorem aligned29488_29496 :
    AlignedValid 12 4 missing29488_29496 records29488_29496 :=
  aligned29488_29492.append aligned29492_29496

def missing29496_29497 : List (BitVec (edgeCount 12)) :=
  [missing29496]
abbrev records29496_29497 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29496]
theorem aligned29496_29497 :
    AlignedValid 12 4 missing29496_29497 records29496_29497 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29496
    maskCheck29496 AlignedValid.nil

def missing29497_29498 : List (BitVec (edgeCount 12)) :=
  [missing29497]
abbrev records29497_29498 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29497]
theorem aligned29497_29498 :
    AlignedValid 12 4 missing29497_29498 records29497_29498 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29497
    maskCheck29497 AlignedValid.nil

def missing29496_29498 : List (BitVec (edgeCount 12)) :=
  missing29496_29497 ++ missing29497_29498
abbrev records29496_29498 : List Blob :=
  records29496_29497 ++ records29497_29498
theorem aligned29496_29498 :
    AlignedValid 12 4 missing29496_29498 records29496_29498 :=
  aligned29496_29497.append aligned29497_29498

def missing29498_29499 : List (BitVec (edgeCount 12)) :=
  [missing29498]
abbrev records29498_29499 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29498]
theorem aligned29498_29499 :
    AlignedValid 12 4 missing29498_29499 records29498_29499 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29498
    maskCheck29498 AlignedValid.nil

def missing29499_29500 : List (BitVec (edgeCount 12)) :=
  [missing29499]
abbrev records29499_29500 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29499]
theorem aligned29499_29500 :
    AlignedValid 12 4 missing29499_29500 records29499_29500 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29499
    maskCheck29499 AlignedValid.nil

def missing29498_29500 : List (BitVec (edgeCount 12)) :=
  missing29498_29499 ++ missing29499_29500
abbrev records29498_29500 : List Blob :=
  records29498_29499 ++ records29499_29500
theorem aligned29498_29500 :
    AlignedValid 12 4 missing29498_29500 records29498_29500 :=
  aligned29498_29499.append aligned29499_29500

def missing29496_29500 : List (BitVec (edgeCount 12)) :=
  missing29496_29498 ++ missing29498_29500
abbrev records29496_29500 : List Blob :=
  records29496_29498 ++ records29498_29500
theorem aligned29496_29500 :
    AlignedValid 12 4 missing29496_29500 records29496_29500 :=
  aligned29496_29498.append aligned29498_29500

def missing29500_29501 : List (BitVec (edgeCount 12)) :=
  [missing29500]
abbrev records29500_29501 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29500]
theorem aligned29500_29501 :
    AlignedValid 12 4 missing29500_29501 records29500_29501 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29500
    maskCheck29500 AlignedValid.nil

def missing29501_29502 : List (BitVec (edgeCount 12)) :=
  [missing29501]
abbrev records29501_29502 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29501]
theorem aligned29501_29502 :
    AlignedValid 12 4 missing29501_29502 records29501_29502 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29501
    maskCheck29501 AlignedValid.nil

def missing29500_29502 : List (BitVec (edgeCount 12)) :=
  missing29500_29501 ++ missing29501_29502
abbrev records29500_29502 : List Blob :=
  records29500_29501 ++ records29501_29502
theorem aligned29500_29502 :
    AlignedValid 12 4 missing29500_29502 records29500_29502 :=
  aligned29500_29501.append aligned29501_29502

def missing29502_29503 : List (BitVec (edgeCount 12)) :=
  [missing29502]
abbrev records29502_29503 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29502]
theorem aligned29502_29503 :
    AlignedValid 12 4 missing29502_29503 records29502_29503 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29502
    maskCheck29502 AlignedValid.nil

def missing29503_29504 : List (BitVec (edgeCount 12)) :=
  [missing29503]
abbrev records29503_29504 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29503]
theorem aligned29503_29504 :
    AlignedValid 12 4 missing29503_29504 records29503_29504 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29503
    maskCheck29503 AlignedValid.nil

def missing29502_29504 : List (BitVec (edgeCount 12)) :=
  missing29502_29503 ++ missing29503_29504
abbrev records29502_29504 : List Blob :=
  records29502_29503 ++ records29503_29504
theorem aligned29502_29504 :
    AlignedValid 12 4 missing29502_29504 records29502_29504 :=
  aligned29502_29503.append aligned29503_29504

def missing29500_29504 : List (BitVec (edgeCount 12)) :=
  missing29500_29502 ++ missing29502_29504
abbrev records29500_29504 : List Blob :=
  records29500_29502 ++ records29502_29504
theorem aligned29500_29504 :
    AlignedValid 12 4 missing29500_29504 records29500_29504 :=
  aligned29500_29502.append aligned29502_29504

def missing29496_29504 : List (BitVec (edgeCount 12)) :=
  missing29496_29500 ++ missing29500_29504
abbrev records29496_29504 : List Blob :=
  records29496_29500 ++ records29500_29504
theorem aligned29496_29504 :
    AlignedValid 12 4 missing29496_29504 records29496_29504 :=
  aligned29496_29500.append aligned29500_29504

def missing29488_29504 : List (BitVec (edgeCount 12)) :=
  missing29488_29496 ++ missing29496_29504
abbrev records29488_29504 : List Blob :=
  records29488_29496 ++ records29496_29504
theorem aligned29488_29504 :
    AlignedValid 12 4 missing29488_29504 records29488_29504 :=
  aligned29488_29496.append aligned29496_29504

def missing29472_29504 : List (BitVec (edgeCount 12)) :=
  missing29472_29488 ++ missing29488_29504
abbrev records29472_29504 : List Blob :=
  records29472_29488 ++ records29488_29504
theorem aligned29472_29504 :
    AlignedValid 12 4 missing29472_29504 records29472_29504 :=
  aligned29472_29488.append aligned29488_29504

def missing29440_29504 : List (BitVec (edgeCount 12)) :=
  missing29440_29472 ++ missing29472_29504
abbrev records29440_29504 : List Blob :=
  records29440_29472 ++ records29472_29504
theorem aligned29440_29504 :
    AlignedValid 12 4 missing29440_29504 records29440_29504 :=
  aligned29440_29472.append aligned29472_29504

def missing29504_29505 : List (BitVec (edgeCount 12)) :=
  [missing29504]
abbrev records29504_29505 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29504]
theorem aligned29504_29505 :
    AlignedValid 12 4 missing29504_29505 records29504_29505 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29504
    maskCheck29504 AlignedValid.nil

def missing29505_29506 : List (BitVec (edgeCount 12)) :=
  [missing29505]
abbrev records29505_29506 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29505]
theorem aligned29505_29506 :
    AlignedValid 12 4 missing29505_29506 records29505_29506 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29505
    maskCheck29505 AlignedValid.nil

def missing29504_29506 : List (BitVec (edgeCount 12)) :=
  missing29504_29505 ++ missing29505_29506
abbrev records29504_29506 : List Blob :=
  records29504_29505 ++ records29505_29506
theorem aligned29504_29506 :
    AlignedValid 12 4 missing29504_29506 records29504_29506 :=
  aligned29504_29505.append aligned29505_29506

def missing29506_29507 : List (BitVec (edgeCount 12)) :=
  [missing29506]
abbrev records29506_29507 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29506]
theorem aligned29506_29507 :
    AlignedValid 12 4 missing29506_29507 records29506_29507 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29506
    maskCheck29506 AlignedValid.nil

def missing29507_29508 : List (BitVec (edgeCount 12)) :=
  [missing29507]
abbrev records29507_29508 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29507]
theorem aligned29507_29508 :
    AlignedValid 12 4 missing29507_29508 records29507_29508 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29507
    maskCheck29507 AlignedValid.nil

def missing29506_29508 : List (BitVec (edgeCount 12)) :=
  missing29506_29507 ++ missing29507_29508
abbrev records29506_29508 : List Blob :=
  records29506_29507 ++ records29507_29508
theorem aligned29506_29508 :
    AlignedValid 12 4 missing29506_29508 records29506_29508 :=
  aligned29506_29507.append aligned29507_29508

def missing29504_29508 : List (BitVec (edgeCount 12)) :=
  missing29504_29506 ++ missing29506_29508
abbrev records29504_29508 : List Blob :=
  records29504_29506 ++ records29506_29508
theorem aligned29504_29508 :
    AlignedValid 12 4 missing29504_29508 records29504_29508 :=
  aligned29504_29506.append aligned29506_29508

def missing29508_29509 : List (BitVec (edgeCount 12)) :=
  [missing29508]
abbrev records29508_29509 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29508]
theorem aligned29508_29509 :
    AlignedValid 12 4 missing29508_29509 records29508_29509 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29508
    maskCheck29508 AlignedValid.nil

def missing29509_29510 : List (BitVec (edgeCount 12)) :=
  [missing29509]
abbrev records29509_29510 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29509]
theorem aligned29509_29510 :
    AlignedValid 12 4 missing29509_29510 records29509_29510 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29509
    maskCheck29509 AlignedValid.nil

def missing29508_29510 : List (BitVec (edgeCount 12)) :=
  missing29508_29509 ++ missing29509_29510
abbrev records29508_29510 : List Blob :=
  records29508_29509 ++ records29509_29510
theorem aligned29508_29510 :
    AlignedValid 12 4 missing29508_29510 records29508_29510 :=
  aligned29508_29509.append aligned29509_29510

def missing29510_29511 : List (BitVec (edgeCount 12)) :=
  [missing29510]
abbrev records29510_29511 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29510]
theorem aligned29510_29511 :
    AlignedValid 12 4 missing29510_29511 records29510_29511 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29510
    maskCheck29510 AlignedValid.nil

def missing29511_29512 : List (BitVec (edgeCount 12)) :=
  [missing29511]
abbrev records29511_29512 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29511]
theorem aligned29511_29512 :
    AlignedValid 12 4 missing29511_29512 records29511_29512 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29511
    maskCheck29511 AlignedValid.nil

def missing29510_29512 : List (BitVec (edgeCount 12)) :=
  missing29510_29511 ++ missing29511_29512
abbrev records29510_29512 : List Blob :=
  records29510_29511 ++ records29511_29512
theorem aligned29510_29512 :
    AlignedValid 12 4 missing29510_29512 records29510_29512 :=
  aligned29510_29511.append aligned29511_29512

def missing29508_29512 : List (BitVec (edgeCount 12)) :=
  missing29508_29510 ++ missing29510_29512
abbrev records29508_29512 : List Blob :=
  records29508_29510 ++ records29510_29512
theorem aligned29508_29512 :
    AlignedValid 12 4 missing29508_29512 records29508_29512 :=
  aligned29508_29510.append aligned29510_29512

def missing29504_29512 : List (BitVec (edgeCount 12)) :=
  missing29504_29508 ++ missing29508_29512
abbrev records29504_29512 : List Blob :=
  records29504_29508 ++ records29508_29512
theorem aligned29504_29512 :
    AlignedValid 12 4 missing29504_29512 records29504_29512 :=
  aligned29504_29508.append aligned29508_29512

def missing29512_29513 : List (BitVec (edgeCount 12)) :=
  [missing29512]
abbrev records29512_29513 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29512]
theorem aligned29512_29513 :
    AlignedValid 12 4 missing29512_29513 records29512_29513 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29512
    maskCheck29512 AlignedValid.nil

def missing29513_29514 : List (BitVec (edgeCount 12)) :=
  [missing29513]
abbrev records29513_29514 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29513]
theorem aligned29513_29514 :
    AlignedValid 12 4 missing29513_29514 records29513_29514 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29513
    maskCheck29513 AlignedValid.nil

def missing29512_29514 : List (BitVec (edgeCount 12)) :=
  missing29512_29513 ++ missing29513_29514
abbrev records29512_29514 : List Blob :=
  records29512_29513 ++ records29513_29514
theorem aligned29512_29514 :
    AlignedValid 12 4 missing29512_29514 records29512_29514 :=
  aligned29512_29513.append aligned29513_29514

def missing29514_29515 : List (BitVec (edgeCount 12)) :=
  [missing29514]
abbrev records29514_29515 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29514]
theorem aligned29514_29515 :
    AlignedValid 12 4 missing29514_29515 records29514_29515 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29514
    maskCheck29514 AlignedValid.nil

def missing29515_29516 : List (BitVec (edgeCount 12)) :=
  [missing29515]
abbrev records29515_29516 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29515]
theorem aligned29515_29516 :
    AlignedValid 12 4 missing29515_29516 records29515_29516 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29515
    maskCheck29515 AlignedValid.nil

def missing29514_29516 : List (BitVec (edgeCount 12)) :=
  missing29514_29515 ++ missing29515_29516
abbrev records29514_29516 : List Blob :=
  records29514_29515 ++ records29515_29516
theorem aligned29514_29516 :
    AlignedValid 12 4 missing29514_29516 records29514_29516 :=
  aligned29514_29515.append aligned29515_29516

def missing29512_29516 : List (BitVec (edgeCount 12)) :=
  missing29512_29514 ++ missing29514_29516
abbrev records29512_29516 : List Blob :=
  records29512_29514 ++ records29514_29516
theorem aligned29512_29516 :
    AlignedValid 12 4 missing29512_29516 records29512_29516 :=
  aligned29512_29514.append aligned29514_29516

def missing29516_29517 : List (BitVec (edgeCount 12)) :=
  [missing29516]
abbrev records29516_29517 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29516]
theorem aligned29516_29517 :
    AlignedValid 12 4 missing29516_29517 records29516_29517 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29516
    maskCheck29516 AlignedValid.nil

def missing29517_29518 : List (BitVec (edgeCount 12)) :=
  [missing29517]
abbrev records29517_29518 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29517]
theorem aligned29517_29518 :
    AlignedValid 12 4 missing29517_29518 records29517_29518 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29517
    maskCheck29517 AlignedValid.nil

def missing29516_29518 : List (BitVec (edgeCount 12)) :=
  missing29516_29517 ++ missing29517_29518
abbrev records29516_29518 : List Blob :=
  records29516_29517 ++ records29517_29518
theorem aligned29516_29518 :
    AlignedValid 12 4 missing29516_29518 records29516_29518 :=
  aligned29516_29517.append aligned29517_29518

def missing29518_29519 : List (BitVec (edgeCount 12)) :=
  [missing29518]
abbrev records29518_29519 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29518]
theorem aligned29518_29519 :
    AlignedValid 12 4 missing29518_29519 records29518_29519 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29518
    maskCheck29518 AlignedValid.nil

def missing29519_29520 : List (BitVec (edgeCount 12)) :=
  [missing29519]
abbrev records29519_29520 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29519]
theorem aligned29519_29520 :
    AlignedValid 12 4 missing29519_29520 records29519_29520 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29519
    maskCheck29519 AlignedValid.nil

def missing29518_29520 : List (BitVec (edgeCount 12)) :=
  missing29518_29519 ++ missing29519_29520
abbrev records29518_29520 : List Blob :=
  records29518_29519 ++ records29519_29520
theorem aligned29518_29520 :
    AlignedValid 12 4 missing29518_29520 records29518_29520 :=
  aligned29518_29519.append aligned29519_29520

def missing29516_29520 : List (BitVec (edgeCount 12)) :=
  missing29516_29518 ++ missing29518_29520
abbrev records29516_29520 : List Blob :=
  records29516_29518 ++ records29518_29520
theorem aligned29516_29520 :
    AlignedValid 12 4 missing29516_29520 records29516_29520 :=
  aligned29516_29518.append aligned29518_29520

def missing29512_29520 : List (BitVec (edgeCount 12)) :=
  missing29512_29516 ++ missing29516_29520
abbrev records29512_29520 : List Blob :=
  records29512_29516 ++ records29516_29520
theorem aligned29512_29520 :
    AlignedValid 12 4 missing29512_29520 records29512_29520 :=
  aligned29512_29516.append aligned29516_29520

def missing29504_29520 : List (BitVec (edgeCount 12)) :=
  missing29504_29512 ++ missing29512_29520
abbrev records29504_29520 : List Blob :=
  records29504_29512 ++ records29512_29520
theorem aligned29504_29520 :
    AlignedValid 12 4 missing29504_29520 records29504_29520 :=
  aligned29504_29512.append aligned29512_29520

def missing29520_29521 : List (BitVec (edgeCount 12)) :=
  [missing29520]
abbrev records29520_29521 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29520]
theorem aligned29520_29521 :
    AlignedValid 12 4 missing29520_29521 records29520_29521 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29520
    maskCheck29520 AlignedValid.nil

def missing29521_29522 : List (BitVec (edgeCount 12)) :=
  [missing29521]
abbrev records29521_29522 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29521]
theorem aligned29521_29522 :
    AlignedValid 12 4 missing29521_29522 records29521_29522 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29521
    maskCheck29521 AlignedValid.nil

def missing29520_29522 : List (BitVec (edgeCount 12)) :=
  missing29520_29521 ++ missing29521_29522
abbrev records29520_29522 : List Blob :=
  records29520_29521 ++ records29521_29522
theorem aligned29520_29522 :
    AlignedValid 12 4 missing29520_29522 records29520_29522 :=
  aligned29520_29521.append aligned29521_29522

def missing29522_29523 : List (BitVec (edgeCount 12)) :=
  [missing29522]
abbrev records29522_29523 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29522]
theorem aligned29522_29523 :
    AlignedValid 12 4 missing29522_29523 records29522_29523 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29522
    maskCheck29522 AlignedValid.nil

def missing29523_29524 : List (BitVec (edgeCount 12)) :=
  [missing29523]
abbrev records29523_29524 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29523]
theorem aligned29523_29524 :
    AlignedValid 12 4 missing29523_29524 records29523_29524 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29523
    maskCheck29523 AlignedValid.nil

def missing29522_29524 : List (BitVec (edgeCount 12)) :=
  missing29522_29523 ++ missing29523_29524
abbrev records29522_29524 : List Blob :=
  records29522_29523 ++ records29523_29524
theorem aligned29522_29524 :
    AlignedValid 12 4 missing29522_29524 records29522_29524 :=
  aligned29522_29523.append aligned29523_29524

def missing29520_29524 : List (BitVec (edgeCount 12)) :=
  missing29520_29522 ++ missing29522_29524
abbrev records29520_29524 : List Blob :=
  records29520_29522 ++ records29522_29524
theorem aligned29520_29524 :
    AlignedValid 12 4 missing29520_29524 records29520_29524 :=
  aligned29520_29522.append aligned29522_29524

def missing29524_29525 : List (BitVec (edgeCount 12)) :=
  [missing29524]
abbrev records29524_29525 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29524]
theorem aligned29524_29525 :
    AlignedValid 12 4 missing29524_29525 records29524_29525 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29524
    maskCheck29524 AlignedValid.nil

def missing29525_29526 : List (BitVec (edgeCount 12)) :=
  [missing29525]
abbrev records29525_29526 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29525]
theorem aligned29525_29526 :
    AlignedValid 12 4 missing29525_29526 records29525_29526 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29525
    maskCheck29525 AlignedValid.nil

def missing29524_29526 : List (BitVec (edgeCount 12)) :=
  missing29524_29525 ++ missing29525_29526
abbrev records29524_29526 : List Blob :=
  records29524_29525 ++ records29525_29526
theorem aligned29524_29526 :
    AlignedValid 12 4 missing29524_29526 records29524_29526 :=
  aligned29524_29525.append aligned29525_29526

def missing29526_29527 : List (BitVec (edgeCount 12)) :=
  [missing29526]
abbrev records29526_29527 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29526]
theorem aligned29526_29527 :
    AlignedValid 12 4 missing29526_29527 records29526_29527 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29526
    maskCheck29526 AlignedValid.nil

def missing29527_29528 : List (BitVec (edgeCount 12)) :=
  [missing29527]
abbrev records29527_29528 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29527]
theorem aligned29527_29528 :
    AlignedValid 12 4 missing29527_29528 records29527_29528 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29527
    maskCheck29527 AlignedValid.nil

def missing29526_29528 : List (BitVec (edgeCount 12)) :=
  missing29526_29527 ++ missing29527_29528
abbrev records29526_29528 : List Blob :=
  records29526_29527 ++ records29527_29528
theorem aligned29526_29528 :
    AlignedValid 12 4 missing29526_29528 records29526_29528 :=
  aligned29526_29527.append aligned29527_29528

def missing29524_29528 : List (BitVec (edgeCount 12)) :=
  missing29524_29526 ++ missing29526_29528
abbrev records29524_29528 : List Blob :=
  records29524_29526 ++ records29526_29528
theorem aligned29524_29528 :
    AlignedValid 12 4 missing29524_29528 records29524_29528 :=
  aligned29524_29526.append aligned29526_29528

def missing29520_29528 : List (BitVec (edgeCount 12)) :=
  missing29520_29524 ++ missing29524_29528
abbrev records29520_29528 : List Blob :=
  records29520_29524 ++ records29524_29528
theorem aligned29520_29528 :
    AlignedValid 12 4 missing29520_29528 records29520_29528 :=
  aligned29520_29524.append aligned29524_29528

def missing29528_29529 : List (BitVec (edgeCount 12)) :=
  [missing29528]
abbrev records29528_29529 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29528]
theorem aligned29528_29529 :
    AlignedValid 12 4 missing29528_29529 records29528_29529 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29528
    maskCheck29528 AlignedValid.nil

def missing29529_29530 : List (BitVec (edgeCount 12)) :=
  [missing29529]
abbrev records29529_29530 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29529]
theorem aligned29529_29530 :
    AlignedValid 12 4 missing29529_29530 records29529_29530 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29529
    maskCheck29529 AlignedValid.nil

def missing29528_29530 : List (BitVec (edgeCount 12)) :=
  missing29528_29529 ++ missing29529_29530
abbrev records29528_29530 : List Blob :=
  records29528_29529 ++ records29529_29530
theorem aligned29528_29530 :
    AlignedValid 12 4 missing29528_29530 records29528_29530 :=
  aligned29528_29529.append aligned29529_29530

def missing29530_29531 : List (BitVec (edgeCount 12)) :=
  [missing29530]
abbrev records29530_29531 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29530]
theorem aligned29530_29531 :
    AlignedValid 12 4 missing29530_29531 records29530_29531 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29530
    maskCheck29530 AlignedValid.nil

def missing29531_29532 : List (BitVec (edgeCount 12)) :=
  [missing29531]
abbrev records29531_29532 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29531]
theorem aligned29531_29532 :
    AlignedValid 12 4 missing29531_29532 records29531_29532 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29531
    maskCheck29531 AlignedValid.nil

def missing29530_29532 : List (BitVec (edgeCount 12)) :=
  missing29530_29531 ++ missing29531_29532
abbrev records29530_29532 : List Blob :=
  records29530_29531 ++ records29531_29532
theorem aligned29530_29532 :
    AlignedValid 12 4 missing29530_29532 records29530_29532 :=
  aligned29530_29531.append aligned29531_29532

def missing29528_29532 : List (BitVec (edgeCount 12)) :=
  missing29528_29530 ++ missing29530_29532
abbrev records29528_29532 : List Blob :=
  records29528_29530 ++ records29530_29532
theorem aligned29528_29532 :
    AlignedValid 12 4 missing29528_29532 records29528_29532 :=
  aligned29528_29530.append aligned29530_29532

def missing29532_29533 : List (BitVec (edgeCount 12)) :=
  [missing29532]
abbrev records29532_29533 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29532]
theorem aligned29532_29533 :
    AlignedValid 12 4 missing29532_29533 records29532_29533 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29532
    maskCheck29532 AlignedValid.nil

def missing29533_29534 : List (BitVec (edgeCount 12)) :=
  [missing29533]
abbrev records29533_29534 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29533]
theorem aligned29533_29534 :
    AlignedValid 12 4 missing29533_29534 records29533_29534 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29533
    maskCheck29533 AlignedValid.nil

def missing29532_29534 : List (BitVec (edgeCount 12)) :=
  missing29532_29533 ++ missing29533_29534
abbrev records29532_29534 : List Blob :=
  records29532_29533 ++ records29533_29534
theorem aligned29532_29534 :
    AlignedValid 12 4 missing29532_29534 records29532_29534 :=
  aligned29532_29533.append aligned29533_29534

def missing29534_29535 : List (BitVec (edgeCount 12)) :=
  [missing29534]
abbrev records29534_29535 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29534]
theorem aligned29534_29535 :
    AlignedValid 12 4 missing29534_29535 records29534_29535 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29534
    maskCheck29534 AlignedValid.nil

def missing29535_29536 : List (BitVec (edgeCount 12)) :=
  [missing29535]
abbrev records29535_29536 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29535]
theorem aligned29535_29536 :
    AlignedValid 12 4 missing29535_29536 records29535_29536 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29535
    maskCheck29535 AlignedValid.nil

def missing29534_29536 : List (BitVec (edgeCount 12)) :=
  missing29534_29535 ++ missing29535_29536
abbrev records29534_29536 : List Blob :=
  records29534_29535 ++ records29535_29536
theorem aligned29534_29536 :
    AlignedValid 12 4 missing29534_29536 records29534_29536 :=
  aligned29534_29535.append aligned29535_29536

def missing29532_29536 : List (BitVec (edgeCount 12)) :=
  missing29532_29534 ++ missing29534_29536
abbrev records29532_29536 : List Blob :=
  records29532_29534 ++ records29534_29536
theorem aligned29532_29536 :
    AlignedValid 12 4 missing29532_29536 records29532_29536 :=
  aligned29532_29534.append aligned29534_29536

def missing29528_29536 : List (BitVec (edgeCount 12)) :=
  missing29528_29532 ++ missing29532_29536
abbrev records29528_29536 : List Blob :=
  records29528_29532 ++ records29532_29536
theorem aligned29528_29536 :
    AlignedValid 12 4 missing29528_29536 records29528_29536 :=
  aligned29528_29532.append aligned29532_29536

def missing29520_29536 : List (BitVec (edgeCount 12)) :=
  missing29520_29528 ++ missing29528_29536
abbrev records29520_29536 : List Blob :=
  records29520_29528 ++ records29528_29536
theorem aligned29520_29536 :
    AlignedValid 12 4 missing29520_29536 records29520_29536 :=
  aligned29520_29528.append aligned29528_29536

def missing29504_29536 : List (BitVec (edgeCount 12)) :=
  missing29504_29520 ++ missing29520_29536
abbrev records29504_29536 : List Blob :=
  records29504_29520 ++ records29520_29536
theorem aligned29504_29536 :
    AlignedValid 12 4 missing29504_29536 records29504_29536 :=
  aligned29504_29520.append aligned29520_29536

def missing29536_29537 : List (BitVec (edgeCount 12)) :=
  [missing29536]
abbrev records29536_29537 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29536]
theorem aligned29536_29537 :
    AlignedValid 12 4 missing29536_29537 records29536_29537 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29536
    maskCheck29536 AlignedValid.nil

def missing29537_29538 : List (BitVec (edgeCount 12)) :=
  [missing29537]
abbrev records29537_29538 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29537]
theorem aligned29537_29538 :
    AlignedValid 12 4 missing29537_29538 records29537_29538 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29537
    maskCheck29537 AlignedValid.nil

def missing29536_29538 : List (BitVec (edgeCount 12)) :=
  missing29536_29537 ++ missing29537_29538
abbrev records29536_29538 : List Blob :=
  records29536_29537 ++ records29537_29538
theorem aligned29536_29538 :
    AlignedValid 12 4 missing29536_29538 records29536_29538 :=
  aligned29536_29537.append aligned29537_29538

def missing29538_29539 : List (BitVec (edgeCount 12)) :=
  [missing29538]
abbrev records29538_29539 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29538]
theorem aligned29538_29539 :
    AlignedValid 12 4 missing29538_29539 records29538_29539 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29538
    maskCheck29538 AlignedValid.nil

def missing29539_29540 : List (BitVec (edgeCount 12)) :=
  [missing29539]
abbrev records29539_29540 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29539]
theorem aligned29539_29540 :
    AlignedValid 12 4 missing29539_29540 records29539_29540 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29539
    maskCheck29539 AlignedValid.nil

def missing29538_29540 : List (BitVec (edgeCount 12)) :=
  missing29538_29539 ++ missing29539_29540
abbrev records29538_29540 : List Blob :=
  records29538_29539 ++ records29539_29540
theorem aligned29538_29540 :
    AlignedValid 12 4 missing29538_29540 records29538_29540 :=
  aligned29538_29539.append aligned29539_29540

def missing29536_29540 : List (BitVec (edgeCount 12)) :=
  missing29536_29538 ++ missing29538_29540
abbrev records29536_29540 : List Blob :=
  records29536_29538 ++ records29538_29540
theorem aligned29536_29540 :
    AlignedValid 12 4 missing29536_29540 records29536_29540 :=
  aligned29536_29538.append aligned29538_29540

def missing29540_29541 : List (BitVec (edgeCount 12)) :=
  [missing29540]
abbrev records29540_29541 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29540]
theorem aligned29540_29541 :
    AlignedValid 12 4 missing29540_29541 records29540_29541 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29540
    maskCheck29540 AlignedValid.nil

def missing29541_29542 : List (BitVec (edgeCount 12)) :=
  [missing29541]
abbrev records29541_29542 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29541]
theorem aligned29541_29542 :
    AlignedValid 12 4 missing29541_29542 records29541_29542 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29541
    maskCheck29541 AlignedValid.nil

def missing29540_29542 : List (BitVec (edgeCount 12)) :=
  missing29540_29541 ++ missing29541_29542
abbrev records29540_29542 : List Blob :=
  records29540_29541 ++ records29541_29542
theorem aligned29540_29542 :
    AlignedValid 12 4 missing29540_29542 records29540_29542 :=
  aligned29540_29541.append aligned29541_29542

def missing29542_29543 : List (BitVec (edgeCount 12)) :=
  [missing29542]
abbrev records29542_29543 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29542]
theorem aligned29542_29543 :
    AlignedValid 12 4 missing29542_29543 records29542_29543 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29542
    maskCheck29542 AlignedValid.nil

def missing29543_29544 : List (BitVec (edgeCount 12)) :=
  [missing29543]
abbrev records29543_29544 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29543]
theorem aligned29543_29544 :
    AlignedValid 12 4 missing29543_29544 records29543_29544 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29543
    maskCheck29543 AlignedValid.nil

def missing29542_29544 : List (BitVec (edgeCount 12)) :=
  missing29542_29543 ++ missing29543_29544
abbrev records29542_29544 : List Blob :=
  records29542_29543 ++ records29543_29544
theorem aligned29542_29544 :
    AlignedValid 12 4 missing29542_29544 records29542_29544 :=
  aligned29542_29543.append aligned29543_29544

def missing29540_29544 : List (BitVec (edgeCount 12)) :=
  missing29540_29542 ++ missing29542_29544
abbrev records29540_29544 : List Blob :=
  records29540_29542 ++ records29542_29544
theorem aligned29540_29544 :
    AlignedValid 12 4 missing29540_29544 records29540_29544 :=
  aligned29540_29542.append aligned29542_29544

def missing29536_29544 : List (BitVec (edgeCount 12)) :=
  missing29536_29540 ++ missing29540_29544
abbrev records29536_29544 : List Blob :=
  records29536_29540 ++ records29540_29544
theorem aligned29536_29544 :
    AlignedValid 12 4 missing29536_29544 records29536_29544 :=
  aligned29536_29540.append aligned29540_29544

def missing29544_29545 : List (BitVec (edgeCount 12)) :=
  [missing29544]
abbrev records29544_29545 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29544]
theorem aligned29544_29545 :
    AlignedValid 12 4 missing29544_29545 records29544_29545 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29544
    maskCheck29544 AlignedValid.nil

def missing29545_29546 : List (BitVec (edgeCount 12)) :=
  [missing29545]
abbrev records29545_29546 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29545]
theorem aligned29545_29546 :
    AlignedValid 12 4 missing29545_29546 records29545_29546 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29545
    maskCheck29545 AlignedValid.nil

def missing29544_29546 : List (BitVec (edgeCount 12)) :=
  missing29544_29545 ++ missing29545_29546
abbrev records29544_29546 : List Blob :=
  records29544_29545 ++ records29545_29546
theorem aligned29544_29546 :
    AlignedValid 12 4 missing29544_29546 records29544_29546 :=
  aligned29544_29545.append aligned29545_29546

def missing29546_29547 : List (BitVec (edgeCount 12)) :=
  [missing29546]
abbrev records29546_29547 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29546]
theorem aligned29546_29547 :
    AlignedValid 12 4 missing29546_29547 records29546_29547 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29546
    maskCheck29546 AlignedValid.nil

def missing29547_29548 : List (BitVec (edgeCount 12)) :=
  [missing29547]
abbrev records29547_29548 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29547]
theorem aligned29547_29548 :
    AlignedValid 12 4 missing29547_29548 records29547_29548 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29547
    maskCheck29547 AlignedValid.nil

def missing29546_29548 : List (BitVec (edgeCount 12)) :=
  missing29546_29547 ++ missing29547_29548
abbrev records29546_29548 : List Blob :=
  records29546_29547 ++ records29547_29548
theorem aligned29546_29548 :
    AlignedValid 12 4 missing29546_29548 records29546_29548 :=
  aligned29546_29547.append aligned29547_29548

def missing29544_29548 : List (BitVec (edgeCount 12)) :=
  missing29544_29546 ++ missing29546_29548
abbrev records29544_29548 : List Blob :=
  records29544_29546 ++ records29546_29548
theorem aligned29544_29548 :
    AlignedValid 12 4 missing29544_29548 records29544_29548 :=
  aligned29544_29546.append aligned29546_29548

def missing29548_29549 : List (BitVec (edgeCount 12)) :=
  [missing29548]
abbrev records29548_29549 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29548]
theorem aligned29548_29549 :
    AlignedValid 12 4 missing29548_29549 records29548_29549 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29548
    maskCheck29548 AlignedValid.nil

def missing29549_29550 : List (BitVec (edgeCount 12)) :=
  [missing29549]
abbrev records29549_29550 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29549]
theorem aligned29549_29550 :
    AlignedValid 12 4 missing29549_29550 records29549_29550 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29549
    maskCheck29549 AlignedValid.nil

def missing29548_29550 : List (BitVec (edgeCount 12)) :=
  missing29548_29549 ++ missing29549_29550
abbrev records29548_29550 : List Blob :=
  records29548_29549 ++ records29549_29550
theorem aligned29548_29550 :
    AlignedValid 12 4 missing29548_29550 records29548_29550 :=
  aligned29548_29549.append aligned29549_29550

def missing29550_29551 : List (BitVec (edgeCount 12)) :=
  [missing29550]
abbrev records29550_29551 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29550]
theorem aligned29550_29551 :
    AlignedValid 12 4 missing29550_29551 records29550_29551 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29550
    maskCheck29550 AlignedValid.nil

def missing29551_29552 : List (BitVec (edgeCount 12)) :=
  [missing29551]
abbrev records29551_29552 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29551]
theorem aligned29551_29552 :
    AlignedValid 12 4 missing29551_29552 records29551_29552 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29551
    maskCheck29551 AlignedValid.nil

def missing29550_29552 : List (BitVec (edgeCount 12)) :=
  missing29550_29551 ++ missing29551_29552
abbrev records29550_29552 : List Blob :=
  records29550_29551 ++ records29551_29552
theorem aligned29550_29552 :
    AlignedValid 12 4 missing29550_29552 records29550_29552 :=
  aligned29550_29551.append aligned29551_29552

def missing29548_29552 : List (BitVec (edgeCount 12)) :=
  missing29548_29550 ++ missing29550_29552
abbrev records29548_29552 : List Blob :=
  records29548_29550 ++ records29550_29552
theorem aligned29548_29552 :
    AlignedValid 12 4 missing29548_29552 records29548_29552 :=
  aligned29548_29550.append aligned29550_29552

def missing29544_29552 : List (BitVec (edgeCount 12)) :=
  missing29544_29548 ++ missing29548_29552
abbrev records29544_29552 : List Blob :=
  records29544_29548 ++ records29548_29552
theorem aligned29544_29552 :
    AlignedValid 12 4 missing29544_29552 records29544_29552 :=
  aligned29544_29548.append aligned29548_29552

def missing29536_29552 : List (BitVec (edgeCount 12)) :=
  missing29536_29544 ++ missing29544_29552
abbrev records29536_29552 : List Blob :=
  records29536_29544 ++ records29544_29552
theorem aligned29536_29552 :
    AlignedValid 12 4 missing29536_29552 records29536_29552 :=
  aligned29536_29544.append aligned29544_29552

def missing29552_29553 : List (BitVec (edgeCount 12)) :=
  [missing29552]
abbrev records29552_29553 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29552]
theorem aligned29552_29553 :
    AlignedValid 12 4 missing29552_29553 records29552_29553 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29552
    maskCheck29552 AlignedValid.nil

def missing29553_29554 : List (BitVec (edgeCount 12)) :=
  [missing29553]
abbrev records29553_29554 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29553]
theorem aligned29553_29554 :
    AlignedValid 12 4 missing29553_29554 records29553_29554 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29553
    maskCheck29553 AlignedValid.nil

def missing29552_29554 : List (BitVec (edgeCount 12)) :=
  missing29552_29553 ++ missing29553_29554
abbrev records29552_29554 : List Blob :=
  records29552_29553 ++ records29553_29554
theorem aligned29552_29554 :
    AlignedValid 12 4 missing29552_29554 records29552_29554 :=
  aligned29552_29553.append aligned29553_29554

def missing29554_29555 : List (BitVec (edgeCount 12)) :=
  [missing29554]
abbrev records29554_29555 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29554]
theorem aligned29554_29555 :
    AlignedValid 12 4 missing29554_29555 records29554_29555 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29554
    maskCheck29554 AlignedValid.nil

def missing29555_29556 : List (BitVec (edgeCount 12)) :=
  [missing29555]
abbrev records29555_29556 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29555]
theorem aligned29555_29556 :
    AlignedValid 12 4 missing29555_29556 records29555_29556 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29555
    maskCheck29555 AlignedValid.nil

def missing29554_29556 : List (BitVec (edgeCount 12)) :=
  missing29554_29555 ++ missing29555_29556
abbrev records29554_29556 : List Blob :=
  records29554_29555 ++ records29555_29556
theorem aligned29554_29556 :
    AlignedValid 12 4 missing29554_29556 records29554_29556 :=
  aligned29554_29555.append aligned29555_29556

def missing29552_29556 : List (BitVec (edgeCount 12)) :=
  missing29552_29554 ++ missing29554_29556
abbrev records29552_29556 : List Blob :=
  records29552_29554 ++ records29554_29556
theorem aligned29552_29556 :
    AlignedValid 12 4 missing29552_29556 records29552_29556 :=
  aligned29552_29554.append aligned29554_29556

def missing29556_29557 : List (BitVec (edgeCount 12)) :=
  [missing29556]
abbrev records29556_29557 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29556]
theorem aligned29556_29557 :
    AlignedValid 12 4 missing29556_29557 records29556_29557 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29556
    maskCheck29556 AlignedValid.nil

def missing29557_29558 : List (BitVec (edgeCount 12)) :=
  [missing29557]
abbrev records29557_29558 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29557]
theorem aligned29557_29558 :
    AlignedValid 12 4 missing29557_29558 records29557_29558 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29557
    maskCheck29557 AlignedValid.nil

def missing29556_29558 : List (BitVec (edgeCount 12)) :=
  missing29556_29557 ++ missing29557_29558
abbrev records29556_29558 : List Blob :=
  records29556_29557 ++ records29557_29558
theorem aligned29556_29558 :
    AlignedValid 12 4 missing29556_29558 records29556_29558 :=
  aligned29556_29557.append aligned29557_29558

def missing29558_29559 : List (BitVec (edgeCount 12)) :=
  [missing29558]
abbrev records29558_29559 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29558]
theorem aligned29558_29559 :
    AlignedValid 12 4 missing29558_29559 records29558_29559 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29558
    maskCheck29558 AlignedValid.nil

def missing29559_29560 : List (BitVec (edgeCount 12)) :=
  [missing29559]
abbrev records29559_29560 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29559]
theorem aligned29559_29560 :
    AlignedValid 12 4 missing29559_29560 records29559_29560 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29559
    maskCheck29559 AlignedValid.nil

def missing29558_29560 : List (BitVec (edgeCount 12)) :=
  missing29558_29559 ++ missing29559_29560
abbrev records29558_29560 : List Blob :=
  records29558_29559 ++ records29559_29560
theorem aligned29558_29560 :
    AlignedValid 12 4 missing29558_29560 records29558_29560 :=
  aligned29558_29559.append aligned29559_29560

def missing29556_29560 : List (BitVec (edgeCount 12)) :=
  missing29556_29558 ++ missing29558_29560
abbrev records29556_29560 : List Blob :=
  records29556_29558 ++ records29558_29560
theorem aligned29556_29560 :
    AlignedValid 12 4 missing29556_29560 records29556_29560 :=
  aligned29556_29558.append aligned29558_29560

def missing29552_29560 : List (BitVec (edgeCount 12)) :=
  missing29552_29556 ++ missing29556_29560
abbrev records29552_29560 : List Blob :=
  records29552_29556 ++ records29556_29560
theorem aligned29552_29560 :
    AlignedValid 12 4 missing29552_29560 records29552_29560 :=
  aligned29552_29556.append aligned29556_29560

def missing29560_29561 : List (BitVec (edgeCount 12)) :=
  [missing29560]
abbrev records29560_29561 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29560]
theorem aligned29560_29561 :
    AlignedValid 12 4 missing29560_29561 records29560_29561 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29560
    maskCheck29560 AlignedValid.nil

def missing29561_29562 : List (BitVec (edgeCount 12)) :=
  [missing29561]
abbrev records29561_29562 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29561]
theorem aligned29561_29562 :
    AlignedValid 12 4 missing29561_29562 records29561_29562 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29561
    maskCheck29561 AlignedValid.nil

def missing29560_29562 : List (BitVec (edgeCount 12)) :=
  missing29560_29561 ++ missing29561_29562
abbrev records29560_29562 : List Blob :=
  records29560_29561 ++ records29561_29562
theorem aligned29560_29562 :
    AlignedValid 12 4 missing29560_29562 records29560_29562 :=
  aligned29560_29561.append aligned29561_29562

def missing29562_29563 : List (BitVec (edgeCount 12)) :=
  [missing29562]
abbrev records29562_29563 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29562]
theorem aligned29562_29563 :
    AlignedValid 12 4 missing29562_29563 records29562_29563 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29562
    maskCheck29562 AlignedValid.nil

def missing29563_29564 : List (BitVec (edgeCount 12)) :=
  [missing29563]
abbrev records29563_29564 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29563]
theorem aligned29563_29564 :
    AlignedValid 12 4 missing29563_29564 records29563_29564 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29563
    maskCheck29563 AlignedValid.nil

def missing29562_29564 : List (BitVec (edgeCount 12)) :=
  missing29562_29563 ++ missing29563_29564
abbrev records29562_29564 : List Blob :=
  records29562_29563 ++ records29563_29564
theorem aligned29562_29564 :
    AlignedValid 12 4 missing29562_29564 records29562_29564 :=
  aligned29562_29563.append aligned29563_29564

def missing29560_29564 : List (BitVec (edgeCount 12)) :=
  missing29560_29562 ++ missing29562_29564
abbrev records29560_29564 : List Blob :=
  records29560_29562 ++ records29562_29564
theorem aligned29560_29564 :
    AlignedValid 12 4 missing29560_29564 records29560_29564 :=
  aligned29560_29562.append aligned29562_29564

def missing29564_29565 : List (BitVec (edgeCount 12)) :=
  [missing29564]
abbrev records29564_29565 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29564]
theorem aligned29564_29565 :
    AlignedValid 12 4 missing29564_29565 records29564_29565 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29564
    maskCheck29564 AlignedValid.nil

def missing29565_29566 : List (BitVec (edgeCount 12)) :=
  [missing29565]
abbrev records29565_29566 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29565]
theorem aligned29565_29566 :
    AlignedValid 12 4 missing29565_29566 records29565_29566 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29565
    maskCheck29565 AlignedValid.nil

def missing29564_29566 : List (BitVec (edgeCount 12)) :=
  missing29564_29565 ++ missing29565_29566
abbrev records29564_29566 : List Blob :=
  records29564_29565 ++ records29565_29566
theorem aligned29564_29566 :
    AlignedValid 12 4 missing29564_29566 records29564_29566 :=
  aligned29564_29565.append aligned29565_29566

def missing29566_29567 : List (BitVec (edgeCount 12)) :=
  [missing29566]
abbrev records29566_29567 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29566]
theorem aligned29566_29567 :
    AlignedValid 12 4 missing29566_29567 records29566_29567 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29566
    maskCheck29566 AlignedValid.nil

def missing29567_29568 : List (BitVec (edgeCount 12)) :=
  [missing29567]
abbrev records29567_29568 : List Blob :=
  [StrongPackedBucketN12A4Shard230.record29567]
theorem aligned29567_29568 :
    AlignedValid 12 4 missing29567_29568 records29567_29568 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard230.check29567
    maskCheck29567 AlignedValid.nil

def missing29566_29568 : List (BitVec (edgeCount 12)) :=
  missing29566_29567 ++ missing29567_29568
abbrev records29566_29568 : List Blob :=
  records29566_29567 ++ records29567_29568
theorem aligned29566_29568 :
    AlignedValid 12 4 missing29566_29568 records29566_29568 :=
  aligned29566_29567.append aligned29567_29568

def missing29564_29568 : List (BitVec (edgeCount 12)) :=
  missing29564_29566 ++ missing29566_29568
abbrev records29564_29568 : List Blob :=
  records29564_29566 ++ records29566_29568
theorem aligned29564_29568 :
    AlignedValid 12 4 missing29564_29568 records29564_29568 :=
  aligned29564_29566.append aligned29566_29568

def missing29560_29568 : List (BitVec (edgeCount 12)) :=
  missing29560_29564 ++ missing29564_29568
abbrev records29560_29568 : List Blob :=
  records29560_29564 ++ records29564_29568
theorem aligned29560_29568 :
    AlignedValid 12 4 missing29560_29568 records29560_29568 :=
  aligned29560_29564.append aligned29564_29568

def missing29552_29568 : List (BitVec (edgeCount 12)) :=
  missing29552_29560 ++ missing29560_29568
abbrev records29552_29568 : List Blob :=
  records29552_29560 ++ records29560_29568
theorem aligned29552_29568 :
    AlignedValid 12 4 missing29552_29568 records29552_29568 :=
  aligned29552_29560.append aligned29560_29568

def missing29536_29568 : List (BitVec (edgeCount 12)) :=
  missing29536_29552 ++ missing29552_29568
abbrev records29536_29568 : List Blob :=
  records29536_29552 ++ records29552_29568
theorem aligned29536_29568 :
    AlignedValid 12 4 missing29536_29568 records29536_29568 :=
  aligned29536_29552.append aligned29552_29568

def missing29504_29568 : List (BitVec (edgeCount 12)) :=
  missing29504_29536 ++ missing29536_29568
abbrev records29504_29568 : List Blob :=
  records29504_29536 ++ records29536_29568
theorem aligned29504_29568 :
    AlignedValid 12 4 missing29504_29568 records29504_29568 :=
  aligned29504_29536.append aligned29536_29568

def missing29440_29568 : List (BitVec (edgeCount 12)) :=
  missing29440_29504 ++ missing29504_29568
abbrev records29440_29568 : List Blob :=
  records29440_29504 ++ records29504_29568
theorem aligned29440_29568 :
    AlignedValid 12 4 missing29440_29568 records29440_29568 :=
  aligned29440_29504.append aligned29504_29568

abbrev missing : List (BitVec (edgeCount 12)) := missing29440_29568
abbrev records : List Blob := records29440_29568
theorem aligned : AlignedValid 12 4 missing records := aligned29440_29568

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard230
