/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A3Shard050

/-! Decode-only alignment checks for n=12, a=3, records 6400--6527. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard050

open PackedBucketCertificate

def missing6400 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18843553766263750656
theorem maskCheck6400 :
    checkMaskFor missing6400 StrongPackedBucketN12A3Shard050.record6400 = true := by
  decide

def missing6401 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18915611360301678592
theorem maskCheck6401 :
    checkMaskFor missing6401 StrongPackedBucketN12A3Shard050.record6401 = true := by
  decide

def missing6402 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18951640157320642560
theorem maskCheck6402 :
    checkMaskFor missing6402 StrongPackedBucketN12A3Shard050.record6402 = true := by
  decide

def missing6403 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19131784142415462400
theorem maskCheck6403 :
    checkMaskFor missing6403 StrongPackedBucketN12A3Shard050.record6403 = true := by
  decide

def missing6404 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19203841736453390336
theorem maskCheck6404 :
    checkMaskFor missing6404 StrongPackedBucketN12A3Shard050.record6404 = true := by
  decide

def missing6405 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19239870533472354304
theorem maskCheck6405 :
    checkMaskFor missing6405 StrongPackedBucketN12A3Shard050.record6405 = true := by
  decide

def missing6406 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19347956924529246208
theorem maskCheck6406 :
    checkMaskFor missing6406 StrongPackedBucketN12A3Shard050.record6406 = true := by
  decide

def missing6407 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19383985721548210176
theorem maskCheck6407 :
    checkMaskFor missing6407 StrongPackedBucketN12A3Shard050.record6407 = true := by
  decide

def missing6408 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19456043315586138112
theorem maskCheck6408 :
    checkMaskFor missing6408 StrongPackedBucketN12A3Shard050.record6408 = true := by
  decide

def missing6409 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20212648052984381440
theorem maskCheck6409 :
    checkMaskFor missing6409 StrongPackedBucketN12A3Shard050.record6409 = true := by
  decide

def missing6410 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20248676850003345408
theorem maskCheck6410 :
    checkMaskFor missing6410 StrongPackedBucketN12A3Shard050.record6410 = true := by
  decide

def missing6411 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20320734444041273344
theorem maskCheck6411 :
    checkMaskFor missing6411 StrongPackedBucketN12A3Shard050.record6411 = true := by
  decide

def missing6412 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20464849632117129216
theorem maskCheck6412 :
    checkMaskFor missing6412 StrongPackedBucketN12A3Shard050.record6412 = true := by
  decide

def missing6413 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22482462265179111424
theorem maskCheck6413 :
    checkMaskFor missing6413 StrongPackedBucketN12A3Shard050.record6413 = true := by
  decide

def missing6414 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23167009408539426816
theorem maskCheck6414 :
    checkMaskFor missing6414 StrongPackedBucketN12A3Shard050.record6414 = true := by
  decide

def missing6415 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23239067002577354752
theorem maskCheck6415 :
    checkMaskFor missing6415 StrongPackedBucketN12A3Shard050.record6415 = true := by
  decide

def missing6416 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23275095799596318720
theorem maskCheck6416 :
    checkMaskFor missing6416 StrongPackedBucketN12A3Shard050.record6416 = true := by
  decide

def missing6417 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23383182190653210624
theorem maskCheck6417 :
    checkMaskFor missing6417 StrongPackedBucketN12A3Shard050.record6417 = true := by
  decide

def missing6418 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23419210987672174592
theorem maskCheck6418 :
    checkMaskFor missing6418 StrongPackedBucketN12A3Shard050.record6418 = true := by
  decide

def missing6419 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23491268581710102528
theorem maskCheck6419 :
    checkMaskFor missing6419 StrongPackedBucketN12A3Shard050.record6419 = true := by
  decide

def missing6420 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23671412566804922368
theorem maskCheck6420 :
    checkMaskFor missing6420 StrongPackedBucketN12A3Shard050.record6420 = true := by
  decide

def missing6421 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23707441363823886336
theorem maskCheck6421 :
    checkMaskFor missing6421 StrongPackedBucketN12A3Shard050.record6421 = true := by
  decide

def missing6422 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23779498957861814272
theorem maskCheck6422 :
    checkMaskFor missing6422 StrongPackedBucketN12A3Shard050.record6422 = true := by
  decide

def missing6423 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23923614145937670144
theorem maskCheck6423 :
    checkMaskFor missing6423 StrongPackedBucketN12A3Shard050.record6423 = true := by
  decide

def missing6424 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24788305274392805376
theorem maskCheck6424 :
    checkMaskFor missing6424 StrongPackedBucketN12A3Shard050.record6424 = true := by
  decide

def missing6425 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27778695426966814720
theorem maskCheck6425 :
    checkMaskFor missing6425 StrongPackedBucketN12A3Shard050.record6425 = true := by
  decide

def missing6426 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27850753021004742656
theorem maskCheck6426 :
    checkMaskFor missing6426 StrongPackedBucketN12A3Shard050.record6426 = true := by
  decide

def missing6427 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27886781818023706624
theorem maskCheck6427 :
    checkMaskFor missing6427 StrongPackedBucketN12A3Shard050.record6427 = true := by
  decide

def missing6428 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27994868209080598528
theorem maskCheck6428 :
    checkMaskFor missing6428 StrongPackedBucketN12A3Shard050.record6428 = true := by
  decide

def missing6429 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28030897006099562496
theorem maskCheck6429 :
    checkMaskFor missing6429 StrongPackedBucketN12A3Shard050.record6429 = true := by
  decide

def missing6430 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28102954600137490432
theorem maskCheck6430 :
    checkMaskFor missing6430 StrongPackedBucketN12A3Shard050.record6430 = true := by
  decide

def missing6431 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28283098585232310272
theorem maskCheck6431 :
    checkMaskFor missing6431 StrongPackedBucketN12A3Shard050.record6431 = true := by
  decide

def missing6432 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28319127382251274240
theorem maskCheck6432 :
    checkMaskFor missing6432 StrongPackedBucketN12A3Shard050.record6432 = true := by
  decide

def missing6433 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28391184976289202176
theorem maskCheck6433 :
    checkMaskFor missing6433 StrongPackedBucketN12A3Shard050.record6433 = true := by
  decide

def missing6434 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28535300164365058048
theorem maskCheck6434 :
    checkMaskFor missing6434 StrongPackedBucketN12A3Shard050.record6434 = true := by
  decide

def missing6435 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29399991292820193280
theorem maskCheck6435 :
    checkMaskFor missing6435 StrongPackedBucketN12A3Shard050.record6435 = true := by
  decide

def missing6436 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32318323851356274688
theorem maskCheck6436 :
    checkMaskFor missing6436 StrongPackedBucketN12A3Shard050.record6436 = true := by
  decide

def missing6437 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32354352648375238656
theorem maskCheck6437 :
    checkMaskFor missing6437 StrongPackedBucketN12A3Shard050.record6437 = true := by
  decide

def missing6438 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32426410242413166592
theorem maskCheck6438 :
    checkMaskFor missing6438 StrongPackedBucketN12A3Shard050.record6438 = true := by
  decide

def missing6439 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32570525430489022464
theorem maskCheck6439 :
    checkMaskFor missing6439 StrongPackedBucketN12A3Shard050.record6439 = true := by
  decide

def missing6440 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32858755806640734208
theorem maskCheck6440 :
    checkMaskFor missing6440 StrongPackedBucketN12A3Shard050.record6440 = true := by
  decide

def missing6441 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37146182651897446400
theorem maskCheck6441 :
    checkMaskFor missing6441 StrongPackedBucketN12A3Shard050.record6441 = true := by
  decide

def missing6442 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37398384231030194176
theorem maskCheck6442 :
    checkMaskFor missing6442 StrongPackedBucketN12A3Shard050.record6442 = true := by
  decide

def missing6443 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37686614607181905920
theorem maskCheck6443 :
    checkMaskFor missing6443 StrongPackedBucketN12A3Shard050.record6443 = true := by
  decide

def missing6444 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41613753482248978432
theorem maskCheck6444 :
    checkMaskFor missing6444 StrongPackedBucketN12A3Shard050.record6444 = true := by
  decide

def missing6445 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41721839873305870336
theorem maskCheck6445 :
    checkMaskFor missing6445 StrongPackedBucketN12A3Shard050.record6445 = true := by
  decide

def missing6446 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41865955061381726208
theorem maskCheck6446 :
    checkMaskFor missing6446 StrongPackedBucketN12A3Shard050.record6446 = true := by
  decide

def missing6447 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42154185437533437952
theorem maskCheck6447 :
    checkMaskFor missing6447 StrongPackedBucketN12A3Shard050.record6447 = true := by
  decide

def missing6448 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46225439500676366336
theorem maskCheck6448 :
    checkMaskFor missing6448 StrongPackedBucketN12A3Shard050.record6448 = true := by
  decide

def missing6449 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46297497094714294272
theorem maskCheck6449 :
    checkMaskFor missing6449 StrongPackedBucketN12A3Shard050.record6449 = true := by
  decide

def missing6450 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46333525891733258240
theorem maskCheck6450 :
    checkMaskFor missing6450 StrongPackedBucketN12A3Shard050.record6450 = true := by
  decide

def missing6451 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46477641079809114112
theorem maskCheck6451 :
    checkMaskFor missing6451 StrongPackedBucketN12A3Shard050.record6451 = true := by
  decide

def missing6452 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46549698673847042048
theorem maskCheck6452 :
    checkMaskFor missing6452 StrongPackedBucketN12A3Shard050.record6452 = true := by
  decide

def missing6453 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46765871455960825856
theorem maskCheck6453 :
    checkMaskFor missing6453 StrongPackedBucketN12A3Shard050.record6453 = true := by
  decide

def missing6454 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46837929049998753792
theorem maskCheck6454 :
    checkMaskFor missing6454 StrongPackedBucketN12A3Shard050.record6454 = true := by
  decide

def missing6455 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50765067925065826304
theorem maskCheck6455 :
    checkMaskFor missing6455 StrongPackedBucketN12A3Shard050.record6455 = true := by
  decide

def missing6456 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50801096722084790272
theorem maskCheck6456 :
    checkMaskFor missing6456 StrongPackedBucketN12A3Shard050.record6456 = true := by
  decide

def missing6457 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50873154316122718208
theorem maskCheck6457 :
    checkMaskFor missing6457 StrongPackedBucketN12A3Shard050.record6457 = true := by
  decide

def missing6458 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51017269504198574080
theorem maskCheck6458 :
    checkMaskFor missing6458 StrongPackedBucketN12A3Shard050.record6458 = true := by
  decide

def missing6459 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51305499880350285824
theorem maskCheck6459 :
    checkMaskFor missing6459 StrongPackedBucketN12A3Shard050.record6459 = true := by
  decide

def missing6460 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55556897928588034048
theorem maskCheck6460 :
    checkMaskFor missing6460 StrongPackedBucketN12A3Shard050.record6460 = true := by
  decide

def missing6461 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60024468758939566080
theorem maskCheck6461 :
    checkMaskFor missing6461 StrongPackedBucketN12A3Shard050.record6461 = true := by
  decide

def missing6462 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64636154777366953984
theorem maskCheck6462 :
    checkMaskFor missing6462 StrongPackedBucketN12A3Shard050.record6462 = true := by
  decide

def missing6463 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64708212371404881920
theorem maskCheck6463 :
    checkMaskFor missing6463 StrongPackedBucketN12A3Shard050.record6463 = true := by
  decide

def missing6464 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 69175783201756413952
theorem maskCheck6464 :
    checkMaskFor missing6464 StrongPackedBucketN12A3Shard050.record6464 = true := by
  decide

def missing6465 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 541347093095120896
theorem maskCheck6465 :
    checkMaskFor missing6465 StrongPackedBucketN12A3Shard050.record6465 = true := by
  decide

def missing6466 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 973692657322688512
theorem maskCheck6466 :
    checkMaskFor missing6466 StrongPackedBucketN12A3Shard050.record6466 = true := by
  decide

def missing6467 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1045750251360616448
theorem maskCheck6467 :
    checkMaskFor missing6467 StrongPackedBucketN12A3Shard050.record6467 = true := by
  decide

def missing6468 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081779048379580416
theorem maskCheck6468 :
    checkMaskFor missing6468 StrongPackedBucketN12A3Shard050.record6468 = true := by
  decide

def missing6469 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1406038221550256128
theorem maskCheck6469 :
    checkMaskFor missing6469 StrongPackedBucketN12A3Shard050.record6469 = true := by
  decide

def missing6470 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1550153409626112000
theorem maskCheck6470 :
    checkMaskFor missing6470 StrongPackedBucketN12A3Shard050.record6470 = true := by
  decide

def missing6471 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1622211003664039936
theorem maskCheck6471 :
    checkMaskFor missing6471 StrongPackedBucketN12A3Shard050.record6471 = true := by
  decide

def missing6472 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1658239800683003904
theorem maskCheck6472 :
    checkMaskFor missing6472 StrongPackedBucketN12A3Shard050.record6472 = true := by
  decide

def missing6473 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2054556567891607552
theorem maskCheck6473 :
    checkMaskFor missing6473 StrongPackedBucketN12A3Shard050.record6473 = true := by
  decide

def missing6474 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2090585364910571520
theorem maskCheck6474 :
    checkMaskFor missing6474 StrongPackedBucketN12A3Shard050.record6474 = true := by
  decide

def missing6475 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2162642958948499456
theorem maskCheck6475 :
    checkMaskFor missing6475 StrongPackedBucketN12A3Shard050.record6475 = true := by
  decide

def missing6476 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3567766042688094208
theorem maskCheck6476 :
    checkMaskFor missing6476 StrongPackedBucketN12A3Shard050.record6476 = true := by
  decide

def missing6477 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3639823636726022144
theorem maskCheck6477 :
    checkMaskFor missing6477 StrongPackedBucketN12A3Shard050.record6477 = true := by
  decide

def missing6478 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3675852433744986112
theorem maskCheck6478 :
    checkMaskFor missing6478 StrongPackedBucketN12A3Shard050.record6478 = true := by
  decide

def missing6479 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3783938824801878016
theorem maskCheck6479 :
    checkMaskFor missing6479 StrongPackedBucketN12A3Shard050.record6479 = true := by
  decide

def missing6480 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3819967621820841984
theorem maskCheck6480 :
    checkMaskFor missing6480 StrongPackedBucketN12A3Shard050.record6480 = true := by
  decide

def missing6481 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3892025215858769920
theorem maskCheck6481 :
    checkMaskFor missing6481 StrongPackedBucketN12A3Shard050.record6481 = true := by
  decide

def missing6482 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4324370780086337536
theorem maskCheck6482 :
    checkMaskFor missing6482 StrongPackedBucketN12A3Shard050.record6482 = true := by
  decide

def missing6483 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4864802735370797056
theorem maskCheck6483 :
    checkMaskFor missing6483 StrongPackedBucketN12A3Shard050.record6483 = true := by
  decide

def missing6484 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5008917923446652928
theorem maskCheck6484 :
    checkMaskFor missing6484 StrongPackedBucketN12A3Shard050.record6484 = true := by
  decide

def missing6485 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5080975517484580864
theorem maskCheck6485 :
    checkMaskFor missing6485 StrongPackedBucketN12A3Shard050.record6485 = true := by
  decide

def missing6486 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5117004314503544832
theorem maskCheck6486 :
    checkMaskFor missing6486 StrongPackedBucketN12A3Shard050.record6486 = true := by
  decide

def missing6487 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5513321081712148480
theorem maskCheck6487 :
    checkMaskFor missing6487 StrongPackedBucketN12A3Shard050.record6487 = true := by
  decide

def missing6488 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5621407472769040384
theorem maskCheck6488 :
    checkMaskFor missing6488 StrongPackedBucketN12A3Shard050.record6488 = true := by
  decide

def missing6489 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5873609051901788160
theorem maskCheck6489 :
    checkMaskFor missing6489 StrongPackedBucketN12A3Shard050.record6489 = true := by
  decide

def missing6490 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5945666645939716096
theorem maskCheck6490 :
    checkMaskFor missing6490 StrongPackedBucketN12A3Shard050.record6490 = true := by
  decide

def missing6491 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5981695442958680064
theorem maskCheck6491 :
    checkMaskFor missing6491 StrongPackedBucketN12A3Shard050.record6491 = true := by
  decide

def missing6492 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6089781834015571968
theorem maskCheck6492 :
    checkMaskFor missing6492 StrongPackedBucketN12A3Shard050.record6492 = true := by
  decide

def missing6493 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6197868225072463872
theorem maskCheck6493 :
    checkMaskFor missing6493 StrongPackedBucketN12A3Shard050.record6493 = true := by
  decide

def missing6494 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8107394467077554176
theorem maskCheck6494 :
    checkMaskFor missing6494 StrongPackedBucketN12A3Shard050.record6494 = true := by
  decide

def missing6495 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8215480858134446080
theorem maskCheck6495 :
    checkMaskFor missing6495 StrongPackedBucketN12A3Shard050.record6495 = true := by
  decide

def missing6496 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9476488753798184960
theorem maskCheck6496 :
    checkMaskFor missing6496 StrongPackedBucketN12A3Shard050.record6496 = true := by
  decide

def missing6497 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9620603941874040832
theorem maskCheck6497 :
    checkMaskFor missing6497 StrongPackedBucketN12A3Shard050.record6497 = true := by
  decide

def missing6498 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9692661535911968768
theorem maskCheck6498 :
    checkMaskFor missing6498 StrongPackedBucketN12A3Shard050.record6498 = true := by
  decide

def missing6499 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9728690332930932736
theorem maskCheck6499 :
    checkMaskFor missing6499 StrongPackedBucketN12A3Shard050.record6499 = true := by
  decide

def missing6500 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10125007100139536384
theorem maskCheck6500 :
    checkMaskFor missing6500 StrongPackedBucketN12A3Shard050.record6500 = true := by
  decide

def missing6501 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10161035897158500352
theorem maskCheck6501 :
    checkMaskFor missing6501 StrongPackedBucketN12A3Shard050.record6501 = true := by
  decide

def missing6502 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10233093491196428288
theorem maskCheck6502 :
    checkMaskFor missing6502 StrongPackedBucketN12A3Shard050.record6502 = true := by
  decide

def missing6503 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10485295070329176064
theorem maskCheck6503 :
    checkMaskFor missing6503 StrongPackedBucketN12A3Shard050.record6503 = true := by
  decide

def missing6504 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10557352664367104000
theorem maskCheck6504 :
    checkMaskFor missing6504 StrongPackedBucketN12A3Shard050.record6504 = true := by
  decide

def missing6505 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10593381461386067968
theorem maskCheck6505 :
    checkMaskFor missing6505 StrongPackedBucketN12A3Shard050.record6505 = true := by
  decide

def missing6506 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10701467852442959872
theorem maskCheck6506 :
    checkMaskFor missing6506 StrongPackedBucketN12A3Shard050.record6506 = true := by
  decide

def missing6507 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10737496649461923840
theorem maskCheck6507 :
    checkMaskFor missing6507 StrongPackedBucketN12A3Shard050.record6507 = true := by
  decide

def missing6508 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10809554243499851776
theorem maskCheck6508 :
    checkMaskFor missing6508 StrongPackedBucketN12A3Shard050.record6508 = true := by
  decide

def missing6509 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11241899807727419392
theorem maskCheck6509 :
    checkMaskFor missing6509 StrongPackedBucketN12A3Shard050.record6509 = true := by
  decide

def missing6510 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12719080485504942080
theorem maskCheck6510 :
    checkMaskFor missing6510 StrongPackedBucketN12A3Shard050.record6510 = true := by
  decide

def missing6511 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12755109282523906048
theorem maskCheck6511 :
    checkMaskFor missing6511 StrongPackedBucketN12A3Shard050.record6511 = true := by
  decide

def missing6512 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12827166876561833984
theorem maskCheck6512 :
    checkMaskFor missing6512 StrongPackedBucketN12A3Shard050.record6512 = true := by
  decide

def missing6513 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12971282064637689856
theorem maskCheck6513 :
    checkMaskFor missing6513 StrongPackedBucketN12A3Shard050.record6513 = true := by
  decide

def missing6514 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13944059584149716992
theorem maskCheck6514 :
    checkMaskFor missing6514 StrongPackedBucketN12A3Shard050.record6514 = true := by
  decide

def missing6515 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14016117178187644928
theorem maskCheck6515 :
    checkMaskFor missing6515 StrongPackedBucketN12A3Shard050.record6515 = true := by
  decide

def missing6516 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14052145975206608896
theorem maskCheck6516 :
    checkMaskFor missing6516 StrongPackedBucketN12A3Shard050.record6516 = true := by
  decide

def missing6517 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14160232366263500800
theorem maskCheck6517 :
    checkMaskFor missing6517 StrongPackedBucketN12A3Shard050.record6517 = true := by
  decide

def missing6518 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14268318757320392704
theorem maskCheck6518 :
    checkMaskFor missing6518 StrongPackedBucketN12A3Shard050.record6518 = true := by
  decide

def missing6519 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15024923494718636032
theorem maskCheck6519 :
    checkMaskFor missing6519 StrongPackedBucketN12A3Shard050.record6519 = true := by
  decide

def missing6520 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15133009885775527936
theorem maskCheck6520 :
    checkMaskFor missing6520 StrongPackedBucketN12A3Shard050.record6520 = true := by
  decide

def missing6521 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699860790652960768
theorem maskCheck6521 :
    checkMaskFor missing6521 StrongPackedBucketN12A3Shard050.record6521 = true := by
  decide

def missing6522 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18843975978728816640
theorem maskCheck6522 :
    checkMaskFor missing6522 StrongPackedBucketN12A3Shard050.record6522 = true := by
  decide

def missing6523 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18916033572766744576
theorem maskCheck6523 :
    checkMaskFor missing6523 StrongPackedBucketN12A3Shard050.record6523 = true := by
  decide

def missing6524 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19348379136994312192
theorem maskCheck6524 :
    checkMaskFor missing6524 StrongPackedBucketN12A3Shard050.record6524 = true := by
  decide

def missing6525 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19708667107183951872
theorem maskCheck6525 :
    checkMaskFor missing6525 StrongPackedBucketN12A3Shard050.record6525 = true := by
  decide

def missing6526 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19780724701221879808
theorem maskCheck6526 :
    checkMaskFor missing6526 StrongPackedBucketN12A3Shard050.record6526 = true := by
  decide

def missing6527 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19924839889297735680
theorem maskCheck6527 :
    checkMaskFor missing6527 StrongPackedBucketN12A3Shard050.record6527 = true := by
  decide

def missing6400_6401 : List (BitVec (edgeCount 12)) :=
  [missing6400]
abbrev records6400_6401 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6400]
theorem aligned6400_6401 :
    AlignedValid 12 3 missing6400_6401 records6400_6401 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6400
    maskCheck6400 AlignedValid.nil

def missing6401_6402 : List (BitVec (edgeCount 12)) :=
  [missing6401]
abbrev records6401_6402 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6401]
theorem aligned6401_6402 :
    AlignedValid 12 3 missing6401_6402 records6401_6402 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6401
    maskCheck6401 AlignedValid.nil

def missing6400_6402 : List (BitVec (edgeCount 12)) :=
  missing6400_6401 ++ missing6401_6402
abbrev records6400_6402 : List Blob :=
  records6400_6401 ++ records6401_6402
theorem aligned6400_6402 :
    AlignedValid 12 3 missing6400_6402 records6400_6402 :=
  aligned6400_6401.append aligned6401_6402

def missing6402_6403 : List (BitVec (edgeCount 12)) :=
  [missing6402]
abbrev records6402_6403 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6402]
theorem aligned6402_6403 :
    AlignedValid 12 3 missing6402_6403 records6402_6403 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6402
    maskCheck6402 AlignedValid.nil

def missing6403_6404 : List (BitVec (edgeCount 12)) :=
  [missing6403]
abbrev records6403_6404 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6403]
theorem aligned6403_6404 :
    AlignedValid 12 3 missing6403_6404 records6403_6404 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6403
    maskCheck6403 AlignedValid.nil

def missing6402_6404 : List (BitVec (edgeCount 12)) :=
  missing6402_6403 ++ missing6403_6404
abbrev records6402_6404 : List Blob :=
  records6402_6403 ++ records6403_6404
theorem aligned6402_6404 :
    AlignedValid 12 3 missing6402_6404 records6402_6404 :=
  aligned6402_6403.append aligned6403_6404

def missing6400_6404 : List (BitVec (edgeCount 12)) :=
  missing6400_6402 ++ missing6402_6404
abbrev records6400_6404 : List Blob :=
  records6400_6402 ++ records6402_6404
theorem aligned6400_6404 :
    AlignedValid 12 3 missing6400_6404 records6400_6404 :=
  aligned6400_6402.append aligned6402_6404

def missing6404_6405 : List (BitVec (edgeCount 12)) :=
  [missing6404]
abbrev records6404_6405 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6404]
theorem aligned6404_6405 :
    AlignedValid 12 3 missing6404_6405 records6404_6405 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6404
    maskCheck6404 AlignedValid.nil

def missing6405_6406 : List (BitVec (edgeCount 12)) :=
  [missing6405]
abbrev records6405_6406 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6405]
theorem aligned6405_6406 :
    AlignedValid 12 3 missing6405_6406 records6405_6406 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6405
    maskCheck6405 AlignedValid.nil

def missing6404_6406 : List (BitVec (edgeCount 12)) :=
  missing6404_6405 ++ missing6405_6406
abbrev records6404_6406 : List Blob :=
  records6404_6405 ++ records6405_6406
theorem aligned6404_6406 :
    AlignedValid 12 3 missing6404_6406 records6404_6406 :=
  aligned6404_6405.append aligned6405_6406

def missing6406_6407 : List (BitVec (edgeCount 12)) :=
  [missing6406]
abbrev records6406_6407 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6406]
theorem aligned6406_6407 :
    AlignedValid 12 3 missing6406_6407 records6406_6407 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6406
    maskCheck6406 AlignedValid.nil

def missing6407_6408 : List (BitVec (edgeCount 12)) :=
  [missing6407]
abbrev records6407_6408 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6407]
theorem aligned6407_6408 :
    AlignedValid 12 3 missing6407_6408 records6407_6408 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6407
    maskCheck6407 AlignedValid.nil

def missing6406_6408 : List (BitVec (edgeCount 12)) :=
  missing6406_6407 ++ missing6407_6408
abbrev records6406_6408 : List Blob :=
  records6406_6407 ++ records6407_6408
theorem aligned6406_6408 :
    AlignedValid 12 3 missing6406_6408 records6406_6408 :=
  aligned6406_6407.append aligned6407_6408

def missing6404_6408 : List (BitVec (edgeCount 12)) :=
  missing6404_6406 ++ missing6406_6408
abbrev records6404_6408 : List Blob :=
  records6404_6406 ++ records6406_6408
theorem aligned6404_6408 :
    AlignedValid 12 3 missing6404_6408 records6404_6408 :=
  aligned6404_6406.append aligned6406_6408

def missing6400_6408 : List (BitVec (edgeCount 12)) :=
  missing6400_6404 ++ missing6404_6408
abbrev records6400_6408 : List Blob :=
  records6400_6404 ++ records6404_6408
theorem aligned6400_6408 :
    AlignedValid 12 3 missing6400_6408 records6400_6408 :=
  aligned6400_6404.append aligned6404_6408

def missing6408_6409 : List (BitVec (edgeCount 12)) :=
  [missing6408]
abbrev records6408_6409 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6408]
theorem aligned6408_6409 :
    AlignedValid 12 3 missing6408_6409 records6408_6409 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6408
    maskCheck6408 AlignedValid.nil

def missing6409_6410 : List (BitVec (edgeCount 12)) :=
  [missing6409]
abbrev records6409_6410 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6409]
theorem aligned6409_6410 :
    AlignedValid 12 3 missing6409_6410 records6409_6410 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6409
    maskCheck6409 AlignedValid.nil

def missing6408_6410 : List (BitVec (edgeCount 12)) :=
  missing6408_6409 ++ missing6409_6410
abbrev records6408_6410 : List Blob :=
  records6408_6409 ++ records6409_6410
theorem aligned6408_6410 :
    AlignedValid 12 3 missing6408_6410 records6408_6410 :=
  aligned6408_6409.append aligned6409_6410

def missing6410_6411 : List (BitVec (edgeCount 12)) :=
  [missing6410]
abbrev records6410_6411 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6410]
theorem aligned6410_6411 :
    AlignedValid 12 3 missing6410_6411 records6410_6411 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6410
    maskCheck6410 AlignedValid.nil

def missing6411_6412 : List (BitVec (edgeCount 12)) :=
  [missing6411]
abbrev records6411_6412 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6411]
theorem aligned6411_6412 :
    AlignedValid 12 3 missing6411_6412 records6411_6412 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6411
    maskCheck6411 AlignedValid.nil

def missing6410_6412 : List (BitVec (edgeCount 12)) :=
  missing6410_6411 ++ missing6411_6412
abbrev records6410_6412 : List Blob :=
  records6410_6411 ++ records6411_6412
theorem aligned6410_6412 :
    AlignedValid 12 3 missing6410_6412 records6410_6412 :=
  aligned6410_6411.append aligned6411_6412

def missing6408_6412 : List (BitVec (edgeCount 12)) :=
  missing6408_6410 ++ missing6410_6412
abbrev records6408_6412 : List Blob :=
  records6408_6410 ++ records6410_6412
theorem aligned6408_6412 :
    AlignedValid 12 3 missing6408_6412 records6408_6412 :=
  aligned6408_6410.append aligned6410_6412

def missing6412_6413 : List (BitVec (edgeCount 12)) :=
  [missing6412]
abbrev records6412_6413 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6412]
theorem aligned6412_6413 :
    AlignedValid 12 3 missing6412_6413 records6412_6413 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6412
    maskCheck6412 AlignedValid.nil

def missing6413_6414 : List (BitVec (edgeCount 12)) :=
  [missing6413]
abbrev records6413_6414 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6413]
theorem aligned6413_6414 :
    AlignedValid 12 3 missing6413_6414 records6413_6414 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6413
    maskCheck6413 AlignedValid.nil

def missing6412_6414 : List (BitVec (edgeCount 12)) :=
  missing6412_6413 ++ missing6413_6414
abbrev records6412_6414 : List Blob :=
  records6412_6413 ++ records6413_6414
theorem aligned6412_6414 :
    AlignedValid 12 3 missing6412_6414 records6412_6414 :=
  aligned6412_6413.append aligned6413_6414

def missing6414_6415 : List (BitVec (edgeCount 12)) :=
  [missing6414]
abbrev records6414_6415 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6414]
theorem aligned6414_6415 :
    AlignedValid 12 3 missing6414_6415 records6414_6415 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6414
    maskCheck6414 AlignedValid.nil

def missing6415_6416 : List (BitVec (edgeCount 12)) :=
  [missing6415]
abbrev records6415_6416 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6415]
theorem aligned6415_6416 :
    AlignedValid 12 3 missing6415_6416 records6415_6416 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6415
    maskCheck6415 AlignedValid.nil

def missing6414_6416 : List (BitVec (edgeCount 12)) :=
  missing6414_6415 ++ missing6415_6416
abbrev records6414_6416 : List Blob :=
  records6414_6415 ++ records6415_6416
theorem aligned6414_6416 :
    AlignedValid 12 3 missing6414_6416 records6414_6416 :=
  aligned6414_6415.append aligned6415_6416

def missing6412_6416 : List (BitVec (edgeCount 12)) :=
  missing6412_6414 ++ missing6414_6416
abbrev records6412_6416 : List Blob :=
  records6412_6414 ++ records6414_6416
theorem aligned6412_6416 :
    AlignedValid 12 3 missing6412_6416 records6412_6416 :=
  aligned6412_6414.append aligned6414_6416

def missing6408_6416 : List (BitVec (edgeCount 12)) :=
  missing6408_6412 ++ missing6412_6416
abbrev records6408_6416 : List Blob :=
  records6408_6412 ++ records6412_6416
theorem aligned6408_6416 :
    AlignedValid 12 3 missing6408_6416 records6408_6416 :=
  aligned6408_6412.append aligned6412_6416

def missing6400_6416 : List (BitVec (edgeCount 12)) :=
  missing6400_6408 ++ missing6408_6416
abbrev records6400_6416 : List Blob :=
  records6400_6408 ++ records6408_6416
theorem aligned6400_6416 :
    AlignedValid 12 3 missing6400_6416 records6400_6416 :=
  aligned6400_6408.append aligned6408_6416

def missing6416_6417 : List (BitVec (edgeCount 12)) :=
  [missing6416]
abbrev records6416_6417 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6416]
theorem aligned6416_6417 :
    AlignedValid 12 3 missing6416_6417 records6416_6417 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6416
    maskCheck6416 AlignedValid.nil

def missing6417_6418 : List (BitVec (edgeCount 12)) :=
  [missing6417]
abbrev records6417_6418 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6417]
theorem aligned6417_6418 :
    AlignedValid 12 3 missing6417_6418 records6417_6418 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6417
    maskCheck6417 AlignedValid.nil

def missing6416_6418 : List (BitVec (edgeCount 12)) :=
  missing6416_6417 ++ missing6417_6418
abbrev records6416_6418 : List Blob :=
  records6416_6417 ++ records6417_6418
theorem aligned6416_6418 :
    AlignedValid 12 3 missing6416_6418 records6416_6418 :=
  aligned6416_6417.append aligned6417_6418

def missing6418_6419 : List (BitVec (edgeCount 12)) :=
  [missing6418]
abbrev records6418_6419 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6418]
theorem aligned6418_6419 :
    AlignedValid 12 3 missing6418_6419 records6418_6419 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6418
    maskCheck6418 AlignedValid.nil

def missing6419_6420 : List (BitVec (edgeCount 12)) :=
  [missing6419]
abbrev records6419_6420 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6419]
theorem aligned6419_6420 :
    AlignedValid 12 3 missing6419_6420 records6419_6420 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6419
    maskCheck6419 AlignedValid.nil

def missing6418_6420 : List (BitVec (edgeCount 12)) :=
  missing6418_6419 ++ missing6419_6420
abbrev records6418_6420 : List Blob :=
  records6418_6419 ++ records6419_6420
theorem aligned6418_6420 :
    AlignedValid 12 3 missing6418_6420 records6418_6420 :=
  aligned6418_6419.append aligned6419_6420

def missing6416_6420 : List (BitVec (edgeCount 12)) :=
  missing6416_6418 ++ missing6418_6420
abbrev records6416_6420 : List Blob :=
  records6416_6418 ++ records6418_6420
theorem aligned6416_6420 :
    AlignedValid 12 3 missing6416_6420 records6416_6420 :=
  aligned6416_6418.append aligned6418_6420

def missing6420_6421 : List (BitVec (edgeCount 12)) :=
  [missing6420]
abbrev records6420_6421 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6420]
theorem aligned6420_6421 :
    AlignedValid 12 3 missing6420_6421 records6420_6421 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6420
    maskCheck6420 AlignedValid.nil

def missing6421_6422 : List (BitVec (edgeCount 12)) :=
  [missing6421]
abbrev records6421_6422 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6421]
theorem aligned6421_6422 :
    AlignedValid 12 3 missing6421_6422 records6421_6422 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6421
    maskCheck6421 AlignedValid.nil

def missing6420_6422 : List (BitVec (edgeCount 12)) :=
  missing6420_6421 ++ missing6421_6422
abbrev records6420_6422 : List Blob :=
  records6420_6421 ++ records6421_6422
theorem aligned6420_6422 :
    AlignedValid 12 3 missing6420_6422 records6420_6422 :=
  aligned6420_6421.append aligned6421_6422

def missing6422_6423 : List (BitVec (edgeCount 12)) :=
  [missing6422]
abbrev records6422_6423 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6422]
theorem aligned6422_6423 :
    AlignedValid 12 3 missing6422_6423 records6422_6423 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6422
    maskCheck6422 AlignedValid.nil

def missing6423_6424 : List (BitVec (edgeCount 12)) :=
  [missing6423]
abbrev records6423_6424 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6423]
theorem aligned6423_6424 :
    AlignedValid 12 3 missing6423_6424 records6423_6424 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6423
    maskCheck6423 AlignedValid.nil

def missing6422_6424 : List (BitVec (edgeCount 12)) :=
  missing6422_6423 ++ missing6423_6424
abbrev records6422_6424 : List Blob :=
  records6422_6423 ++ records6423_6424
theorem aligned6422_6424 :
    AlignedValid 12 3 missing6422_6424 records6422_6424 :=
  aligned6422_6423.append aligned6423_6424

def missing6420_6424 : List (BitVec (edgeCount 12)) :=
  missing6420_6422 ++ missing6422_6424
abbrev records6420_6424 : List Blob :=
  records6420_6422 ++ records6422_6424
theorem aligned6420_6424 :
    AlignedValid 12 3 missing6420_6424 records6420_6424 :=
  aligned6420_6422.append aligned6422_6424

def missing6416_6424 : List (BitVec (edgeCount 12)) :=
  missing6416_6420 ++ missing6420_6424
abbrev records6416_6424 : List Blob :=
  records6416_6420 ++ records6420_6424
theorem aligned6416_6424 :
    AlignedValid 12 3 missing6416_6424 records6416_6424 :=
  aligned6416_6420.append aligned6420_6424

def missing6424_6425 : List (BitVec (edgeCount 12)) :=
  [missing6424]
abbrev records6424_6425 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6424]
theorem aligned6424_6425 :
    AlignedValid 12 3 missing6424_6425 records6424_6425 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6424
    maskCheck6424 AlignedValid.nil

def missing6425_6426 : List (BitVec (edgeCount 12)) :=
  [missing6425]
abbrev records6425_6426 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6425]
theorem aligned6425_6426 :
    AlignedValid 12 3 missing6425_6426 records6425_6426 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6425
    maskCheck6425 AlignedValid.nil

def missing6424_6426 : List (BitVec (edgeCount 12)) :=
  missing6424_6425 ++ missing6425_6426
abbrev records6424_6426 : List Blob :=
  records6424_6425 ++ records6425_6426
theorem aligned6424_6426 :
    AlignedValid 12 3 missing6424_6426 records6424_6426 :=
  aligned6424_6425.append aligned6425_6426

def missing6426_6427 : List (BitVec (edgeCount 12)) :=
  [missing6426]
abbrev records6426_6427 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6426]
theorem aligned6426_6427 :
    AlignedValid 12 3 missing6426_6427 records6426_6427 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6426
    maskCheck6426 AlignedValid.nil

def missing6427_6428 : List (BitVec (edgeCount 12)) :=
  [missing6427]
abbrev records6427_6428 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6427]
theorem aligned6427_6428 :
    AlignedValid 12 3 missing6427_6428 records6427_6428 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6427
    maskCheck6427 AlignedValid.nil

def missing6426_6428 : List (BitVec (edgeCount 12)) :=
  missing6426_6427 ++ missing6427_6428
abbrev records6426_6428 : List Blob :=
  records6426_6427 ++ records6427_6428
theorem aligned6426_6428 :
    AlignedValid 12 3 missing6426_6428 records6426_6428 :=
  aligned6426_6427.append aligned6427_6428

def missing6424_6428 : List (BitVec (edgeCount 12)) :=
  missing6424_6426 ++ missing6426_6428
abbrev records6424_6428 : List Blob :=
  records6424_6426 ++ records6426_6428
theorem aligned6424_6428 :
    AlignedValid 12 3 missing6424_6428 records6424_6428 :=
  aligned6424_6426.append aligned6426_6428

def missing6428_6429 : List (BitVec (edgeCount 12)) :=
  [missing6428]
abbrev records6428_6429 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6428]
theorem aligned6428_6429 :
    AlignedValid 12 3 missing6428_6429 records6428_6429 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6428
    maskCheck6428 AlignedValid.nil

def missing6429_6430 : List (BitVec (edgeCount 12)) :=
  [missing6429]
abbrev records6429_6430 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6429]
theorem aligned6429_6430 :
    AlignedValid 12 3 missing6429_6430 records6429_6430 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6429
    maskCheck6429 AlignedValid.nil

def missing6428_6430 : List (BitVec (edgeCount 12)) :=
  missing6428_6429 ++ missing6429_6430
abbrev records6428_6430 : List Blob :=
  records6428_6429 ++ records6429_6430
theorem aligned6428_6430 :
    AlignedValid 12 3 missing6428_6430 records6428_6430 :=
  aligned6428_6429.append aligned6429_6430

def missing6430_6431 : List (BitVec (edgeCount 12)) :=
  [missing6430]
abbrev records6430_6431 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6430]
theorem aligned6430_6431 :
    AlignedValid 12 3 missing6430_6431 records6430_6431 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6430
    maskCheck6430 AlignedValid.nil

def missing6431_6432 : List (BitVec (edgeCount 12)) :=
  [missing6431]
abbrev records6431_6432 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6431]
theorem aligned6431_6432 :
    AlignedValid 12 3 missing6431_6432 records6431_6432 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6431
    maskCheck6431 AlignedValid.nil

def missing6430_6432 : List (BitVec (edgeCount 12)) :=
  missing6430_6431 ++ missing6431_6432
abbrev records6430_6432 : List Blob :=
  records6430_6431 ++ records6431_6432
theorem aligned6430_6432 :
    AlignedValid 12 3 missing6430_6432 records6430_6432 :=
  aligned6430_6431.append aligned6431_6432

def missing6428_6432 : List (BitVec (edgeCount 12)) :=
  missing6428_6430 ++ missing6430_6432
abbrev records6428_6432 : List Blob :=
  records6428_6430 ++ records6430_6432
theorem aligned6428_6432 :
    AlignedValid 12 3 missing6428_6432 records6428_6432 :=
  aligned6428_6430.append aligned6430_6432

def missing6424_6432 : List (BitVec (edgeCount 12)) :=
  missing6424_6428 ++ missing6428_6432
abbrev records6424_6432 : List Blob :=
  records6424_6428 ++ records6428_6432
theorem aligned6424_6432 :
    AlignedValid 12 3 missing6424_6432 records6424_6432 :=
  aligned6424_6428.append aligned6428_6432

def missing6416_6432 : List (BitVec (edgeCount 12)) :=
  missing6416_6424 ++ missing6424_6432
abbrev records6416_6432 : List Blob :=
  records6416_6424 ++ records6424_6432
theorem aligned6416_6432 :
    AlignedValid 12 3 missing6416_6432 records6416_6432 :=
  aligned6416_6424.append aligned6424_6432

def missing6400_6432 : List (BitVec (edgeCount 12)) :=
  missing6400_6416 ++ missing6416_6432
abbrev records6400_6432 : List Blob :=
  records6400_6416 ++ records6416_6432
theorem aligned6400_6432 :
    AlignedValid 12 3 missing6400_6432 records6400_6432 :=
  aligned6400_6416.append aligned6416_6432

def missing6432_6433 : List (BitVec (edgeCount 12)) :=
  [missing6432]
abbrev records6432_6433 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6432]
theorem aligned6432_6433 :
    AlignedValid 12 3 missing6432_6433 records6432_6433 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6432
    maskCheck6432 AlignedValid.nil

def missing6433_6434 : List (BitVec (edgeCount 12)) :=
  [missing6433]
abbrev records6433_6434 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6433]
theorem aligned6433_6434 :
    AlignedValid 12 3 missing6433_6434 records6433_6434 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6433
    maskCheck6433 AlignedValid.nil

def missing6432_6434 : List (BitVec (edgeCount 12)) :=
  missing6432_6433 ++ missing6433_6434
abbrev records6432_6434 : List Blob :=
  records6432_6433 ++ records6433_6434
theorem aligned6432_6434 :
    AlignedValid 12 3 missing6432_6434 records6432_6434 :=
  aligned6432_6433.append aligned6433_6434

def missing6434_6435 : List (BitVec (edgeCount 12)) :=
  [missing6434]
abbrev records6434_6435 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6434]
theorem aligned6434_6435 :
    AlignedValid 12 3 missing6434_6435 records6434_6435 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6434
    maskCheck6434 AlignedValid.nil

def missing6435_6436 : List (BitVec (edgeCount 12)) :=
  [missing6435]
abbrev records6435_6436 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6435]
theorem aligned6435_6436 :
    AlignedValid 12 3 missing6435_6436 records6435_6436 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6435
    maskCheck6435 AlignedValid.nil

def missing6434_6436 : List (BitVec (edgeCount 12)) :=
  missing6434_6435 ++ missing6435_6436
abbrev records6434_6436 : List Blob :=
  records6434_6435 ++ records6435_6436
theorem aligned6434_6436 :
    AlignedValid 12 3 missing6434_6436 records6434_6436 :=
  aligned6434_6435.append aligned6435_6436

def missing6432_6436 : List (BitVec (edgeCount 12)) :=
  missing6432_6434 ++ missing6434_6436
abbrev records6432_6436 : List Blob :=
  records6432_6434 ++ records6434_6436
theorem aligned6432_6436 :
    AlignedValid 12 3 missing6432_6436 records6432_6436 :=
  aligned6432_6434.append aligned6434_6436

def missing6436_6437 : List (BitVec (edgeCount 12)) :=
  [missing6436]
abbrev records6436_6437 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6436]
theorem aligned6436_6437 :
    AlignedValid 12 3 missing6436_6437 records6436_6437 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6436
    maskCheck6436 AlignedValid.nil

def missing6437_6438 : List (BitVec (edgeCount 12)) :=
  [missing6437]
abbrev records6437_6438 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6437]
theorem aligned6437_6438 :
    AlignedValid 12 3 missing6437_6438 records6437_6438 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6437
    maskCheck6437 AlignedValid.nil

def missing6436_6438 : List (BitVec (edgeCount 12)) :=
  missing6436_6437 ++ missing6437_6438
abbrev records6436_6438 : List Blob :=
  records6436_6437 ++ records6437_6438
theorem aligned6436_6438 :
    AlignedValid 12 3 missing6436_6438 records6436_6438 :=
  aligned6436_6437.append aligned6437_6438

def missing6438_6439 : List (BitVec (edgeCount 12)) :=
  [missing6438]
abbrev records6438_6439 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6438]
theorem aligned6438_6439 :
    AlignedValid 12 3 missing6438_6439 records6438_6439 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6438
    maskCheck6438 AlignedValid.nil

def missing6439_6440 : List (BitVec (edgeCount 12)) :=
  [missing6439]
abbrev records6439_6440 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6439]
theorem aligned6439_6440 :
    AlignedValid 12 3 missing6439_6440 records6439_6440 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6439
    maskCheck6439 AlignedValid.nil

def missing6438_6440 : List (BitVec (edgeCount 12)) :=
  missing6438_6439 ++ missing6439_6440
abbrev records6438_6440 : List Blob :=
  records6438_6439 ++ records6439_6440
theorem aligned6438_6440 :
    AlignedValid 12 3 missing6438_6440 records6438_6440 :=
  aligned6438_6439.append aligned6439_6440

def missing6436_6440 : List (BitVec (edgeCount 12)) :=
  missing6436_6438 ++ missing6438_6440
abbrev records6436_6440 : List Blob :=
  records6436_6438 ++ records6438_6440
theorem aligned6436_6440 :
    AlignedValid 12 3 missing6436_6440 records6436_6440 :=
  aligned6436_6438.append aligned6438_6440

def missing6432_6440 : List (BitVec (edgeCount 12)) :=
  missing6432_6436 ++ missing6436_6440
abbrev records6432_6440 : List Blob :=
  records6432_6436 ++ records6436_6440
theorem aligned6432_6440 :
    AlignedValid 12 3 missing6432_6440 records6432_6440 :=
  aligned6432_6436.append aligned6436_6440

def missing6440_6441 : List (BitVec (edgeCount 12)) :=
  [missing6440]
abbrev records6440_6441 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6440]
theorem aligned6440_6441 :
    AlignedValid 12 3 missing6440_6441 records6440_6441 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6440
    maskCheck6440 AlignedValid.nil

def missing6441_6442 : List (BitVec (edgeCount 12)) :=
  [missing6441]
abbrev records6441_6442 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6441]
theorem aligned6441_6442 :
    AlignedValid 12 3 missing6441_6442 records6441_6442 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6441
    maskCheck6441 AlignedValid.nil

def missing6440_6442 : List (BitVec (edgeCount 12)) :=
  missing6440_6441 ++ missing6441_6442
abbrev records6440_6442 : List Blob :=
  records6440_6441 ++ records6441_6442
theorem aligned6440_6442 :
    AlignedValid 12 3 missing6440_6442 records6440_6442 :=
  aligned6440_6441.append aligned6441_6442

def missing6442_6443 : List (BitVec (edgeCount 12)) :=
  [missing6442]
abbrev records6442_6443 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6442]
theorem aligned6442_6443 :
    AlignedValid 12 3 missing6442_6443 records6442_6443 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6442
    maskCheck6442 AlignedValid.nil

def missing6443_6444 : List (BitVec (edgeCount 12)) :=
  [missing6443]
abbrev records6443_6444 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6443]
theorem aligned6443_6444 :
    AlignedValid 12 3 missing6443_6444 records6443_6444 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6443
    maskCheck6443 AlignedValid.nil

def missing6442_6444 : List (BitVec (edgeCount 12)) :=
  missing6442_6443 ++ missing6443_6444
abbrev records6442_6444 : List Blob :=
  records6442_6443 ++ records6443_6444
theorem aligned6442_6444 :
    AlignedValid 12 3 missing6442_6444 records6442_6444 :=
  aligned6442_6443.append aligned6443_6444

def missing6440_6444 : List (BitVec (edgeCount 12)) :=
  missing6440_6442 ++ missing6442_6444
abbrev records6440_6444 : List Blob :=
  records6440_6442 ++ records6442_6444
theorem aligned6440_6444 :
    AlignedValid 12 3 missing6440_6444 records6440_6444 :=
  aligned6440_6442.append aligned6442_6444

def missing6444_6445 : List (BitVec (edgeCount 12)) :=
  [missing6444]
abbrev records6444_6445 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6444]
theorem aligned6444_6445 :
    AlignedValid 12 3 missing6444_6445 records6444_6445 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6444
    maskCheck6444 AlignedValid.nil

def missing6445_6446 : List (BitVec (edgeCount 12)) :=
  [missing6445]
abbrev records6445_6446 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6445]
theorem aligned6445_6446 :
    AlignedValid 12 3 missing6445_6446 records6445_6446 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6445
    maskCheck6445 AlignedValid.nil

def missing6444_6446 : List (BitVec (edgeCount 12)) :=
  missing6444_6445 ++ missing6445_6446
abbrev records6444_6446 : List Blob :=
  records6444_6445 ++ records6445_6446
theorem aligned6444_6446 :
    AlignedValid 12 3 missing6444_6446 records6444_6446 :=
  aligned6444_6445.append aligned6445_6446

def missing6446_6447 : List (BitVec (edgeCount 12)) :=
  [missing6446]
abbrev records6446_6447 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6446]
theorem aligned6446_6447 :
    AlignedValid 12 3 missing6446_6447 records6446_6447 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6446
    maskCheck6446 AlignedValid.nil

def missing6447_6448 : List (BitVec (edgeCount 12)) :=
  [missing6447]
abbrev records6447_6448 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6447]
theorem aligned6447_6448 :
    AlignedValid 12 3 missing6447_6448 records6447_6448 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6447
    maskCheck6447 AlignedValid.nil

def missing6446_6448 : List (BitVec (edgeCount 12)) :=
  missing6446_6447 ++ missing6447_6448
abbrev records6446_6448 : List Blob :=
  records6446_6447 ++ records6447_6448
theorem aligned6446_6448 :
    AlignedValid 12 3 missing6446_6448 records6446_6448 :=
  aligned6446_6447.append aligned6447_6448

def missing6444_6448 : List (BitVec (edgeCount 12)) :=
  missing6444_6446 ++ missing6446_6448
abbrev records6444_6448 : List Blob :=
  records6444_6446 ++ records6446_6448
theorem aligned6444_6448 :
    AlignedValid 12 3 missing6444_6448 records6444_6448 :=
  aligned6444_6446.append aligned6446_6448

def missing6440_6448 : List (BitVec (edgeCount 12)) :=
  missing6440_6444 ++ missing6444_6448
abbrev records6440_6448 : List Blob :=
  records6440_6444 ++ records6444_6448
theorem aligned6440_6448 :
    AlignedValid 12 3 missing6440_6448 records6440_6448 :=
  aligned6440_6444.append aligned6444_6448

def missing6432_6448 : List (BitVec (edgeCount 12)) :=
  missing6432_6440 ++ missing6440_6448
abbrev records6432_6448 : List Blob :=
  records6432_6440 ++ records6440_6448
theorem aligned6432_6448 :
    AlignedValid 12 3 missing6432_6448 records6432_6448 :=
  aligned6432_6440.append aligned6440_6448

def missing6448_6449 : List (BitVec (edgeCount 12)) :=
  [missing6448]
abbrev records6448_6449 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6448]
theorem aligned6448_6449 :
    AlignedValid 12 3 missing6448_6449 records6448_6449 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6448
    maskCheck6448 AlignedValid.nil

def missing6449_6450 : List (BitVec (edgeCount 12)) :=
  [missing6449]
abbrev records6449_6450 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6449]
theorem aligned6449_6450 :
    AlignedValid 12 3 missing6449_6450 records6449_6450 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6449
    maskCheck6449 AlignedValid.nil

def missing6448_6450 : List (BitVec (edgeCount 12)) :=
  missing6448_6449 ++ missing6449_6450
abbrev records6448_6450 : List Blob :=
  records6448_6449 ++ records6449_6450
theorem aligned6448_6450 :
    AlignedValid 12 3 missing6448_6450 records6448_6450 :=
  aligned6448_6449.append aligned6449_6450

def missing6450_6451 : List (BitVec (edgeCount 12)) :=
  [missing6450]
abbrev records6450_6451 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6450]
theorem aligned6450_6451 :
    AlignedValid 12 3 missing6450_6451 records6450_6451 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6450
    maskCheck6450 AlignedValid.nil

def missing6451_6452 : List (BitVec (edgeCount 12)) :=
  [missing6451]
abbrev records6451_6452 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6451]
theorem aligned6451_6452 :
    AlignedValid 12 3 missing6451_6452 records6451_6452 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6451
    maskCheck6451 AlignedValid.nil

def missing6450_6452 : List (BitVec (edgeCount 12)) :=
  missing6450_6451 ++ missing6451_6452
abbrev records6450_6452 : List Blob :=
  records6450_6451 ++ records6451_6452
theorem aligned6450_6452 :
    AlignedValid 12 3 missing6450_6452 records6450_6452 :=
  aligned6450_6451.append aligned6451_6452

def missing6448_6452 : List (BitVec (edgeCount 12)) :=
  missing6448_6450 ++ missing6450_6452
abbrev records6448_6452 : List Blob :=
  records6448_6450 ++ records6450_6452
theorem aligned6448_6452 :
    AlignedValid 12 3 missing6448_6452 records6448_6452 :=
  aligned6448_6450.append aligned6450_6452

def missing6452_6453 : List (BitVec (edgeCount 12)) :=
  [missing6452]
abbrev records6452_6453 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6452]
theorem aligned6452_6453 :
    AlignedValid 12 3 missing6452_6453 records6452_6453 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6452
    maskCheck6452 AlignedValid.nil

def missing6453_6454 : List (BitVec (edgeCount 12)) :=
  [missing6453]
abbrev records6453_6454 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6453]
theorem aligned6453_6454 :
    AlignedValid 12 3 missing6453_6454 records6453_6454 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6453
    maskCheck6453 AlignedValid.nil

def missing6452_6454 : List (BitVec (edgeCount 12)) :=
  missing6452_6453 ++ missing6453_6454
abbrev records6452_6454 : List Blob :=
  records6452_6453 ++ records6453_6454
theorem aligned6452_6454 :
    AlignedValid 12 3 missing6452_6454 records6452_6454 :=
  aligned6452_6453.append aligned6453_6454

def missing6454_6455 : List (BitVec (edgeCount 12)) :=
  [missing6454]
abbrev records6454_6455 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6454]
theorem aligned6454_6455 :
    AlignedValid 12 3 missing6454_6455 records6454_6455 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6454
    maskCheck6454 AlignedValid.nil

def missing6455_6456 : List (BitVec (edgeCount 12)) :=
  [missing6455]
abbrev records6455_6456 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6455]
theorem aligned6455_6456 :
    AlignedValid 12 3 missing6455_6456 records6455_6456 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6455
    maskCheck6455 AlignedValid.nil

def missing6454_6456 : List (BitVec (edgeCount 12)) :=
  missing6454_6455 ++ missing6455_6456
abbrev records6454_6456 : List Blob :=
  records6454_6455 ++ records6455_6456
theorem aligned6454_6456 :
    AlignedValid 12 3 missing6454_6456 records6454_6456 :=
  aligned6454_6455.append aligned6455_6456

def missing6452_6456 : List (BitVec (edgeCount 12)) :=
  missing6452_6454 ++ missing6454_6456
abbrev records6452_6456 : List Blob :=
  records6452_6454 ++ records6454_6456
theorem aligned6452_6456 :
    AlignedValid 12 3 missing6452_6456 records6452_6456 :=
  aligned6452_6454.append aligned6454_6456

def missing6448_6456 : List (BitVec (edgeCount 12)) :=
  missing6448_6452 ++ missing6452_6456
abbrev records6448_6456 : List Blob :=
  records6448_6452 ++ records6452_6456
theorem aligned6448_6456 :
    AlignedValid 12 3 missing6448_6456 records6448_6456 :=
  aligned6448_6452.append aligned6452_6456

def missing6456_6457 : List (BitVec (edgeCount 12)) :=
  [missing6456]
abbrev records6456_6457 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6456]
theorem aligned6456_6457 :
    AlignedValid 12 3 missing6456_6457 records6456_6457 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6456
    maskCheck6456 AlignedValid.nil

def missing6457_6458 : List (BitVec (edgeCount 12)) :=
  [missing6457]
abbrev records6457_6458 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6457]
theorem aligned6457_6458 :
    AlignedValid 12 3 missing6457_6458 records6457_6458 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6457
    maskCheck6457 AlignedValid.nil

def missing6456_6458 : List (BitVec (edgeCount 12)) :=
  missing6456_6457 ++ missing6457_6458
abbrev records6456_6458 : List Blob :=
  records6456_6457 ++ records6457_6458
theorem aligned6456_6458 :
    AlignedValid 12 3 missing6456_6458 records6456_6458 :=
  aligned6456_6457.append aligned6457_6458

def missing6458_6459 : List (BitVec (edgeCount 12)) :=
  [missing6458]
abbrev records6458_6459 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6458]
theorem aligned6458_6459 :
    AlignedValid 12 3 missing6458_6459 records6458_6459 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6458
    maskCheck6458 AlignedValid.nil

def missing6459_6460 : List (BitVec (edgeCount 12)) :=
  [missing6459]
abbrev records6459_6460 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6459]
theorem aligned6459_6460 :
    AlignedValid 12 3 missing6459_6460 records6459_6460 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6459
    maskCheck6459 AlignedValid.nil

def missing6458_6460 : List (BitVec (edgeCount 12)) :=
  missing6458_6459 ++ missing6459_6460
abbrev records6458_6460 : List Blob :=
  records6458_6459 ++ records6459_6460
theorem aligned6458_6460 :
    AlignedValid 12 3 missing6458_6460 records6458_6460 :=
  aligned6458_6459.append aligned6459_6460

def missing6456_6460 : List (BitVec (edgeCount 12)) :=
  missing6456_6458 ++ missing6458_6460
abbrev records6456_6460 : List Blob :=
  records6456_6458 ++ records6458_6460
theorem aligned6456_6460 :
    AlignedValid 12 3 missing6456_6460 records6456_6460 :=
  aligned6456_6458.append aligned6458_6460

def missing6460_6461 : List (BitVec (edgeCount 12)) :=
  [missing6460]
abbrev records6460_6461 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6460]
theorem aligned6460_6461 :
    AlignedValid 12 3 missing6460_6461 records6460_6461 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6460
    maskCheck6460 AlignedValid.nil

def missing6461_6462 : List (BitVec (edgeCount 12)) :=
  [missing6461]
abbrev records6461_6462 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6461]
theorem aligned6461_6462 :
    AlignedValid 12 3 missing6461_6462 records6461_6462 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6461
    maskCheck6461 AlignedValid.nil

def missing6460_6462 : List (BitVec (edgeCount 12)) :=
  missing6460_6461 ++ missing6461_6462
abbrev records6460_6462 : List Blob :=
  records6460_6461 ++ records6461_6462
theorem aligned6460_6462 :
    AlignedValid 12 3 missing6460_6462 records6460_6462 :=
  aligned6460_6461.append aligned6461_6462

def missing6462_6463 : List (BitVec (edgeCount 12)) :=
  [missing6462]
abbrev records6462_6463 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6462]
theorem aligned6462_6463 :
    AlignedValid 12 3 missing6462_6463 records6462_6463 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6462
    maskCheck6462 AlignedValid.nil

def missing6463_6464 : List (BitVec (edgeCount 12)) :=
  [missing6463]
abbrev records6463_6464 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6463]
theorem aligned6463_6464 :
    AlignedValid 12 3 missing6463_6464 records6463_6464 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6463
    maskCheck6463 AlignedValid.nil

def missing6462_6464 : List (BitVec (edgeCount 12)) :=
  missing6462_6463 ++ missing6463_6464
abbrev records6462_6464 : List Blob :=
  records6462_6463 ++ records6463_6464
theorem aligned6462_6464 :
    AlignedValid 12 3 missing6462_6464 records6462_6464 :=
  aligned6462_6463.append aligned6463_6464

def missing6460_6464 : List (BitVec (edgeCount 12)) :=
  missing6460_6462 ++ missing6462_6464
abbrev records6460_6464 : List Blob :=
  records6460_6462 ++ records6462_6464
theorem aligned6460_6464 :
    AlignedValid 12 3 missing6460_6464 records6460_6464 :=
  aligned6460_6462.append aligned6462_6464

def missing6456_6464 : List (BitVec (edgeCount 12)) :=
  missing6456_6460 ++ missing6460_6464
abbrev records6456_6464 : List Blob :=
  records6456_6460 ++ records6460_6464
theorem aligned6456_6464 :
    AlignedValid 12 3 missing6456_6464 records6456_6464 :=
  aligned6456_6460.append aligned6460_6464

def missing6448_6464 : List (BitVec (edgeCount 12)) :=
  missing6448_6456 ++ missing6456_6464
abbrev records6448_6464 : List Blob :=
  records6448_6456 ++ records6456_6464
theorem aligned6448_6464 :
    AlignedValid 12 3 missing6448_6464 records6448_6464 :=
  aligned6448_6456.append aligned6456_6464

def missing6432_6464 : List (BitVec (edgeCount 12)) :=
  missing6432_6448 ++ missing6448_6464
abbrev records6432_6464 : List Blob :=
  records6432_6448 ++ records6448_6464
theorem aligned6432_6464 :
    AlignedValid 12 3 missing6432_6464 records6432_6464 :=
  aligned6432_6448.append aligned6448_6464

def missing6400_6464 : List (BitVec (edgeCount 12)) :=
  missing6400_6432 ++ missing6432_6464
abbrev records6400_6464 : List Blob :=
  records6400_6432 ++ records6432_6464
theorem aligned6400_6464 :
    AlignedValid 12 3 missing6400_6464 records6400_6464 :=
  aligned6400_6432.append aligned6432_6464

def missing6464_6465 : List (BitVec (edgeCount 12)) :=
  [missing6464]
abbrev records6464_6465 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6464]
theorem aligned6464_6465 :
    AlignedValid 12 3 missing6464_6465 records6464_6465 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6464
    maskCheck6464 AlignedValid.nil

def missing6465_6466 : List (BitVec (edgeCount 12)) :=
  [missing6465]
abbrev records6465_6466 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6465]
theorem aligned6465_6466 :
    AlignedValid 12 3 missing6465_6466 records6465_6466 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6465
    maskCheck6465 AlignedValid.nil

def missing6464_6466 : List (BitVec (edgeCount 12)) :=
  missing6464_6465 ++ missing6465_6466
abbrev records6464_6466 : List Blob :=
  records6464_6465 ++ records6465_6466
theorem aligned6464_6466 :
    AlignedValid 12 3 missing6464_6466 records6464_6466 :=
  aligned6464_6465.append aligned6465_6466

def missing6466_6467 : List (BitVec (edgeCount 12)) :=
  [missing6466]
abbrev records6466_6467 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6466]
theorem aligned6466_6467 :
    AlignedValid 12 3 missing6466_6467 records6466_6467 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6466
    maskCheck6466 AlignedValid.nil

def missing6467_6468 : List (BitVec (edgeCount 12)) :=
  [missing6467]
abbrev records6467_6468 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6467]
theorem aligned6467_6468 :
    AlignedValid 12 3 missing6467_6468 records6467_6468 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6467
    maskCheck6467 AlignedValid.nil

def missing6466_6468 : List (BitVec (edgeCount 12)) :=
  missing6466_6467 ++ missing6467_6468
abbrev records6466_6468 : List Blob :=
  records6466_6467 ++ records6467_6468
theorem aligned6466_6468 :
    AlignedValid 12 3 missing6466_6468 records6466_6468 :=
  aligned6466_6467.append aligned6467_6468

def missing6464_6468 : List (BitVec (edgeCount 12)) :=
  missing6464_6466 ++ missing6466_6468
abbrev records6464_6468 : List Blob :=
  records6464_6466 ++ records6466_6468
theorem aligned6464_6468 :
    AlignedValid 12 3 missing6464_6468 records6464_6468 :=
  aligned6464_6466.append aligned6466_6468

def missing6468_6469 : List (BitVec (edgeCount 12)) :=
  [missing6468]
abbrev records6468_6469 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6468]
theorem aligned6468_6469 :
    AlignedValid 12 3 missing6468_6469 records6468_6469 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6468
    maskCheck6468 AlignedValid.nil

def missing6469_6470 : List (BitVec (edgeCount 12)) :=
  [missing6469]
abbrev records6469_6470 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6469]
theorem aligned6469_6470 :
    AlignedValid 12 3 missing6469_6470 records6469_6470 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6469
    maskCheck6469 AlignedValid.nil

def missing6468_6470 : List (BitVec (edgeCount 12)) :=
  missing6468_6469 ++ missing6469_6470
abbrev records6468_6470 : List Blob :=
  records6468_6469 ++ records6469_6470
theorem aligned6468_6470 :
    AlignedValid 12 3 missing6468_6470 records6468_6470 :=
  aligned6468_6469.append aligned6469_6470

def missing6470_6471 : List (BitVec (edgeCount 12)) :=
  [missing6470]
abbrev records6470_6471 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6470]
theorem aligned6470_6471 :
    AlignedValid 12 3 missing6470_6471 records6470_6471 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6470
    maskCheck6470 AlignedValid.nil

def missing6471_6472 : List (BitVec (edgeCount 12)) :=
  [missing6471]
abbrev records6471_6472 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6471]
theorem aligned6471_6472 :
    AlignedValid 12 3 missing6471_6472 records6471_6472 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6471
    maskCheck6471 AlignedValid.nil

def missing6470_6472 : List (BitVec (edgeCount 12)) :=
  missing6470_6471 ++ missing6471_6472
abbrev records6470_6472 : List Blob :=
  records6470_6471 ++ records6471_6472
theorem aligned6470_6472 :
    AlignedValid 12 3 missing6470_6472 records6470_6472 :=
  aligned6470_6471.append aligned6471_6472

def missing6468_6472 : List (BitVec (edgeCount 12)) :=
  missing6468_6470 ++ missing6470_6472
abbrev records6468_6472 : List Blob :=
  records6468_6470 ++ records6470_6472
theorem aligned6468_6472 :
    AlignedValid 12 3 missing6468_6472 records6468_6472 :=
  aligned6468_6470.append aligned6470_6472

def missing6464_6472 : List (BitVec (edgeCount 12)) :=
  missing6464_6468 ++ missing6468_6472
abbrev records6464_6472 : List Blob :=
  records6464_6468 ++ records6468_6472
theorem aligned6464_6472 :
    AlignedValid 12 3 missing6464_6472 records6464_6472 :=
  aligned6464_6468.append aligned6468_6472

def missing6472_6473 : List (BitVec (edgeCount 12)) :=
  [missing6472]
abbrev records6472_6473 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6472]
theorem aligned6472_6473 :
    AlignedValid 12 3 missing6472_6473 records6472_6473 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6472
    maskCheck6472 AlignedValid.nil

def missing6473_6474 : List (BitVec (edgeCount 12)) :=
  [missing6473]
abbrev records6473_6474 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6473]
theorem aligned6473_6474 :
    AlignedValid 12 3 missing6473_6474 records6473_6474 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6473
    maskCheck6473 AlignedValid.nil

def missing6472_6474 : List (BitVec (edgeCount 12)) :=
  missing6472_6473 ++ missing6473_6474
abbrev records6472_6474 : List Blob :=
  records6472_6473 ++ records6473_6474
theorem aligned6472_6474 :
    AlignedValid 12 3 missing6472_6474 records6472_6474 :=
  aligned6472_6473.append aligned6473_6474

def missing6474_6475 : List (BitVec (edgeCount 12)) :=
  [missing6474]
abbrev records6474_6475 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6474]
theorem aligned6474_6475 :
    AlignedValid 12 3 missing6474_6475 records6474_6475 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6474
    maskCheck6474 AlignedValid.nil

def missing6475_6476 : List (BitVec (edgeCount 12)) :=
  [missing6475]
abbrev records6475_6476 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6475]
theorem aligned6475_6476 :
    AlignedValid 12 3 missing6475_6476 records6475_6476 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6475
    maskCheck6475 AlignedValid.nil

def missing6474_6476 : List (BitVec (edgeCount 12)) :=
  missing6474_6475 ++ missing6475_6476
abbrev records6474_6476 : List Blob :=
  records6474_6475 ++ records6475_6476
theorem aligned6474_6476 :
    AlignedValid 12 3 missing6474_6476 records6474_6476 :=
  aligned6474_6475.append aligned6475_6476

def missing6472_6476 : List (BitVec (edgeCount 12)) :=
  missing6472_6474 ++ missing6474_6476
abbrev records6472_6476 : List Blob :=
  records6472_6474 ++ records6474_6476
theorem aligned6472_6476 :
    AlignedValid 12 3 missing6472_6476 records6472_6476 :=
  aligned6472_6474.append aligned6474_6476

def missing6476_6477 : List (BitVec (edgeCount 12)) :=
  [missing6476]
abbrev records6476_6477 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6476]
theorem aligned6476_6477 :
    AlignedValid 12 3 missing6476_6477 records6476_6477 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6476
    maskCheck6476 AlignedValid.nil

def missing6477_6478 : List (BitVec (edgeCount 12)) :=
  [missing6477]
abbrev records6477_6478 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6477]
theorem aligned6477_6478 :
    AlignedValid 12 3 missing6477_6478 records6477_6478 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6477
    maskCheck6477 AlignedValid.nil

def missing6476_6478 : List (BitVec (edgeCount 12)) :=
  missing6476_6477 ++ missing6477_6478
abbrev records6476_6478 : List Blob :=
  records6476_6477 ++ records6477_6478
theorem aligned6476_6478 :
    AlignedValid 12 3 missing6476_6478 records6476_6478 :=
  aligned6476_6477.append aligned6477_6478

def missing6478_6479 : List (BitVec (edgeCount 12)) :=
  [missing6478]
abbrev records6478_6479 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6478]
theorem aligned6478_6479 :
    AlignedValid 12 3 missing6478_6479 records6478_6479 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6478
    maskCheck6478 AlignedValid.nil

def missing6479_6480 : List (BitVec (edgeCount 12)) :=
  [missing6479]
abbrev records6479_6480 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6479]
theorem aligned6479_6480 :
    AlignedValid 12 3 missing6479_6480 records6479_6480 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6479
    maskCheck6479 AlignedValid.nil

def missing6478_6480 : List (BitVec (edgeCount 12)) :=
  missing6478_6479 ++ missing6479_6480
abbrev records6478_6480 : List Blob :=
  records6478_6479 ++ records6479_6480
theorem aligned6478_6480 :
    AlignedValid 12 3 missing6478_6480 records6478_6480 :=
  aligned6478_6479.append aligned6479_6480

def missing6476_6480 : List (BitVec (edgeCount 12)) :=
  missing6476_6478 ++ missing6478_6480
abbrev records6476_6480 : List Blob :=
  records6476_6478 ++ records6478_6480
theorem aligned6476_6480 :
    AlignedValid 12 3 missing6476_6480 records6476_6480 :=
  aligned6476_6478.append aligned6478_6480

def missing6472_6480 : List (BitVec (edgeCount 12)) :=
  missing6472_6476 ++ missing6476_6480
abbrev records6472_6480 : List Blob :=
  records6472_6476 ++ records6476_6480
theorem aligned6472_6480 :
    AlignedValid 12 3 missing6472_6480 records6472_6480 :=
  aligned6472_6476.append aligned6476_6480

def missing6464_6480 : List (BitVec (edgeCount 12)) :=
  missing6464_6472 ++ missing6472_6480
abbrev records6464_6480 : List Blob :=
  records6464_6472 ++ records6472_6480
theorem aligned6464_6480 :
    AlignedValid 12 3 missing6464_6480 records6464_6480 :=
  aligned6464_6472.append aligned6472_6480

def missing6480_6481 : List (BitVec (edgeCount 12)) :=
  [missing6480]
abbrev records6480_6481 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6480]
theorem aligned6480_6481 :
    AlignedValid 12 3 missing6480_6481 records6480_6481 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6480
    maskCheck6480 AlignedValid.nil

def missing6481_6482 : List (BitVec (edgeCount 12)) :=
  [missing6481]
abbrev records6481_6482 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6481]
theorem aligned6481_6482 :
    AlignedValid 12 3 missing6481_6482 records6481_6482 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6481
    maskCheck6481 AlignedValid.nil

def missing6480_6482 : List (BitVec (edgeCount 12)) :=
  missing6480_6481 ++ missing6481_6482
abbrev records6480_6482 : List Blob :=
  records6480_6481 ++ records6481_6482
theorem aligned6480_6482 :
    AlignedValid 12 3 missing6480_6482 records6480_6482 :=
  aligned6480_6481.append aligned6481_6482

def missing6482_6483 : List (BitVec (edgeCount 12)) :=
  [missing6482]
abbrev records6482_6483 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6482]
theorem aligned6482_6483 :
    AlignedValid 12 3 missing6482_6483 records6482_6483 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6482
    maskCheck6482 AlignedValid.nil

def missing6483_6484 : List (BitVec (edgeCount 12)) :=
  [missing6483]
abbrev records6483_6484 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6483]
theorem aligned6483_6484 :
    AlignedValid 12 3 missing6483_6484 records6483_6484 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6483
    maskCheck6483 AlignedValid.nil

def missing6482_6484 : List (BitVec (edgeCount 12)) :=
  missing6482_6483 ++ missing6483_6484
abbrev records6482_6484 : List Blob :=
  records6482_6483 ++ records6483_6484
theorem aligned6482_6484 :
    AlignedValid 12 3 missing6482_6484 records6482_6484 :=
  aligned6482_6483.append aligned6483_6484

def missing6480_6484 : List (BitVec (edgeCount 12)) :=
  missing6480_6482 ++ missing6482_6484
abbrev records6480_6484 : List Blob :=
  records6480_6482 ++ records6482_6484
theorem aligned6480_6484 :
    AlignedValid 12 3 missing6480_6484 records6480_6484 :=
  aligned6480_6482.append aligned6482_6484

def missing6484_6485 : List (BitVec (edgeCount 12)) :=
  [missing6484]
abbrev records6484_6485 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6484]
theorem aligned6484_6485 :
    AlignedValid 12 3 missing6484_6485 records6484_6485 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6484
    maskCheck6484 AlignedValid.nil

def missing6485_6486 : List (BitVec (edgeCount 12)) :=
  [missing6485]
abbrev records6485_6486 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6485]
theorem aligned6485_6486 :
    AlignedValid 12 3 missing6485_6486 records6485_6486 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6485
    maskCheck6485 AlignedValid.nil

def missing6484_6486 : List (BitVec (edgeCount 12)) :=
  missing6484_6485 ++ missing6485_6486
abbrev records6484_6486 : List Blob :=
  records6484_6485 ++ records6485_6486
theorem aligned6484_6486 :
    AlignedValid 12 3 missing6484_6486 records6484_6486 :=
  aligned6484_6485.append aligned6485_6486

def missing6486_6487 : List (BitVec (edgeCount 12)) :=
  [missing6486]
abbrev records6486_6487 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6486]
theorem aligned6486_6487 :
    AlignedValid 12 3 missing6486_6487 records6486_6487 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6486
    maskCheck6486 AlignedValid.nil

def missing6487_6488 : List (BitVec (edgeCount 12)) :=
  [missing6487]
abbrev records6487_6488 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6487]
theorem aligned6487_6488 :
    AlignedValid 12 3 missing6487_6488 records6487_6488 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6487
    maskCheck6487 AlignedValid.nil

def missing6486_6488 : List (BitVec (edgeCount 12)) :=
  missing6486_6487 ++ missing6487_6488
abbrev records6486_6488 : List Blob :=
  records6486_6487 ++ records6487_6488
theorem aligned6486_6488 :
    AlignedValid 12 3 missing6486_6488 records6486_6488 :=
  aligned6486_6487.append aligned6487_6488

def missing6484_6488 : List (BitVec (edgeCount 12)) :=
  missing6484_6486 ++ missing6486_6488
abbrev records6484_6488 : List Blob :=
  records6484_6486 ++ records6486_6488
theorem aligned6484_6488 :
    AlignedValid 12 3 missing6484_6488 records6484_6488 :=
  aligned6484_6486.append aligned6486_6488

def missing6480_6488 : List (BitVec (edgeCount 12)) :=
  missing6480_6484 ++ missing6484_6488
abbrev records6480_6488 : List Blob :=
  records6480_6484 ++ records6484_6488
theorem aligned6480_6488 :
    AlignedValid 12 3 missing6480_6488 records6480_6488 :=
  aligned6480_6484.append aligned6484_6488

def missing6488_6489 : List (BitVec (edgeCount 12)) :=
  [missing6488]
abbrev records6488_6489 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6488]
theorem aligned6488_6489 :
    AlignedValid 12 3 missing6488_6489 records6488_6489 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6488
    maskCheck6488 AlignedValid.nil

def missing6489_6490 : List (BitVec (edgeCount 12)) :=
  [missing6489]
abbrev records6489_6490 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6489]
theorem aligned6489_6490 :
    AlignedValid 12 3 missing6489_6490 records6489_6490 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6489
    maskCheck6489 AlignedValid.nil

def missing6488_6490 : List (BitVec (edgeCount 12)) :=
  missing6488_6489 ++ missing6489_6490
abbrev records6488_6490 : List Blob :=
  records6488_6489 ++ records6489_6490
theorem aligned6488_6490 :
    AlignedValid 12 3 missing6488_6490 records6488_6490 :=
  aligned6488_6489.append aligned6489_6490

def missing6490_6491 : List (BitVec (edgeCount 12)) :=
  [missing6490]
abbrev records6490_6491 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6490]
theorem aligned6490_6491 :
    AlignedValid 12 3 missing6490_6491 records6490_6491 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6490
    maskCheck6490 AlignedValid.nil

def missing6491_6492 : List (BitVec (edgeCount 12)) :=
  [missing6491]
abbrev records6491_6492 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6491]
theorem aligned6491_6492 :
    AlignedValid 12 3 missing6491_6492 records6491_6492 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6491
    maskCheck6491 AlignedValid.nil

def missing6490_6492 : List (BitVec (edgeCount 12)) :=
  missing6490_6491 ++ missing6491_6492
abbrev records6490_6492 : List Blob :=
  records6490_6491 ++ records6491_6492
theorem aligned6490_6492 :
    AlignedValid 12 3 missing6490_6492 records6490_6492 :=
  aligned6490_6491.append aligned6491_6492

def missing6488_6492 : List (BitVec (edgeCount 12)) :=
  missing6488_6490 ++ missing6490_6492
abbrev records6488_6492 : List Blob :=
  records6488_6490 ++ records6490_6492
theorem aligned6488_6492 :
    AlignedValid 12 3 missing6488_6492 records6488_6492 :=
  aligned6488_6490.append aligned6490_6492

def missing6492_6493 : List (BitVec (edgeCount 12)) :=
  [missing6492]
abbrev records6492_6493 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6492]
theorem aligned6492_6493 :
    AlignedValid 12 3 missing6492_6493 records6492_6493 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6492
    maskCheck6492 AlignedValid.nil

def missing6493_6494 : List (BitVec (edgeCount 12)) :=
  [missing6493]
abbrev records6493_6494 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6493]
theorem aligned6493_6494 :
    AlignedValid 12 3 missing6493_6494 records6493_6494 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6493
    maskCheck6493 AlignedValid.nil

def missing6492_6494 : List (BitVec (edgeCount 12)) :=
  missing6492_6493 ++ missing6493_6494
abbrev records6492_6494 : List Blob :=
  records6492_6493 ++ records6493_6494
theorem aligned6492_6494 :
    AlignedValid 12 3 missing6492_6494 records6492_6494 :=
  aligned6492_6493.append aligned6493_6494

def missing6494_6495 : List (BitVec (edgeCount 12)) :=
  [missing6494]
abbrev records6494_6495 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6494]
theorem aligned6494_6495 :
    AlignedValid 12 3 missing6494_6495 records6494_6495 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6494
    maskCheck6494 AlignedValid.nil

def missing6495_6496 : List (BitVec (edgeCount 12)) :=
  [missing6495]
abbrev records6495_6496 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6495]
theorem aligned6495_6496 :
    AlignedValid 12 3 missing6495_6496 records6495_6496 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6495
    maskCheck6495 AlignedValid.nil

def missing6494_6496 : List (BitVec (edgeCount 12)) :=
  missing6494_6495 ++ missing6495_6496
abbrev records6494_6496 : List Blob :=
  records6494_6495 ++ records6495_6496
theorem aligned6494_6496 :
    AlignedValid 12 3 missing6494_6496 records6494_6496 :=
  aligned6494_6495.append aligned6495_6496

def missing6492_6496 : List (BitVec (edgeCount 12)) :=
  missing6492_6494 ++ missing6494_6496
abbrev records6492_6496 : List Blob :=
  records6492_6494 ++ records6494_6496
theorem aligned6492_6496 :
    AlignedValid 12 3 missing6492_6496 records6492_6496 :=
  aligned6492_6494.append aligned6494_6496

def missing6488_6496 : List (BitVec (edgeCount 12)) :=
  missing6488_6492 ++ missing6492_6496
abbrev records6488_6496 : List Blob :=
  records6488_6492 ++ records6492_6496
theorem aligned6488_6496 :
    AlignedValid 12 3 missing6488_6496 records6488_6496 :=
  aligned6488_6492.append aligned6492_6496

def missing6480_6496 : List (BitVec (edgeCount 12)) :=
  missing6480_6488 ++ missing6488_6496
abbrev records6480_6496 : List Blob :=
  records6480_6488 ++ records6488_6496
theorem aligned6480_6496 :
    AlignedValid 12 3 missing6480_6496 records6480_6496 :=
  aligned6480_6488.append aligned6488_6496

def missing6464_6496 : List (BitVec (edgeCount 12)) :=
  missing6464_6480 ++ missing6480_6496
abbrev records6464_6496 : List Blob :=
  records6464_6480 ++ records6480_6496
theorem aligned6464_6496 :
    AlignedValid 12 3 missing6464_6496 records6464_6496 :=
  aligned6464_6480.append aligned6480_6496

def missing6496_6497 : List (BitVec (edgeCount 12)) :=
  [missing6496]
abbrev records6496_6497 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6496]
theorem aligned6496_6497 :
    AlignedValid 12 3 missing6496_6497 records6496_6497 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6496
    maskCheck6496 AlignedValid.nil

def missing6497_6498 : List (BitVec (edgeCount 12)) :=
  [missing6497]
abbrev records6497_6498 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6497]
theorem aligned6497_6498 :
    AlignedValid 12 3 missing6497_6498 records6497_6498 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6497
    maskCheck6497 AlignedValid.nil

def missing6496_6498 : List (BitVec (edgeCount 12)) :=
  missing6496_6497 ++ missing6497_6498
abbrev records6496_6498 : List Blob :=
  records6496_6497 ++ records6497_6498
theorem aligned6496_6498 :
    AlignedValid 12 3 missing6496_6498 records6496_6498 :=
  aligned6496_6497.append aligned6497_6498

def missing6498_6499 : List (BitVec (edgeCount 12)) :=
  [missing6498]
abbrev records6498_6499 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6498]
theorem aligned6498_6499 :
    AlignedValid 12 3 missing6498_6499 records6498_6499 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6498
    maskCheck6498 AlignedValid.nil

def missing6499_6500 : List (BitVec (edgeCount 12)) :=
  [missing6499]
abbrev records6499_6500 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6499]
theorem aligned6499_6500 :
    AlignedValid 12 3 missing6499_6500 records6499_6500 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6499
    maskCheck6499 AlignedValid.nil

def missing6498_6500 : List (BitVec (edgeCount 12)) :=
  missing6498_6499 ++ missing6499_6500
abbrev records6498_6500 : List Blob :=
  records6498_6499 ++ records6499_6500
theorem aligned6498_6500 :
    AlignedValid 12 3 missing6498_6500 records6498_6500 :=
  aligned6498_6499.append aligned6499_6500

def missing6496_6500 : List (BitVec (edgeCount 12)) :=
  missing6496_6498 ++ missing6498_6500
abbrev records6496_6500 : List Blob :=
  records6496_6498 ++ records6498_6500
theorem aligned6496_6500 :
    AlignedValid 12 3 missing6496_6500 records6496_6500 :=
  aligned6496_6498.append aligned6498_6500

def missing6500_6501 : List (BitVec (edgeCount 12)) :=
  [missing6500]
abbrev records6500_6501 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6500]
theorem aligned6500_6501 :
    AlignedValid 12 3 missing6500_6501 records6500_6501 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6500
    maskCheck6500 AlignedValid.nil

def missing6501_6502 : List (BitVec (edgeCount 12)) :=
  [missing6501]
abbrev records6501_6502 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6501]
theorem aligned6501_6502 :
    AlignedValid 12 3 missing6501_6502 records6501_6502 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6501
    maskCheck6501 AlignedValid.nil

def missing6500_6502 : List (BitVec (edgeCount 12)) :=
  missing6500_6501 ++ missing6501_6502
abbrev records6500_6502 : List Blob :=
  records6500_6501 ++ records6501_6502
theorem aligned6500_6502 :
    AlignedValid 12 3 missing6500_6502 records6500_6502 :=
  aligned6500_6501.append aligned6501_6502

def missing6502_6503 : List (BitVec (edgeCount 12)) :=
  [missing6502]
abbrev records6502_6503 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6502]
theorem aligned6502_6503 :
    AlignedValid 12 3 missing6502_6503 records6502_6503 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6502
    maskCheck6502 AlignedValid.nil

def missing6503_6504 : List (BitVec (edgeCount 12)) :=
  [missing6503]
abbrev records6503_6504 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6503]
theorem aligned6503_6504 :
    AlignedValid 12 3 missing6503_6504 records6503_6504 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6503
    maskCheck6503 AlignedValid.nil

def missing6502_6504 : List (BitVec (edgeCount 12)) :=
  missing6502_6503 ++ missing6503_6504
abbrev records6502_6504 : List Blob :=
  records6502_6503 ++ records6503_6504
theorem aligned6502_6504 :
    AlignedValid 12 3 missing6502_6504 records6502_6504 :=
  aligned6502_6503.append aligned6503_6504

def missing6500_6504 : List (BitVec (edgeCount 12)) :=
  missing6500_6502 ++ missing6502_6504
abbrev records6500_6504 : List Blob :=
  records6500_6502 ++ records6502_6504
theorem aligned6500_6504 :
    AlignedValid 12 3 missing6500_6504 records6500_6504 :=
  aligned6500_6502.append aligned6502_6504

def missing6496_6504 : List (BitVec (edgeCount 12)) :=
  missing6496_6500 ++ missing6500_6504
abbrev records6496_6504 : List Blob :=
  records6496_6500 ++ records6500_6504
theorem aligned6496_6504 :
    AlignedValid 12 3 missing6496_6504 records6496_6504 :=
  aligned6496_6500.append aligned6500_6504

def missing6504_6505 : List (BitVec (edgeCount 12)) :=
  [missing6504]
abbrev records6504_6505 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6504]
theorem aligned6504_6505 :
    AlignedValid 12 3 missing6504_6505 records6504_6505 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6504
    maskCheck6504 AlignedValid.nil

def missing6505_6506 : List (BitVec (edgeCount 12)) :=
  [missing6505]
abbrev records6505_6506 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6505]
theorem aligned6505_6506 :
    AlignedValid 12 3 missing6505_6506 records6505_6506 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6505
    maskCheck6505 AlignedValid.nil

def missing6504_6506 : List (BitVec (edgeCount 12)) :=
  missing6504_6505 ++ missing6505_6506
abbrev records6504_6506 : List Blob :=
  records6504_6505 ++ records6505_6506
theorem aligned6504_6506 :
    AlignedValid 12 3 missing6504_6506 records6504_6506 :=
  aligned6504_6505.append aligned6505_6506

def missing6506_6507 : List (BitVec (edgeCount 12)) :=
  [missing6506]
abbrev records6506_6507 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6506]
theorem aligned6506_6507 :
    AlignedValid 12 3 missing6506_6507 records6506_6507 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6506
    maskCheck6506 AlignedValid.nil

def missing6507_6508 : List (BitVec (edgeCount 12)) :=
  [missing6507]
abbrev records6507_6508 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6507]
theorem aligned6507_6508 :
    AlignedValid 12 3 missing6507_6508 records6507_6508 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6507
    maskCheck6507 AlignedValid.nil

def missing6506_6508 : List (BitVec (edgeCount 12)) :=
  missing6506_6507 ++ missing6507_6508
abbrev records6506_6508 : List Blob :=
  records6506_6507 ++ records6507_6508
theorem aligned6506_6508 :
    AlignedValid 12 3 missing6506_6508 records6506_6508 :=
  aligned6506_6507.append aligned6507_6508

def missing6504_6508 : List (BitVec (edgeCount 12)) :=
  missing6504_6506 ++ missing6506_6508
abbrev records6504_6508 : List Blob :=
  records6504_6506 ++ records6506_6508
theorem aligned6504_6508 :
    AlignedValid 12 3 missing6504_6508 records6504_6508 :=
  aligned6504_6506.append aligned6506_6508

def missing6508_6509 : List (BitVec (edgeCount 12)) :=
  [missing6508]
abbrev records6508_6509 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6508]
theorem aligned6508_6509 :
    AlignedValid 12 3 missing6508_6509 records6508_6509 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6508
    maskCheck6508 AlignedValid.nil

def missing6509_6510 : List (BitVec (edgeCount 12)) :=
  [missing6509]
abbrev records6509_6510 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6509]
theorem aligned6509_6510 :
    AlignedValid 12 3 missing6509_6510 records6509_6510 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6509
    maskCheck6509 AlignedValid.nil

def missing6508_6510 : List (BitVec (edgeCount 12)) :=
  missing6508_6509 ++ missing6509_6510
abbrev records6508_6510 : List Blob :=
  records6508_6509 ++ records6509_6510
theorem aligned6508_6510 :
    AlignedValid 12 3 missing6508_6510 records6508_6510 :=
  aligned6508_6509.append aligned6509_6510

def missing6510_6511 : List (BitVec (edgeCount 12)) :=
  [missing6510]
abbrev records6510_6511 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6510]
theorem aligned6510_6511 :
    AlignedValid 12 3 missing6510_6511 records6510_6511 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6510
    maskCheck6510 AlignedValid.nil

def missing6511_6512 : List (BitVec (edgeCount 12)) :=
  [missing6511]
abbrev records6511_6512 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6511]
theorem aligned6511_6512 :
    AlignedValid 12 3 missing6511_6512 records6511_6512 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6511
    maskCheck6511 AlignedValid.nil

def missing6510_6512 : List (BitVec (edgeCount 12)) :=
  missing6510_6511 ++ missing6511_6512
abbrev records6510_6512 : List Blob :=
  records6510_6511 ++ records6511_6512
theorem aligned6510_6512 :
    AlignedValid 12 3 missing6510_6512 records6510_6512 :=
  aligned6510_6511.append aligned6511_6512

def missing6508_6512 : List (BitVec (edgeCount 12)) :=
  missing6508_6510 ++ missing6510_6512
abbrev records6508_6512 : List Blob :=
  records6508_6510 ++ records6510_6512
theorem aligned6508_6512 :
    AlignedValid 12 3 missing6508_6512 records6508_6512 :=
  aligned6508_6510.append aligned6510_6512

def missing6504_6512 : List (BitVec (edgeCount 12)) :=
  missing6504_6508 ++ missing6508_6512
abbrev records6504_6512 : List Blob :=
  records6504_6508 ++ records6508_6512
theorem aligned6504_6512 :
    AlignedValid 12 3 missing6504_6512 records6504_6512 :=
  aligned6504_6508.append aligned6508_6512

def missing6496_6512 : List (BitVec (edgeCount 12)) :=
  missing6496_6504 ++ missing6504_6512
abbrev records6496_6512 : List Blob :=
  records6496_6504 ++ records6504_6512
theorem aligned6496_6512 :
    AlignedValid 12 3 missing6496_6512 records6496_6512 :=
  aligned6496_6504.append aligned6504_6512

def missing6512_6513 : List (BitVec (edgeCount 12)) :=
  [missing6512]
abbrev records6512_6513 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6512]
theorem aligned6512_6513 :
    AlignedValid 12 3 missing6512_6513 records6512_6513 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6512
    maskCheck6512 AlignedValid.nil

def missing6513_6514 : List (BitVec (edgeCount 12)) :=
  [missing6513]
abbrev records6513_6514 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6513]
theorem aligned6513_6514 :
    AlignedValid 12 3 missing6513_6514 records6513_6514 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6513
    maskCheck6513 AlignedValid.nil

def missing6512_6514 : List (BitVec (edgeCount 12)) :=
  missing6512_6513 ++ missing6513_6514
abbrev records6512_6514 : List Blob :=
  records6512_6513 ++ records6513_6514
theorem aligned6512_6514 :
    AlignedValid 12 3 missing6512_6514 records6512_6514 :=
  aligned6512_6513.append aligned6513_6514

def missing6514_6515 : List (BitVec (edgeCount 12)) :=
  [missing6514]
abbrev records6514_6515 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6514]
theorem aligned6514_6515 :
    AlignedValid 12 3 missing6514_6515 records6514_6515 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6514
    maskCheck6514 AlignedValid.nil

def missing6515_6516 : List (BitVec (edgeCount 12)) :=
  [missing6515]
abbrev records6515_6516 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6515]
theorem aligned6515_6516 :
    AlignedValid 12 3 missing6515_6516 records6515_6516 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6515
    maskCheck6515 AlignedValid.nil

def missing6514_6516 : List (BitVec (edgeCount 12)) :=
  missing6514_6515 ++ missing6515_6516
abbrev records6514_6516 : List Blob :=
  records6514_6515 ++ records6515_6516
theorem aligned6514_6516 :
    AlignedValid 12 3 missing6514_6516 records6514_6516 :=
  aligned6514_6515.append aligned6515_6516

def missing6512_6516 : List (BitVec (edgeCount 12)) :=
  missing6512_6514 ++ missing6514_6516
abbrev records6512_6516 : List Blob :=
  records6512_6514 ++ records6514_6516
theorem aligned6512_6516 :
    AlignedValid 12 3 missing6512_6516 records6512_6516 :=
  aligned6512_6514.append aligned6514_6516

def missing6516_6517 : List (BitVec (edgeCount 12)) :=
  [missing6516]
abbrev records6516_6517 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6516]
theorem aligned6516_6517 :
    AlignedValid 12 3 missing6516_6517 records6516_6517 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6516
    maskCheck6516 AlignedValid.nil

def missing6517_6518 : List (BitVec (edgeCount 12)) :=
  [missing6517]
abbrev records6517_6518 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6517]
theorem aligned6517_6518 :
    AlignedValid 12 3 missing6517_6518 records6517_6518 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6517
    maskCheck6517 AlignedValid.nil

def missing6516_6518 : List (BitVec (edgeCount 12)) :=
  missing6516_6517 ++ missing6517_6518
abbrev records6516_6518 : List Blob :=
  records6516_6517 ++ records6517_6518
theorem aligned6516_6518 :
    AlignedValid 12 3 missing6516_6518 records6516_6518 :=
  aligned6516_6517.append aligned6517_6518

def missing6518_6519 : List (BitVec (edgeCount 12)) :=
  [missing6518]
abbrev records6518_6519 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6518]
theorem aligned6518_6519 :
    AlignedValid 12 3 missing6518_6519 records6518_6519 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6518
    maskCheck6518 AlignedValid.nil

def missing6519_6520 : List (BitVec (edgeCount 12)) :=
  [missing6519]
abbrev records6519_6520 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6519]
theorem aligned6519_6520 :
    AlignedValid 12 3 missing6519_6520 records6519_6520 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6519
    maskCheck6519 AlignedValid.nil

def missing6518_6520 : List (BitVec (edgeCount 12)) :=
  missing6518_6519 ++ missing6519_6520
abbrev records6518_6520 : List Blob :=
  records6518_6519 ++ records6519_6520
theorem aligned6518_6520 :
    AlignedValid 12 3 missing6518_6520 records6518_6520 :=
  aligned6518_6519.append aligned6519_6520

def missing6516_6520 : List (BitVec (edgeCount 12)) :=
  missing6516_6518 ++ missing6518_6520
abbrev records6516_6520 : List Blob :=
  records6516_6518 ++ records6518_6520
theorem aligned6516_6520 :
    AlignedValid 12 3 missing6516_6520 records6516_6520 :=
  aligned6516_6518.append aligned6518_6520

def missing6512_6520 : List (BitVec (edgeCount 12)) :=
  missing6512_6516 ++ missing6516_6520
abbrev records6512_6520 : List Blob :=
  records6512_6516 ++ records6516_6520
theorem aligned6512_6520 :
    AlignedValid 12 3 missing6512_6520 records6512_6520 :=
  aligned6512_6516.append aligned6516_6520

def missing6520_6521 : List (BitVec (edgeCount 12)) :=
  [missing6520]
abbrev records6520_6521 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6520]
theorem aligned6520_6521 :
    AlignedValid 12 3 missing6520_6521 records6520_6521 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6520
    maskCheck6520 AlignedValid.nil

def missing6521_6522 : List (BitVec (edgeCount 12)) :=
  [missing6521]
abbrev records6521_6522 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6521]
theorem aligned6521_6522 :
    AlignedValid 12 3 missing6521_6522 records6521_6522 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6521
    maskCheck6521 AlignedValid.nil

def missing6520_6522 : List (BitVec (edgeCount 12)) :=
  missing6520_6521 ++ missing6521_6522
abbrev records6520_6522 : List Blob :=
  records6520_6521 ++ records6521_6522
theorem aligned6520_6522 :
    AlignedValid 12 3 missing6520_6522 records6520_6522 :=
  aligned6520_6521.append aligned6521_6522

def missing6522_6523 : List (BitVec (edgeCount 12)) :=
  [missing6522]
abbrev records6522_6523 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6522]
theorem aligned6522_6523 :
    AlignedValid 12 3 missing6522_6523 records6522_6523 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6522
    maskCheck6522 AlignedValid.nil

def missing6523_6524 : List (BitVec (edgeCount 12)) :=
  [missing6523]
abbrev records6523_6524 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6523]
theorem aligned6523_6524 :
    AlignedValid 12 3 missing6523_6524 records6523_6524 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6523
    maskCheck6523 AlignedValid.nil

def missing6522_6524 : List (BitVec (edgeCount 12)) :=
  missing6522_6523 ++ missing6523_6524
abbrev records6522_6524 : List Blob :=
  records6522_6523 ++ records6523_6524
theorem aligned6522_6524 :
    AlignedValid 12 3 missing6522_6524 records6522_6524 :=
  aligned6522_6523.append aligned6523_6524

def missing6520_6524 : List (BitVec (edgeCount 12)) :=
  missing6520_6522 ++ missing6522_6524
abbrev records6520_6524 : List Blob :=
  records6520_6522 ++ records6522_6524
theorem aligned6520_6524 :
    AlignedValid 12 3 missing6520_6524 records6520_6524 :=
  aligned6520_6522.append aligned6522_6524

def missing6524_6525 : List (BitVec (edgeCount 12)) :=
  [missing6524]
abbrev records6524_6525 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6524]
theorem aligned6524_6525 :
    AlignedValid 12 3 missing6524_6525 records6524_6525 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6524
    maskCheck6524 AlignedValid.nil

def missing6525_6526 : List (BitVec (edgeCount 12)) :=
  [missing6525]
abbrev records6525_6526 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6525]
theorem aligned6525_6526 :
    AlignedValid 12 3 missing6525_6526 records6525_6526 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6525
    maskCheck6525 AlignedValid.nil

def missing6524_6526 : List (BitVec (edgeCount 12)) :=
  missing6524_6525 ++ missing6525_6526
abbrev records6524_6526 : List Blob :=
  records6524_6525 ++ records6525_6526
theorem aligned6524_6526 :
    AlignedValid 12 3 missing6524_6526 records6524_6526 :=
  aligned6524_6525.append aligned6525_6526

def missing6526_6527 : List (BitVec (edgeCount 12)) :=
  [missing6526]
abbrev records6526_6527 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6526]
theorem aligned6526_6527 :
    AlignedValid 12 3 missing6526_6527 records6526_6527 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6526
    maskCheck6526 AlignedValid.nil

def missing6527_6528 : List (BitVec (edgeCount 12)) :=
  [missing6527]
abbrev records6527_6528 : List Blob :=
  [StrongPackedBucketN12A3Shard050.record6527]
theorem aligned6527_6528 :
    AlignedValid 12 3 missing6527_6528 records6527_6528 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard050.check6527
    maskCheck6527 AlignedValid.nil

def missing6526_6528 : List (BitVec (edgeCount 12)) :=
  missing6526_6527 ++ missing6527_6528
abbrev records6526_6528 : List Blob :=
  records6526_6527 ++ records6527_6528
theorem aligned6526_6528 :
    AlignedValid 12 3 missing6526_6528 records6526_6528 :=
  aligned6526_6527.append aligned6527_6528

def missing6524_6528 : List (BitVec (edgeCount 12)) :=
  missing6524_6526 ++ missing6526_6528
abbrev records6524_6528 : List Blob :=
  records6524_6526 ++ records6526_6528
theorem aligned6524_6528 :
    AlignedValid 12 3 missing6524_6528 records6524_6528 :=
  aligned6524_6526.append aligned6526_6528

def missing6520_6528 : List (BitVec (edgeCount 12)) :=
  missing6520_6524 ++ missing6524_6528
abbrev records6520_6528 : List Blob :=
  records6520_6524 ++ records6524_6528
theorem aligned6520_6528 :
    AlignedValid 12 3 missing6520_6528 records6520_6528 :=
  aligned6520_6524.append aligned6524_6528

def missing6512_6528 : List (BitVec (edgeCount 12)) :=
  missing6512_6520 ++ missing6520_6528
abbrev records6512_6528 : List Blob :=
  records6512_6520 ++ records6520_6528
theorem aligned6512_6528 :
    AlignedValid 12 3 missing6512_6528 records6512_6528 :=
  aligned6512_6520.append aligned6520_6528

def missing6496_6528 : List (BitVec (edgeCount 12)) :=
  missing6496_6512 ++ missing6512_6528
abbrev records6496_6528 : List Blob :=
  records6496_6512 ++ records6512_6528
theorem aligned6496_6528 :
    AlignedValid 12 3 missing6496_6528 records6496_6528 :=
  aligned6496_6512.append aligned6512_6528

def missing6464_6528 : List (BitVec (edgeCount 12)) :=
  missing6464_6496 ++ missing6496_6528
abbrev records6464_6528 : List Blob :=
  records6464_6496 ++ records6496_6528
theorem aligned6464_6528 :
    AlignedValid 12 3 missing6464_6528 records6464_6528 :=
  aligned6464_6496.append aligned6496_6528

def missing6400_6528 : List (BitVec (edgeCount 12)) :=
  missing6400_6464 ++ missing6464_6528
abbrev records6400_6528 : List Blob :=
  records6400_6464 ++ records6464_6528
theorem aligned6400_6528 :
    AlignedValid 12 3 missing6400_6528 records6400_6528 :=
  aligned6400_6464.append aligned6464_6528

abbrev missing : List (BitVec (edgeCount 12)) := missing6400_6528
abbrev records : List Blob := records6400_6528
theorem aligned : AlignedValid 12 3 missing records := aligned6400_6528

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard050
