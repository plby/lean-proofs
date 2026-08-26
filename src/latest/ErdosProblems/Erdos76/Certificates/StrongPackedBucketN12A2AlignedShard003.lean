/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard003

/-! Decode-only alignment checks for n=12, a=2, records 384--511. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A2AlignedShard003

open PackedBucketCertificate

def missing384 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4233806068351762432
theorem maskCheck384 :
    checkMaskFor missing384 StrongPackedBucketN12A2Shard003.record384 = true := by
  decide

def missing385 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8701376898703294464
theorem maskCheck385 :
    checkMaskFor missing385 StrongPackedBucketN12A2Shard003.record385 = true := by
  decide

def missing386 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17888720138539106304
theorem maskCheck386 :
    checkMaskFor missing386 StrongPackedBucketN12A2Shard003.record386 = true := by
  decide

def missing387 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19005612846126989312
theorem maskCheck387 :
    checkMaskFor missing387 StrongPackedBucketN12A2Shard003.record387 = true := by
  decide

def missing388 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19293843222278701056
theorem maskCheck388 :
    checkMaskFor missing388 StrongPackedBucketN12A2Shard003.record388 = true := by
  decide

def missing389 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19510016004392484864
theorem maskCheck389 :
    checkMaskFor missing389 StrongPackedBucketN12A2Shard003.record389 = true := by
  decide

def missing390 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20302649538809692160
theorem maskCheck390 :
    checkMaskFor missing390 StrongPackedBucketN12A2Shard003.record390 = true := by
  decide

def missing391 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20374707132847620096
theorem maskCheck391 :
    checkMaskFor missing391 StrongPackedBucketN12A2Shard003.record391 = true := by
  decide

def missing392 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20626908711980367872
theorem maskCheck392 :
    checkMaskFor missing392 StrongPackedBucketN12A2Shard003.record392 = true := by
  decide

def missing393 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22536434953985458176
theorem maskCheck393 :
    checkMaskFor missing393 StrongPackedBucketN12A2Shard003.record393 = true := by
  decide

def missing394 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22644521345042350080
theorem maskCheck394 :
    checkMaskFor missing394 StrongPackedBucketN12A2Shard003.record394 = true := by
  decide

def missing395 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27112092175393882112
theorem maskCheck395 :
    checkMaskFor missing395 StrongPackedBucketN12A2Shard003.record395 = true := by
  decide

def missing396 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55610870617394380800
theorem maskCheck396 :
    checkMaskFor missing396 StrongPackedBucketN12A2Shard003.record396 = true := by
  decide

def missing397 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56043216181621948416
theorem maskCheck397 :
    checkMaskFor missing397 StrongPackedBucketN12A2Shard003.record397 = true := by
  decide

def missing398 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56115273775659876352
theorem maskCheck398 :
    checkMaskFor missing398 StrongPackedBucketN12A2Shard003.record398 = true := by
  decide

def missing399 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57124080092190867456
theorem maskCheck399 :
    checkMaskFor missing399 StrongPackedBucketN12A2Shard003.record399 = true := by
  decide

def missing400 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59393894304385597440
theorem maskCheck400 :
    checkMaskFor missing400 StrongPackedBucketN12A2Shard003.record400 = true := by
  decide

def missing401 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 540959927024222208
theorem maskCheck401 :
    checkMaskFor missing401 StrongPackedBucketN12A2Shard003.record401 = true := by
  decide

def missing402 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 829190303175933952
theorem maskCheck402 :
    checkMaskFor missing402 StrongPackedBucketN12A2Shard003.record402 = true := by
  decide

def missing403 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1837996619706925056
theorem maskCheck403 :
    checkMaskFor missing403 StrongPackedBucketN12A2Shard003.record403 = true := by
  decide

def missing404 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 541452508233465856
theorem maskCheck404 :
    checkMaskFor missing404 StrongPackedBucketN12A2Shard003.record404 = true := by
  decide

def missing405 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1045855666498961408
theorem maskCheck405 :
    checkMaskFor missing405 StrongPackedBucketN12A2Shard003.record405 = true := by
  decide

def missing406 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081884463517925376
theorem maskCheck406 :
    checkMaskFor missing406 StrongPackedBucketN12A2Shard003.record406 = true := by
  decide

def missing407 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1406143636688601088
theorem maskCheck407 :
    checkMaskFor missing407 StrongPackedBucketN12A2Shard003.record407 = true := by
  decide

def missing408 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1622316418802384896
theorem maskCheck408 :
    checkMaskFor missing408 StrongPackedBucketN12A2Shard003.record408 = true := by
  decide

def missing409 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1658345215821348864
theorem maskCheck409 :
    checkMaskFor missing409 StrongPackedBucketN12A2Shard003.record409 = true := by
  decide

def missing410 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3567871457826439168
theorem maskCheck410 :
    checkMaskFor missing410 StrongPackedBucketN12A2Shard003.record410 = true := by
  decide

def missing411 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3639929051864367104
theorem maskCheck411 :
    checkMaskFor missing411 StrongPackedBucketN12A2Shard003.record411 = true := by
  decide

def missing412 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3675957848883331072
theorem maskCheck412 :
    checkMaskFor missing412 StrongPackedBucketN12A2Shard003.record412 = true := by
  decide

def missing413 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8107499882215899136
theorem maskCheck413 :
    checkMaskFor missing413 StrongPackedBucketN12A2Shard003.record413 = true := by
  decide

def missing414 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8143528679234863104
theorem maskCheck414 :
    checkMaskFor missing414 StrongPackedBucketN12A2Shard003.record414 = true := by
  decide

def missing415 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699966205791305728
theorem maskCheck415 :
    checkMaskFor missing415 StrongPackedBucketN12A2Shard003.record415 = true := by
  decide

def missing416 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19708772522322296832
theorem maskCheck416 :
    checkMaskFor missing416 StrongPackedBucketN12A2Shard003.record416 = true := by
  decide

def missing417 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 542543223768219648
theorem maskCheck417 :
    checkMaskFor missing417 StrongPackedBucketN12A2Shard003.record417 = true := by
  decide

def missing418 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1046946382033715200
theorem maskCheck418 :
    checkMaskFor missing418 StrongPackedBucketN12A2Shard003.record418 = true := by
  decide

def missing419 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2163839089621598208
theorem maskCheck419 :
    checkMaskFor missing419 StrongPackedBucketN12A2Shard003.record419 = true := by
  decide

def missing420 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2560155856830201856
theorem maskCheck420 :
    checkMaskFor missing420 StrongPackedBucketN12A2Shard003.record420 = true := by
  decide

def missing421 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2776328638943985664
theorem maskCheck421 :
    checkMaskFor missing421 StrongPackedBucketN12A2Shard003.record421 = true := by
  decide

def missing422 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3316760594228445184
theorem maskCheck422 :
    checkMaskFor missing422 StrongPackedBucketN12A2Shard003.record422 = true := by
  decide

def missing423 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7027726687181733888
theorem maskCheck423 :
    checkMaskFor missing423 StrongPackedBucketN12A2Shard003.record423 = true := by
  decide

def missing424 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7099784281219661824
theorem maskCheck424 :
    checkMaskFor missing424 StrongPackedBucketN12A2Shard003.record424 = true := by
  decide

def missing425 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7351985860352409600
theorem maskCheck425 :
    checkMaskFor missing425 StrongPackedBucketN12A2Shard003.record425 = true := by
  decide

def missing426 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16179041129998581760
theorem maskCheck426 :
    checkMaskFor missing426 StrongPackedBucketN12A2Shard003.record426 = true := by
  decide

def missing427 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16287127521055473664
theorem maskCheck427 :
    checkMaskFor missing427 StrongPackedBucketN12A2Shard003.record427 = true := by
  decide

def missing428 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18701056921326059520
theorem maskCheck428 :
    checkMaskFor missing428 StrongPackedBucketN12A2Shard003.record428 = true := by
  decide

def missing429 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18917229703439843328
theorem maskCheck429 :
    checkMaskFor missing429 StrongPackedBucketN12A2Shard003.record429 = true := by
  decide

def missing430 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20862784742463897600
theorem maskCheck430 :
    checkMaskFor missing430 StrongPackedBucketN12A2Shard003.record430 = true := by
  decide

def missing431 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20934842336501825536
theorem maskCheck431 :
    checkMaskFor missing431 StrongPackedBucketN12A2Shard003.record431 = true := by
  decide

def missing432 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25402413166853357568
theorem maskCheck432 :
    checkMaskFor missing432 StrongPackedBucketN12A2Shard003.record432 = true := by
  decide

def missing433 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 558692850556993536
theorem maskCheck433 :
    checkMaskFor missing433 StrongPackedBucketN12A2Shard003.record433 = true := by
  decide

def missing434 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 991038414784561152
theorem maskCheck434 :
    checkMaskFor missing434 StrongPackedBucketN12A2Shard003.record434 = true := by
  decide

def missing435 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 558903956789526528
theorem maskCheck435 :
    checkMaskFor missing435 StrongPackedBucketN12A2Shard003.record435 = true := by
  decide

def missing436 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 847134332941238272
theorem maskCheck436 :
    checkMaskFor missing436 StrongPackedBucketN12A2Shard003.record436 = true := by
  decide

def missing437 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1063307115055022080
theorem maskCheck437 :
    checkMaskFor missing437 StrongPackedBucketN12A2Shard003.record437 = true := by
  decide

def missing438 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1099335912073986048
theorem maskCheck438 :
    checkMaskFor missing438 StrongPackedBucketN12A2Shard003.record438 = true := by
  decide

def missing439 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1855940649472229376
theorem maskCheck439 :
    checkMaskFor missing439 StrongPackedBucketN12A2Shard003.record439 = true := by
  decide

def missing440 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1927998243510157312
theorem maskCheck440 :
    checkMaskFor missing440 StrongPackedBucketN12A2Shard003.record440 = true := by
  decide

def missing441 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1964027040529121280
theorem maskCheck441 :
    checkMaskFor missing441 StrongPackedBucketN12A2Shard003.record441 = true := by
  decide

def missing442 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4089726064647995392
theorem maskCheck442 :
    checkMaskFor missing442 StrongPackedBucketN12A2Shard003.record442 = true := by
  decide

def missing443 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4125754861666959360
theorem maskCheck443 :
    checkMaskFor missing443 StrongPackedBucketN12A2Shard003.record443 = true := by
  decide

def missing444 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 559431722370859008
theorem maskCheck444 :
    checkMaskFor missing444 StrongPackedBucketN12A2Shard003.record444 = true := by
  decide

def missing445 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1063834880636354560
theorem maskCheck445 :
    checkMaskFor missing445 StrongPackedBucketN12A2Shard003.record445 = true := by
  decide

def missing446 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1424122850825994240
theorem maskCheck446 :
    checkMaskFor missing446 StrongPackedBucketN12A2Shard003.record446 = true := by
  decide

def missing447 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1640295632939778048
theorem maskCheck447 :
    checkMaskFor missing447 StrongPackedBucketN12A2Shard003.record447 = true := by
  decide

def missing448 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2180727588224237568
theorem maskCheck448 :
    checkMaskFor missing448 StrongPackedBucketN12A2Shard003.record448 = true := by
  decide

def missing449 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3585850671963832320
theorem maskCheck449 :
    checkMaskFor missing449 StrongPackedBucketN12A2Shard003.record449 = true := by
  decide

def missing450 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3657908266001760256
theorem maskCheck450 :
    checkMaskFor missing450 StrongPackedBucketN12A2Shard003.record450 = true := by
  decide

def missing451 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3910109845134508032
theorem maskCheck451 :
    checkMaskFor missing451 StrongPackedBucketN12A2Shard003.record451 = true := by
  decide

def missing452 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8125479096353292288
theorem maskCheck452 :
    checkMaskFor missing452 StrongPackedBucketN12A2Shard003.record452 = true := by
  decide

def missing453 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8233565487410184192
theorem maskCheck453 :
    checkMaskFor missing453 StrongPackedBucketN12A2Shard003.record453 = true := by
  decide

def missing454 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17312822336189104128
theorem maskCheck454 :
    checkMaskFor missing454 StrongPackedBucketN12A2Shard003.record454 = true := by
  decide

def missing455 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 540678726925418496
theorem maskCheck455 :
    checkMaskFor missing455 StrongPackedBucketN12A2Shard003.record455 = true := by
  decide

def missing456 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 973024291152986112
theorem maskCheck456 :
    checkMaskFor missing456 StrongPackedBucketN12A2Shard003.record456 = true := by
  decide

def missing457 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2053888201721905152
theorem maskCheck457 :
    checkMaskFor missing457 StrongPackedBucketN12A2Shard003.record457 = true := by
  decide

def missing458 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4323702413916635136
theorem maskCheck458 :
    checkMaskFor missing458 StrongPackedBucketN12A2Shard003.record458 = true := by
  decide

def missing459 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699192424483258368
theorem maskCheck459 :
    checkMaskFor missing459 StrongPackedBucketN12A2Shard003.record459 = true := by
  decide

def missing460 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55448565383826505728
theorem maskCheck460 :
    checkMaskFor missing460 StrongPackedBucketN12A2Shard003.record460 = true := by
  decide

def missing461 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55664738165940289536
theorem maskCheck461 :
    checkMaskFor missing461 StrongPackedBucketN12A2Shard003.record461 = true := by
  decide

def missing462 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56205170121224749056
theorem maskCheck462 :
    checkMaskFor missing462 StrongPackedBucketN12A2Shard003.record462 = true := by
  decide

def missing463 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 540819464413773824
theorem maskCheck463 :
    checkMaskFor missing463 StrongPackedBucketN12A2Shard003.record463 = true := by
  decide

def missing464 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 829049840565485568
theorem maskCheck464 :
    checkMaskFor missing464 StrongPackedBucketN12A2Shard003.record464 = true := by
  decide

def missing465 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1045222622679269376
theorem maskCheck465 :
    checkMaskFor missing465 StrongPackedBucketN12A2Shard003.record465 = true := by
  decide

def missing466 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1837856157096476672
theorem maskCheck466 :
    checkMaskFor missing466 StrongPackedBucketN12A2Shard003.record466 = true := by
  decide

def missing467 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1909913751134404608
theorem maskCheck467 :
    checkMaskFor missing467 StrongPackedBucketN12A2Shard003.record467 = true := by
  decide

def missing468 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2162115330267152384
theorem maskCheck468 :
    checkMaskFor missing468 StrongPackedBucketN12A2Shard003.record468 = true := by
  decide

def missing469 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4071641572272242688
theorem maskCheck469 :
    checkMaskFor missing469 StrongPackedBucketN12A2Shard003.record469 = true := by
  decide

def missing470 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4179727963329134592
theorem maskCheck470 :
    checkMaskFor missing470 StrongPackedBucketN12A2Shard003.record470 = true := by
  decide

def missing471 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8647298793680666624
theorem maskCheck471 :
    checkMaskFor missing471 StrongPackedBucketN12A2Shard003.record471 = true := by
  decide

def missing472 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699333161971613696
theorem maskCheck472 :
    checkMaskFor missing472 StrongPackedBucketN12A2Shard003.record472 = true := by
  decide

def missing473 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18843448350047469568
theorem maskCheck473 :
    checkMaskFor missing473 StrongPackedBucketN12A2Shard003.record473 = true := by
  decide

def missing474 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18915505944085397504
theorem maskCheck474 :
    checkMaskFor missing474 StrongPackedBucketN12A2Shard003.record474 = true := by
  decide

def missing475 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19131678726199181312
theorem maskCheck475 :
    checkMaskFor missing475 StrongPackedBucketN12A2Shard003.record475 = true := by
  decide

def missing476 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19347851508312965120
theorem maskCheck476 :
    checkMaskFor missing476 StrongPackedBucketN12A2Shard003.record476 = true := by
  decide

def missing477 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55448706121314861056
theorem maskCheck477 :
    checkMaskFor missing477 StrongPackedBucketN12A2Shard003.record477 = true := by
  decide

def missing478 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55520763715352788992
theorem maskCheck478 :
    checkMaskFor missing478 StrongPackedBucketN12A2Shard003.record478 = true := by
  decide

def missing479 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55772965294485536768
theorem maskCheck479 :
    checkMaskFor missing479 StrongPackedBucketN12A2Shard003.record479 = true := by
  decide

def missing480 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55953109279580356608
theorem maskCheck480 :
    checkMaskFor missing480 StrongPackedBucketN12A2Shard003.record480 = true := by
  decide

def missing481 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56061195670637248512
theorem maskCheck481 :
    checkMaskFor missing481 StrongPackedBucketN12A2Shard003.record481 = true := by
  decide

def missing482 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57070001987168239616
theorem maskCheck482 :
    checkMaskFor missing482 StrongPackedBucketN12A2Shard003.record482 = true := by
  decide

def missing483 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 541312045623017472
theorem maskCheck483 :
    checkMaskFor missing483 StrongPackedBucketN12A2Shard003.record483 = true := by
  decide

def missing484 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081744000907476992
theorem maskCheck484 :
    checkMaskFor missing484 StrongPackedBucketN12A2Shard003.record484 = true := by
  decide

def missing485 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1406003174078152704
theorem maskCheck485 :
    checkMaskFor missing485 StrongPackedBucketN12A2Shard003.record485 = true := by
  decide

def missing486 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1550118362154008576
theorem maskCheck486 :
    checkMaskFor missing486 StrongPackedBucketN12A2Shard003.record486 = true := by
  decide

def missing487 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1658204753210900480
theorem maskCheck487 :
    checkMaskFor missing487 StrongPackedBucketN12A2Shard003.record487 = true := by
  decide

def missing488 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3567730995215990784
theorem maskCheck488 :
    checkMaskFor missing488 StrongPackedBucketN12A2Shard003.record488 = true := by
  decide

def missing489 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3675817386272882688
theorem maskCheck489 :
    checkMaskFor missing489 StrongPackedBucketN12A2Shard003.record489 = true := by
  decide

def missing490 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3819932574348738560
theorem maskCheck490 :
    checkMaskFor missing490 StrongPackedBucketN12A2Shard003.record490 = true := by
  decide

def missing491 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8107359419605450752
theorem maskCheck491 :
    checkMaskFor missing491 StrongPackedBucketN12A2Shard003.record491 = true := by
  decide

def missing492 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8143388216624414720
theorem maskCheck492 :
    checkMaskFor missing492 StrongPackedBucketN12A2Shard003.record492 = true := by
  decide

def missing493 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17294702659441262592
theorem maskCheck493 :
    checkMaskFor missing493 StrongPackedBucketN12A2Shard003.record493 = true := by
  decide

def missing494 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699825743180857344
theorem maskCheck494 :
    checkMaskFor missing494 StrongPackedBucketN12A2Shard003.record494 = true := by
  decide

def missing495 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18843940931256713216
theorem maskCheck495 :
    checkMaskFor missing495 StrongPackedBucketN12A2Shard003.record495 = true := by
  decide

def missing496 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18952027322313605120
theorem maskCheck496 :
    checkMaskFor missing496 StrongPackedBucketN12A2Shard003.record496 = true := by
  decide

def missing497 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19348344089522208768
theorem maskCheck497 :
    checkMaskFor missing497 StrongPackedBucketN12A2Shard003.record497 = true := by
  decide

def missing498 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19384372886541172736
theorem maskCheck498 :
    checkMaskFor missing498 StrongPackedBucketN12A2Shard003.record498 = true := by
  decide

def missing499 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19708632059711848448
theorem maskCheck499 :
    checkMaskFor missing499 StrongPackedBucketN12A2Shard003.record499 = true := by
  decide

def missing500 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19924804841825632256
theorem maskCheck500 :
    checkMaskFor missing500 StrongPackedBucketN12A2Shard003.record500 = true := by
  decide

def missing501 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19960833638844596224
theorem maskCheck501 :
    checkMaskFor missing501 StrongPackedBucketN12A2Shard003.record501 = true := by
  decide

def missing502 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20465236797110091776
theorem maskCheck502 :
    checkMaskFor missing502 StrongPackedBucketN12A2Shard003.record502 = true := by
  decide

def missing503 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21942417474887614464
theorem maskCheck503 :
    checkMaskFor missing503 StrongPackedBucketN12A2Shard003.record503 = true := by
  decide

def missing504 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22194619054020362240
theorem maskCheck504 :
    checkMaskFor missing504 StrongPackedBucketN12A2Shard003.record504 = true := by
  decide

def missing505 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55449198702524104704
theorem maskCheck505 :
    checkMaskFor missing505 StrongPackedBucketN12A2Shard003.record505 = true := by
  decide

def missing506 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55557285093580996608
theorem maskCheck506 :
    checkMaskFor missing506 StrongPackedBucketN12A2Shard003.record506 = true := by
  decide

def missing507 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55701400281656852480
theorem maskCheck507 :
    checkMaskFor missing507 StrongPackedBucketN12A2Shard003.record507 = true := by
  decide

def missing508 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56530062613093023744
theorem maskCheck508 :
    checkMaskFor missing508 StrongPackedBucketN12A2Shard003.record508 = true := by
  decide

def missing509 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56566091410111987712
theorem maskCheck509 :
    checkMaskFor missing509 StrongPackedBucketN12A2Shard003.record509 = true := by
  decide

def missing510 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58799876825287753728
theorem maskCheck510 :
    checkMaskFor missing510 StrongPackedBucketN12A2Shard003.record510 = true := by
  decide

def missing511 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 542402761157771264
theorem maskCheck511 :
    checkMaskFor missing511 StrongPackedBucketN12A2Shard003.record511 = true := by
  decide

def missing384_385 : List (BitVec (edgeCount 12)) :=
  [missing384]
abbrev records384_385 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record384]
theorem aligned384_385 :
    AlignedValid 12 2 missing384_385 records384_385 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check384
    maskCheck384 AlignedValid.nil

def missing385_386 : List (BitVec (edgeCount 12)) :=
  [missing385]
abbrev records385_386 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record385]
theorem aligned385_386 :
    AlignedValid 12 2 missing385_386 records385_386 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check385
    maskCheck385 AlignedValid.nil

def missing384_386 : List (BitVec (edgeCount 12)) :=
  missing384_385 ++ missing385_386
abbrev records384_386 : List Blob :=
  records384_385 ++ records385_386
theorem aligned384_386 :
    AlignedValid 12 2 missing384_386 records384_386 :=
  aligned384_385.append aligned385_386

def missing386_387 : List (BitVec (edgeCount 12)) :=
  [missing386]
abbrev records386_387 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record386]
theorem aligned386_387 :
    AlignedValid 12 2 missing386_387 records386_387 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check386
    maskCheck386 AlignedValid.nil

def missing387_388 : List (BitVec (edgeCount 12)) :=
  [missing387]
abbrev records387_388 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record387]
theorem aligned387_388 :
    AlignedValid 12 2 missing387_388 records387_388 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check387
    maskCheck387 AlignedValid.nil

def missing386_388 : List (BitVec (edgeCount 12)) :=
  missing386_387 ++ missing387_388
abbrev records386_388 : List Blob :=
  records386_387 ++ records387_388
theorem aligned386_388 :
    AlignedValid 12 2 missing386_388 records386_388 :=
  aligned386_387.append aligned387_388

def missing384_388 : List (BitVec (edgeCount 12)) :=
  missing384_386 ++ missing386_388
abbrev records384_388 : List Blob :=
  records384_386 ++ records386_388
theorem aligned384_388 :
    AlignedValid 12 2 missing384_388 records384_388 :=
  aligned384_386.append aligned386_388

def missing388_389 : List (BitVec (edgeCount 12)) :=
  [missing388]
abbrev records388_389 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record388]
theorem aligned388_389 :
    AlignedValid 12 2 missing388_389 records388_389 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check388
    maskCheck388 AlignedValid.nil

def missing389_390 : List (BitVec (edgeCount 12)) :=
  [missing389]
abbrev records389_390 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record389]
theorem aligned389_390 :
    AlignedValid 12 2 missing389_390 records389_390 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check389
    maskCheck389 AlignedValid.nil

def missing388_390 : List (BitVec (edgeCount 12)) :=
  missing388_389 ++ missing389_390
abbrev records388_390 : List Blob :=
  records388_389 ++ records389_390
theorem aligned388_390 :
    AlignedValid 12 2 missing388_390 records388_390 :=
  aligned388_389.append aligned389_390

def missing390_391 : List (BitVec (edgeCount 12)) :=
  [missing390]
abbrev records390_391 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record390]
theorem aligned390_391 :
    AlignedValid 12 2 missing390_391 records390_391 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check390
    maskCheck390 AlignedValid.nil

def missing391_392 : List (BitVec (edgeCount 12)) :=
  [missing391]
abbrev records391_392 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record391]
theorem aligned391_392 :
    AlignedValid 12 2 missing391_392 records391_392 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check391
    maskCheck391 AlignedValid.nil

def missing390_392 : List (BitVec (edgeCount 12)) :=
  missing390_391 ++ missing391_392
abbrev records390_392 : List Blob :=
  records390_391 ++ records391_392
theorem aligned390_392 :
    AlignedValid 12 2 missing390_392 records390_392 :=
  aligned390_391.append aligned391_392

def missing388_392 : List (BitVec (edgeCount 12)) :=
  missing388_390 ++ missing390_392
abbrev records388_392 : List Blob :=
  records388_390 ++ records390_392
theorem aligned388_392 :
    AlignedValid 12 2 missing388_392 records388_392 :=
  aligned388_390.append aligned390_392

def missing384_392 : List (BitVec (edgeCount 12)) :=
  missing384_388 ++ missing388_392
abbrev records384_392 : List Blob :=
  records384_388 ++ records388_392
theorem aligned384_392 :
    AlignedValid 12 2 missing384_392 records384_392 :=
  aligned384_388.append aligned388_392

def missing392_393 : List (BitVec (edgeCount 12)) :=
  [missing392]
abbrev records392_393 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record392]
theorem aligned392_393 :
    AlignedValid 12 2 missing392_393 records392_393 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check392
    maskCheck392 AlignedValid.nil

def missing393_394 : List (BitVec (edgeCount 12)) :=
  [missing393]
abbrev records393_394 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record393]
theorem aligned393_394 :
    AlignedValid 12 2 missing393_394 records393_394 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check393
    maskCheck393 AlignedValid.nil

def missing392_394 : List (BitVec (edgeCount 12)) :=
  missing392_393 ++ missing393_394
abbrev records392_394 : List Blob :=
  records392_393 ++ records393_394
theorem aligned392_394 :
    AlignedValid 12 2 missing392_394 records392_394 :=
  aligned392_393.append aligned393_394

def missing394_395 : List (BitVec (edgeCount 12)) :=
  [missing394]
abbrev records394_395 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record394]
theorem aligned394_395 :
    AlignedValid 12 2 missing394_395 records394_395 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check394
    maskCheck394 AlignedValid.nil

def missing395_396 : List (BitVec (edgeCount 12)) :=
  [missing395]
abbrev records395_396 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record395]
theorem aligned395_396 :
    AlignedValid 12 2 missing395_396 records395_396 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check395
    maskCheck395 AlignedValid.nil

def missing394_396 : List (BitVec (edgeCount 12)) :=
  missing394_395 ++ missing395_396
abbrev records394_396 : List Blob :=
  records394_395 ++ records395_396
theorem aligned394_396 :
    AlignedValid 12 2 missing394_396 records394_396 :=
  aligned394_395.append aligned395_396

def missing392_396 : List (BitVec (edgeCount 12)) :=
  missing392_394 ++ missing394_396
abbrev records392_396 : List Blob :=
  records392_394 ++ records394_396
theorem aligned392_396 :
    AlignedValid 12 2 missing392_396 records392_396 :=
  aligned392_394.append aligned394_396

def missing396_397 : List (BitVec (edgeCount 12)) :=
  [missing396]
abbrev records396_397 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record396]
theorem aligned396_397 :
    AlignedValid 12 2 missing396_397 records396_397 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check396
    maskCheck396 AlignedValid.nil

def missing397_398 : List (BitVec (edgeCount 12)) :=
  [missing397]
abbrev records397_398 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record397]
theorem aligned397_398 :
    AlignedValid 12 2 missing397_398 records397_398 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check397
    maskCheck397 AlignedValid.nil

def missing396_398 : List (BitVec (edgeCount 12)) :=
  missing396_397 ++ missing397_398
abbrev records396_398 : List Blob :=
  records396_397 ++ records397_398
theorem aligned396_398 :
    AlignedValid 12 2 missing396_398 records396_398 :=
  aligned396_397.append aligned397_398

def missing398_399 : List (BitVec (edgeCount 12)) :=
  [missing398]
abbrev records398_399 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record398]
theorem aligned398_399 :
    AlignedValid 12 2 missing398_399 records398_399 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check398
    maskCheck398 AlignedValid.nil

def missing399_400 : List (BitVec (edgeCount 12)) :=
  [missing399]
abbrev records399_400 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record399]
theorem aligned399_400 :
    AlignedValid 12 2 missing399_400 records399_400 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check399
    maskCheck399 AlignedValid.nil

def missing398_400 : List (BitVec (edgeCount 12)) :=
  missing398_399 ++ missing399_400
abbrev records398_400 : List Blob :=
  records398_399 ++ records399_400
theorem aligned398_400 :
    AlignedValid 12 2 missing398_400 records398_400 :=
  aligned398_399.append aligned399_400

def missing396_400 : List (BitVec (edgeCount 12)) :=
  missing396_398 ++ missing398_400
abbrev records396_400 : List Blob :=
  records396_398 ++ records398_400
theorem aligned396_400 :
    AlignedValid 12 2 missing396_400 records396_400 :=
  aligned396_398.append aligned398_400

def missing392_400 : List (BitVec (edgeCount 12)) :=
  missing392_396 ++ missing396_400
abbrev records392_400 : List Blob :=
  records392_396 ++ records396_400
theorem aligned392_400 :
    AlignedValid 12 2 missing392_400 records392_400 :=
  aligned392_396.append aligned396_400

def missing384_400 : List (BitVec (edgeCount 12)) :=
  missing384_392 ++ missing392_400
abbrev records384_400 : List Blob :=
  records384_392 ++ records392_400
theorem aligned384_400 :
    AlignedValid 12 2 missing384_400 records384_400 :=
  aligned384_392.append aligned392_400

def missing400_401 : List (BitVec (edgeCount 12)) :=
  [missing400]
abbrev records400_401 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record400]
theorem aligned400_401 :
    AlignedValid 12 2 missing400_401 records400_401 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check400
    maskCheck400 AlignedValid.nil

def missing401_402 : List (BitVec (edgeCount 12)) :=
  [missing401]
abbrev records401_402 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record401]
theorem aligned401_402 :
    AlignedValid 12 2 missing401_402 records401_402 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check401
    maskCheck401 AlignedValid.nil

def missing400_402 : List (BitVec (edgeCount 12)) :=
  missing400_401 ++ missing401_402
abbrev records400_402 : List Blob :=
  records400_401 ++ records401_402
theorem aligned400_402 :
    AlignedValid 12 2 missing400_402 records400_402 :=
  aligned400_401.append aligned401_402

def missing402_403 : List (BitVec (edgeCount 12)) :=
  [missing402]
abbrev records402_403 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record402]
theorem aligned402_403 :
    AlignedValid 12 2 missing402_403 records402_403 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check402
    maskCheck402 AlignedValid.nil

def missing403_404 : List (BitVec (edgeCount 12)) :=
  [missing403]
abbrev records403_404 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record403]
theorem aligned403_404 :
    AlignedValid 12 2 missing403_404 records403_404 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check403
    maskCheck403 AlignedValid.nil

def missing402_404 : List (BitVec (edgeCount 12)) :=
  missing402_403 ++ missing403_404
abbrev records402_404 : List Blob :=
  records402_403 ++ records403_404
theorem aligned402_404 :
    AlignedValid 12 2 missing402_404 records402_404 :=
  aligned402_403.append aligned403_404

def missing400_404 : List (BitVec (edgeCount 12)) :=
  missing400_402 ++ missing402_404
abbrev records400_404 : List Blob :=
  records400_402 ++ records402_404
theorem aligned400_404 :
    AlignedValid 12 2 missing400_404 records400_404 :=
  aligned400_402.append aligned402_404

def missing404_405 : List (BitVec (edgeCount 12)) :=
  [missing404]
abbrev records404_405 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record404]
theorem aligned404_405 :
    AlignedValid 12 2 missing404_405 records404_405 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check404
    maskCheck404 AlignedValid.nil

def missing405_406 : List (BitVec (edgeCount 12)) :=
  [missing405]
abbrev records405_406 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record405]
theorem aligned405_406 :
    AlignedValid 12 2 missing405_406 records405_406 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check405
    maskCheck405 AlignedValid.nil

def missing404_406 : List (BitVec (edgeCount 12)) :=
  missing404_405 ++ missing405_406
abbrev records404_406 : List Blob :=
  records404_405 ++ records405_406
theorem aligned404_406 :
    AlignedValid 12 2 missing404_406 records404_406 :=
  aligned404_405.append aligned405_406

def missing406_407 : List (BitVec (edgeCount 12)) :=
  [missing406]
abbrev records406_407 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record406]
theorem aligned406_407 :
    AlignedValid 12 2 missing406_407 records406_407 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check406
    maskCheck406 AlignedValid.nil

def missing407_408 : List (BitVec (edgeCount 12)) :=
  [missing407]
abbrev records407_408 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record407]
theorem aligned407_408 :
    AlignedValid 12 2 missing407_408 records407_408 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check407
    maskCheck407 AlignedValid.nil

def missing406_408 : List (BitVec (edgeCount 12)) :=
  missing406_407 ++ missing407_408
abbrev records406_408 : List Blob :=
  records406_407 ++ records407_408
theorem aligned406_408 :
    AlignedValid 12 2 missing406_408 records406_408 :=
  aligned406_407.append aligned407_408

def missing404_408 : List (BitVec (edgeCount 12)) :=
  missing404_406 ++ missing406_408
abbrev records404_408 : List Blob :=
  records404_406 ++ records406_408
theorem aligned404_408 :
    AlignedValid 12 2 missing404_408 records404_408 :=
  aligned404_406.append aligned406_408

def missing400_408 : List (BitVec (edgeCount 12)) :=
  missing400_404 ++ missing404_408
abbrev records400_408 : List Blob :=
  records400_404 ++ records404_408
theorem aligned400_408 :
    AlignedValid 12 2 missing400_408 records400_408 :=
  aligned400_404.append aligned404_408

def missing408_409 : List (BitVec (edgeCount 12)) :=
  [missing408]
abbrev records408_409 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record408]
theorem aligned408_409 :
    AlignedValid 12 2 missing408_409 records408_409 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check408
    maskCheck408 AlignedValid.nil

def missing409_410 : List (BitVec (edgeCount 12)) :=
  [missing409]
abbrev records409_410 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record409]
theorem aligned409_410 :
    AlignedValid 12 2 missing409_410 records409_410 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check409
    maskCheck409 AlignedValid.nil

def missing408_410 : List (BitVec (edgeCount 12)) :=
  missing408_409 ++ missing409_410
abbrev records408_410 : List Blob :=
  records408_409 ++ records409_410
theorem aligned408_410 :
    AlignedValid 12 2 missing408_410 records408_410 :=
  aligned408_409.append aligned409_410

def missing410_411 : List (BitVec (edgeCount 12)) :=
  [missing410]
abbrev records410_411 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record410]
theorem aligned410_411 :
    AlignedValid 12 2 missing410_411 records410_411 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check410
    maskCheck410 AlignedValid.nil

def missing411_412 : List (BitVec (edgeCount 12)) :=
  [missing411]
abbrev records411_412 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record411]
theorem aligned411_412 :
    AlignedValid 12 2 missing411_412 records411_412 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check411
    maskCheck411 AlignedValid.nil

def missing410_412 : List (BitVec (edgeCount 12)) :=
  missing410_411 ++ missing411_412
abbrev records410_412 : List Blob :=
  records410_411 ++ records411_412
theorem aligned410_412 :
    AlignedValid 12 2 missing410_412 records410_412 :=
  aligned410_411.append aligned411_412

def missing408_412 : List (BitVec (edgeCount 12)) :=
  missing408_410 ++ missing410_412
abbrev records408_412 : List Blob :=
  records408_410 ++ records410_412
theorem aligned408_412 :
    AlignedValid 12 2 missing408_412 records408_412 :=
  aligned408_410.append aligned410_412

def missing412_413 : List (BitVec (edgeCount 12)) :=
  [missing412]
abbrev records412_413 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record412]
theorem aligned412_413 :
    AlignedValid 12 2 missing412_413 records412_413 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check412
    maskCheck412 AlignedValid.nil

def missing413_414 : List (BitVec (edgeCount 12)) :=
  [missing413]
abbrev records413_414 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record413]
theorem aligned413_414 :
    AlignedValid 12 2 missing413_414 records413_414 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check413
    maskCheck413 AlignedValid.nil

def missing412_414 : List (BitVec (edgeCount 12)) :=
  missing412_413 ++ missing413_414
abbrev records412_414 : List Blob :=
  records412_413 ++ records413_414
theorem aligned412_414 :
    AlignedValid 12 2 missing412_414 records412_414 :=
  aligned412_413.append aligned413_414

def missing414_415 : List (BitVec (edgeCount 12)) :=
  [missing414]
abbrev records414_415 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record414]
theorem aligned414_415 :
    AlignedValid 12 2 missing414_415 records414_415 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check414
    maskCheck414 AlignedValid.nil

def missing415_416 : List (BitVec (edgeCount 12)) :=
  [missing415]
abbrev records415_416 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record415]
theorem aligned415_416 :
    AlignedValid 12 2 missing415_416 records415_416 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check415
    maskCheck415 AlignedValid.nil

def missing414_416 : List (BitVec (edgeCount 12)) :=
  missing414_415 ++ missing415_416
abbrev records414_416 : List Blob :=
  records414_415 ++ records415_416
theorem aligned414_416 :
    AlignedValid 12 2 missing414_416 records414_416 :=
  aligned414_415.append aligned415_416

def missing412_416 : List (BitVec (edgeCount 12)) :=
  missing412_414 ++ missing414_416
abbrev records412_416 : List Blob :=
  records412_414 ++ records414_416
theorem aligned412_416 :
    AlignedValid 12 2 missing412_416 records412_416 :=
  aligned412_414.append aligned414_416

def missing408_416 : List (BitVec (edgeCount 12)) :=
  missing408_412 ++ missing412_416
abbrev records408_416 : List Blob :=
  records408_412 ++ records412_416
theorem aligned408_416 :
    AlignedValid 12 2 missing408_416 records408_416 :=
  aligned408_412.append aligned412_416

def missing400_416 : List (BitVec (edgeCount 12)) :=
  missing400_408 ++ missing408_416
abbrev records400_416 : List Blob :=
  records400_408 ++ records408_416
theorem aligned400_416 :
    AlignedValid 12 2 missing400_416 records400_416 :=
  aligned400_408.append aligned408_416

def missing384_416 : List (BitVec (edgeCount 12)) :=
  missing384_400 ++ missing400_416
abbrev records384_416 : List Blob :=
  records384_400 ++ records400_416
theorem aligned384_416 :
    AlignedValid 12 2 missing384_416 records384_416 :=
  aligned384_400.append aligned400_416

def missing416_417 : List (BitVec (edgeCount 12)) :=
  [missing416]
abbrev records416_417 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record416]
theorem aligned416_417 :
    AlignedValid 12 2 missing416_417 records416_417 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check416
    maskCheck416 AlignedValid.nil

def missing417_418 : List (BitVec (edgeCount 12)) :=
  [missing417]
abbrev records417_418 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record417]
theorem aligned417_418 :
    AlignedValid 12 2 missing417_418 records417_418 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check417
    maskCheck417 AlignedValid.nil

def missing416_418 : List (BitVec (edgeCount 12)) :=
  missing416_417 ++ missing417_418
abbrev records416_418 : List Blob :=
  records416_417 ++ records417_418
theorem aligned416_418 :
    AlignedValid 12 2 missing416_418 records416_418 :=
  aligned416_417.append aligned417_418

def missing418_419 : List (BitVec (edgeCount 12)) :=
  [missing418]
abbrev records418_419 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record418]
theorem aligned418_419 :
    AlignedValid 12 2 missing418_419 records418_419 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check418
    maskCheck418 AlignedValid.nil

def missing419_420 : List (BitVec (edgeCount 12)) :=
  [missing419]
abbrev records419_420 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record419]
theorem aligned419_420 :
    AlignedValid 12 2 missing419_420 records419_420 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check419
    maskCheck419 AlignedValid.nil

def missing418_420 : List (BitVec (edgeCount 12)) :=
  missing418_419 ++ missing419_420
abbrev records418_420 : List Blob :=
  records418_419 ++ records419_420
theorem aligned418_420 :
    AlignedValid 12 2 missing418_420 records418_420 :=
  aligned418_419.append aligned419_420

def missing416_420 : List (BitVec (edgeCount 12)) :=
  missing416_418 ++ missing418_420
abbrev records416_420 : List Blob :=
  records416_418 ++ records418_420
theorem aligned416_420 :
    AlignedValid 12 2 missing416_420 records416_420 :=
  aligned416_418.append aligned418_420

def missing420_421 : List (BitVec (edgeCount 12)) :=
  [missing420]
abbrev records420_421 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record420]
theorem aligned420_421 :
    AlignedValid 12 2 missing420_421 records420_421 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check420
    maskCheck420 AlignedValid.nil

def missing421_422 : List (BitVec (edgeCount 12)) :=
  [missing421]
abbrev records421_422 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record421]
theorem aligned421_422 :
    AlignedValid 12 2 missing421_422 records421_422 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check421
    maskCheck421 AlignedValid.nil

def missing420_422 : List (BitVec (edgeCount 12)) :=
  missing420_421 ++ missing421_422
abbrev records420_422 : List Blob :=
  records420_421 ++ records421_422
theorem aligned420_422 :
    AlignedValid 12 2 missing420_422 records420_422 :=
  aligned420_421.append aligned421_422

def missing422_423 : List (BitVec (edgeCount 12)) :=
  [missing422]
abbrev records422_423 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record422]
theorem aligned422_423 :
    AlignedValid 12 2 missing422_423 records422_423 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check422
    maskCheck422 AlignedValid.nil

def missing423_424 : List (BitVec (edgeCount 12)) :=
  [missing423]
abbrev records423_424 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record423]
theorem aligned423_424 :
    AlignedValid 12 2 missing423_424 records423_424 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check423
    maskCheck423 AlignedValid.nil

def missing422_424 : List (BitVec (edgeCount 12)) :=
  missing422_423 ++ missing423_424
abbrev records422_424 : List Blob :=
  records422_423 ++ records423_424
theorem aligned422_424 :
    AlignedValid 12 2 missing422_424 records422_424 :=
  aligned422_423.append aligned423_424

def missing420_424 : List (BitVec (edgeCount 12)) :=
  missing420_422 ++ missing422_424
abbrev records420_424 : List Blob :=
  records420_422 ++ records422_424
theorem aligned420_424 :
    AlignedValid 12 2 missing420_424 records420_424 :=
  aligned420_422.append aligned422_424

def missing416_424 : List (BitVec (edgeCount 12)) :=
  missing416_420 ++ missing420_424
abbrev records416_424 : List Blob :=
  records416_420 ++ records420_424
theorem aligned416_424 :
    AlignedValid 12 2 missing416_424 records416_424 :=
  aligned416_420.append aligned420_424

def missing424_425 : List (BitVec (edgeCount 12)) :=
  [missing424]
abbrev records424_425 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record424]
theorem aligned424_425 :
    AlignedValid 12 2 missing424_425 records424_425 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check424
    maskCheck424 AlignedValid.nil

def missing425_426 : List (BitVec (edgeCount 12)) :=
  [missing425]
abbrev records425_426 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record425]
theorem aligned425_426 :
    AlignedValid 12 2 missing425_426 records425_426 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check425
    maskCheck425 AlignedValid.nil

def missing424_426 : List (BitVec (edgeCount 12)) :=
  missing424_425 ++ missing425_426
abbrev records424_426 : List Blob :=
  records424_425 ++ records425_426
theorem aligned424_426 :
    AlignedValid 12 2 missing424_426 records424_426 :=
  aligned424_425.append aligned425_426

def missing426_427 : List (BitVec (edgeCount 12)) :=
  [missing426]
abbrev records426_427 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record426]
theorem aligned426_427 :
    AlignedValid 12 2 missing426_427 records426_427 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check426
    maskCheck426 AlignedValid.nil

def missing427_428 : List (BitVec (edgeCount 12)) :=
  [missing427]
abbrev records427_428 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record427]
theorem aligned427_428 :
    AlignedValid 12 2 missing427_428 records427_428 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check427
    maskCheck427 AlignedValid.nil

def missing426_428 : List (BitVec (edgeCount 12)) :=
  missing426_427 ++ missing427_428
abbrev records426_428 : List Blob :=
  records426_427 ++ records427_428
theorem aligned426_428 :
    AlignedValid 12 2 missing426_428 records426_428 :=
  aligned426_427.append aligned427_428

def missing424_428 : List (BitVec (edgeCount 12)) :=
  missing424_426 ++ missing426_428
abbrev records424_428 : List Blob :=
  records424_426 ++ records426_428
theorem aligned424_428 :
    AlignedValid 12 2 missing424_428 records424_428 :=
  aligned424_426.append aligned426_428

def missing428_429 : List (BitVec (edgeCount 12)) :=
  [missing428]
abbrev records428_429 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record428]
theorem aligned428_429 :
    AlignedValid 12 2 missing428_429 records428_429 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check428
    maskCheck428 AlignedValid.nil

def missing429_430 : List (BitVec (edgeCount 12)) :=
  [missing429]
abbrev records429_430 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record429]
theorem aligned429_430 :
    AlignedValid 12 2 missing429_430 records429_430 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check429
    maskCheck429 AlignedValid.nil

def missing428_430 : List (BitVec (edgeCount 12)) :=
  missing428_429 ++ missing429_430
abbrev records428_430 : List Blob :=
  records428_429 ++ records429_430
theorem aligned428_430 :
    AlignedValid 12 2 missing428_430 records428_430 :=
  aligned428_429.append aligned429_430

def missing430_431 : List (BitVec (edgeCount 12)) :=
  [missing430]
abbrev records430_431 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record430]
theorem aligned430_431 :
    AlignedValid 12 2 missing430_431 records430_431 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check430
    maskCheck430 AlignedValid.nil

def missing431_432 : List (BitVec (edgeCount 12)) :=
  [missing431]
abbrev records431_432 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record431]
theorem aligned431_432 :
    AlignedValid 12 2 missing431_432 records431_432 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check431
    maskCheck431 AlignedValid.nil

def missing430_432 : List (BitVec (edgeCount 12)) :=
  missing430_431 ++ missing431_432
abbrev records430_432 : List Blob :=
  records430_431 ++ records431_432
theorem aligned430_432 :
    AlignedValid 12 2 missing430_432 records430_432 :=
  aligned430_431.append aligned431_432

def missing428_432 : List (BitVec (edgeCount 12)) :=
  missing428_430 ++ missing430_432
abbrev records428_432 : List Blob :=
  records428_430 ++ records430_432
theorem aligned428_432 :
    AlignedValid 12 2 missing428_432 records428_432 :=
  aligned428_430.append aligned430_432

def missing424_432 : List (BitVec (edgeCount 12)) :=
  missing424_428 ++ missing428_432
abbrev records424_432 : List Blob :=
  records424_428 ++ records428_432
theorem aligned424_432 :
    AlignedValid 12 2 missing424_432 records424_432 :=
  aligned424_428.append aligned428_432

def missing416_432 : List (BitVec (edgeCount 12)) :=
  missing416_424 ++ missing424_432
abbrev records416_432 : List Blob :=
  records416_424 ++ records424_432
theorem aligned416_432 :
    AlignedValid 12 2 missing416_432 records416_432 :=
  aligned416_424.append aligned424_432

def missing432_433 : List (BitVec (edgeCount 12)) :=
  [missing432]
abbrev records432_433 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record432]
theorem aligned432_433 :
    AlignedValid 12 2 missing432_433 records432_433 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check432
    maskCheck432 AlignedValid.nil

def missing433_434 : List (BitVec (edgeCount 12)) :=
  [missing433]
abbrev records433_434 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record433]
theorem aligned433_434 :
    AlignedValid 12 2 missing433_434 records433_434 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check433
    maskCheck433 AlignedValid.nil

def missing432_434 : List (BitVec (edgeCount 12)) :=
  missing432_433 ++ missing433_434
abbrev records432_434 : List Blob :=
  records432_433 ++ records433_434
theorem aligned432_434 :
    AlignedValid 12 2 missing432_434 records432_434 :=
  aligned432_433.append aligned433_434

def missing434_435 : List (BitVec (edgeCount 12)) :=
  [missing434]
abbrev records434_435 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record434]
theorem aligned434_435 :
    AlignedValid 12 2 missing434_435 records434_435 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check434
    maskCheck434 AlignedValid.nil

def missing435_436 : List (BitVec (edgeCount 12)) :=
  [missing435]
abbrev records435_436 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record435]
theorem aligned435_436 :
    AlignedValid 12 2 missing435_436 records435_436 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check435
    maskCheck435 AlignedValid.nil

def missing434_436 : List (BitVec (edgeCount 12)) :=
  missing434_435 ++ missing435_436
abbrev records434_436 : List Blob :=
  records434_435 ++ records435_436
theorem aligned434_436 :
    AlignedValid 12 2 missing434_436 records434_436 :=
  aligned434_435.append aligned435_436

def missing432_436 : List (BitVec (edgeCount 12)) :=
  missing432_434 ++ missing434_436
abbrev records432_436 : List Blob :=
  records432_434 ++ records434_436
theorem aligned432_436 :
    AlignedValid 12 2 missing432_436 records432_436 :=
  aligned432_434.append aligned434_436

def missing436_437 : List (BitVec (edgeCount 12)) :=
  [missing436]
abbrev records436_437 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record436]
theorem aligned436_437 :
    AlignedValid 12 2 missing436_437 records436_437 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check436
    maskCheck436 AlignedValid.nil

def missing437_438 : List (BitVec (edgeCount 12)) :=
  [missing437]
abbrev records437_438 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record437]
theorem aligned437_438 :
    AlignedValid 12 2 missing437_438 records437_438 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check437
    maskCheck437 AlignedValid.nil

def missing436_438 : List (BitVec (edgeCount 12)) :=
  missing436_437 ++ missing437_438
abbrev records436_438 : List Blob :=
  records436_437 ++ records437_438
theorem aligned436_438 :
    AlignedValid 12 2 missing436_438 records436_438 :=
  aligned436_437.append aligned437_438

def missing438_439 : List (BitVec (edgeCount 12)) :=
  [missing438]
abbrev records438_439 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record438]
theorem aligned438_439 :
    AlignedValid 12 2 missing438_439 records438_439 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check438
    maskCheck438 AlignedValid.nil

def missing439_440 : List (BitVec (edgeCount 12)) :=
  [missing439]
abbrev records439_440 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record439]
theorem aligned439_440 :
    AlignedValid 12 2 missing439_440 records439_440 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check439
    maskCheck439 AlignedValid.nil

def missing438_440 : List (BitVec (edgeCount 12)) :=
  missing438_439 ++ missing439_440
abbrev records438_440 : List Blob :=
  records438_439 ++ records439_440
theorem aligned438_440 :
    AlignedValid 12 2 missing438_440 records438_440 :=
  aligned438_439.append aligned439_440

def missing436_440 : List (BitVec (edgeCount 12)) :=
  missing436_438 ++ missing438_440
abbrev records436_440 : List Blob :=
  records436_438 ++ records438_440
theorem aligned436_440 :
    AlignedValid 12 2 missing436_440 records436_440 :=
  aligned436_438.append aligned438_440

def missing432_440 : List (BitVec (edgeCount 12)) :=
  missing432_436 ++ missing436_440
abbrev records432_440 : List Blob :=
  records432_436 ++ records436_440
theorem aligned432_440 :
    AlignedValid 12 2 missing432_440 records432_440 :=
  aligned432_436.append aligned436_440

def missing440_441 : List (BitVec (edgeCount 12)) :=
  [missing440]
abbrev records440_441 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record440]
theorem aligned440_441 :
    AlignedValid 12 2 missing440_441 records440_441 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check440
    maskCheck440 AlignedValid.nil

def missing441_442 : List (BitVec (edgeCount 12)) :=
  [missing441]
abbrev records441_442 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record441]
theorem aligned441_442 :
    AlignedValid 12 2 missing441_442 records441_442 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check441
    maskCheck441 AlignedValid.nil

def missing440_442 : List (BitVec (edgeCount 12)) :=
  missing440_441 ++ missing441_442
abbrev records440_442 : List Blob :=
  records440_441 ++ records441_442
theorem aligned440_442 :
    AlignedValid 12 2 missing440_442 records440_442 :=
  aligned440_441.append aligned441_442

def missing442_443 : List (BitVec (edgeCount 12)) :=
  [missing442]
abbrev records442_443 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record442]
theorem aligned442_443 :
    AlignedValid 12 2 missing442_443 records442_443 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check442
    maskCheck442 AlignedValid.nil

def missing443_444 : List (BitVec (edgeCount 12)) :=
  [missing443]
abbrev records443_444 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record443]
theorem aligned443_444 :
    AlignedValid 12 2 missing443_444 records443_444 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check443
    maskCheck443 AlignedValid.nil

def missing442_444 : List (BitVec (edgeCount 12)) :=
  missing442_443 ++ missing443_444
abbrev records442_444 : List Blob :=
  records442_443 ++ records443_444
theorem aligned442_444 :
    AlignedValid 12 2 missing442_444 records442_444 :=
  aligned442_443.append aligned443_444

def missing440_444 : List (BitVec (edgeCount 12)) :=
  missing440_442 ++ missing442_444
abbrev records440_444 : List Blob :=
  records440_442 ++ records442_444
theorem aligned440_444 :
    AlignedValid 12 2 missing440_444 records440_444 :=
  aligned440_442.append aligned442_444

def missing444_445 : List (BitVec (edgeCount 12)) :=
  [missing444]
abbrev records444_445 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record444]
theorem aligned444_445 :
    AlignedValid 12 2 missing444_445 records444_445 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check444
    maskCheck444 AlignedValid.nil

def missing445_446 : List (BitVec (edgeCount 12)) :=
  [missing445]
abbrev records445_446 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record445]
theorem aligned445_446 :
    AlignedValid 12 2 missing445_446 records445_446 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check445
    maskCheck445 AlignedValid.nil

def missing444_446 : List (BitVec (edgeCount 12)) :=
  missing444_445 ++ missing445_446
abbrev records444_446 : List Blob :=
  records444_445 ++ records445_446
theorem aligned444_446 :
    AlignedValid 12 2 missing444_446 records444_446 :=
  aligned444_445.append aligned445_446

def missing446_447 : List (BitVec (edgeCount 12)) :=
  [missing446]
abbrev records446_447 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record446]
theorem aligned446_447 :
    AlignedValid 12 2 missing446_447 records446_447 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check446
    maskCheck446 AlignedValid.nil

def missing447_448 : List (BitVec (edgeCount 12)) :=
  [missing447]
abbrev records447_448 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record447]
theorem aligned447_448 :
    AlignedValid 12 2 missing447_448 records447_448 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check447
    maskCheck447 AlignedValid.nil

def missing446_448 : List (BitVec (edgeCount 12)) :=
  missing446_447 ++ missing447_448
abbrev records446_448 : List Blob :=
  records446_447 ++ records447_448
theorem aligned446_448 :
    AlignedValid 12 2 missing446_448 records446_448 :=
  aligned446_447.append aligned447_448

def missing444_448 : List (BitVec (edgeCount 12)) :=
  missing444_446 ++ missing446_448
abbrev records444_448 : List Blob :=
  records444_446 ++ records446_448
theorem aligned444_448 :
    AlignedValid 12 2 missing444_448 records444_448 :=
  aligned444_446.append aligned446_448

def missing440_448 : List (BitVec (edgeCount 12)) :=
  missing440_444 ++ missing444_448
abbrev records440_448 : List Blob :=
  records440_444 ++ records444_448
theorem aligned440_448 :
    AlignedValid 12 2 missing440_448 records440_448 :=
  aligned440_444.append aligned444_448

def missing432_448 : List (BitVec (edgeCount 12)) :=
  missing432_440 ++ missing440_448
abbrev records432_448 : List Blob :=
  records432_440 ++ records440_448
theorem aligned432_448 :
    AlignedValid 12 2 missing432_448 records432_448 :=
  aligned432_440.append aligned440_448

def missing416_448 : List (BitVec (edgeCount 12)) :=
  missing416_432 ++ missing432_448
abbrev records416_448 : List Blob :=
  records416_432 ++ records432_448
theorem aligned416_448 :
    AlignedValid 12 2 missing416_448 records416_448 :=
  aligned416_432.append aligned432_448

def missing384_448 : List (BitVec (edgeCount 12)) :=
  missing384_416 ++ missing416_448
abbrev records384_448 : List Blob :=
  records384_416 ++ records416_448
theorem aligned384_448 :
    AlignedValid 12 2 missing384_448 records384_448 :=
  aligned384_416.append aligned416_448

def missing448_449 : List (BitVec (edgeCount 12)) :=
  [missing448]
abbrev records448_449 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record448]
theorem aligned448_449 :
    AlignedValid 12 2 missing448_449 records448_449 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check448
    maskCheck448 AlignedValid.nil

def missing449_450 : List (BitVec (edgeCount 12)) :=
  [missing449]
abbrev records449_450 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record449]
theorem aligned449_450 :
    AlignedValid 12 2 missing449_450 records449_450 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check449
    maskCheck449 AlignedValid.nil

def missing448_450 : List (BitVec (edgeCount 12)) :=
  missing448_449 ++ missing449_450
abbrev records448_450 : List Blob :=
  records448_449 ++ records449_450
theorem aligned448_450 :
    AlignedValid 12 2 missing448_450 records448_450 :=
  aligned448_449.append aligned449_450

def missing450_451 : List (BitVec (edgeCount 12)) :=
  [missing450]
abbrev records450_451 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record450]
theorem aligned450_451 :
    AlignedValid 12 2 missing450_451 records450_451 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check450
    maskCheck450 AlignedValid.nil

def missing451_452 : List (BitVec (edgeCount 12)) :=
  [missing451]
abbrev records451_452 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record451]
theorem aligned451_452 :
    AlignedValid 12 2 missing451_452 records451_452 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check451
    maskCheck451 AlignedValid.nil

def missing450_452 : List (BitVec (edgeCount 12)) :=
  missing450_451 ++ missing451_452
abbrev records450_452 : List Blob :=
  records450_451 ++ records451_452
theorem aligned450_452 :
    AlignedValid 12 2 missing450_452 records450_452 :=
  aligned450_451.append aligned451_452

def missing448_452 : List (BitVec (edgeCount 12)) :=
  missing448_450 ++ missing450_452
abbrev records448_452 : List Blob :=
  records448_450 ++ records450_452
theorem aligned448_452 :
    AlignedValid 12 2 missing448_452 records448_452 :=
  aligned448_450.append aligned450_452

def missing452_453 : List (BitVec (edgeCount 12)) :=
  [missing452]
abbrev records452_453 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record452]
theorem aligned452_453 :
    AlignedValid 12 2 missing452_453 records452_453 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check452
    maskCheck452 AlignedValid.nil

def missing453_454 : List (BitVec (edgeCount 12)) :=
  [missing453]
abbrev records453_454 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record453]
theorem aligned453_454 :
    AlignedValid 12 2 missing453_454 records453_454 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check453
    maskCheck453 AlignedValid.nil

def missing452_454 : List (BitVec (edgeCount 12)) :=
  missing452_453 ++ missing453_454
abbrev records452_454 : List Blob :=
  records452_453 ++ records453_454
theorem aligned452_454 :
    AlignedValid 12 2 missing452_454 records452_454 :=
  aligned452_453.append aligned453_454

def missing454_455 : List (BitVec (edgeCount 12)) :=
  [missing454]
abbrev records454_455 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record454]
theorem aligned454_455 :
    AlignedValid 12 2 missing454_455 records454_455 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check454
    maskCheck454 AlignedValid.nil

def missing455_456 : List (BitVec (edgeCount 12)) :=
  [missing455]
abbrev records455_456 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record455]
theorem aligned455_456 :
    AlignedValid 12 2 missing455_456 records455_456 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check455
    maskCheck455 AlignedValid.nil

def missing454_456 : List (BitVec (edgeCount 12)) :=
  missing454_455 ++ missing455_456
abbrev records454_456 : List Blob :=
  records454_455 ++ records455_456
theorem aligned454_456 :
    AlignedValid 12 2 missing454_456 records454_456 :=
  aligned454_455.append aligned455_456

def missing452_456 : List (BitVec (edgeCount 12)) :=
  missing452_454 ++ missing454_456
abbrev records452_456 : List Blob :=
  records452_454 ++ records454_456
theorem aligned452_456 :
    AlignedValid 12 2 missing452_456 records452_456 :=
  aligned452_454.append aligned454_456

def missing448_456 : List (BitVec (edgeCount 12)) :=
  missing448_452 ++ missing452_456
abbrev records448_456 : List Blob :=
  records448_452 ++ records452_456
theorem aligned448_456 :
    AlignedValid 12 2 missing448_456 records448_456 :=
  aligned448_452.append aligned452_456

def missing456_457 : List (BitVec (edgeCount 12)) :=
  [missing456]
abbrev records456_457 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record456]
theorem aligned456_457 :
    AlignedValid 12 2 missing456_457 records456_457 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check456
    maskCheck456 AlignedValid.nil

def missing457_458 : List (BitVec (edgeCount 12)) :=
  [missing457]
abbrev records457_458 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record457]
theorem aligned457_458 :
    AlignedValid 12 2 missing457_458 records457_458 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check457
    maskCheck457 AlignedValid.nil

def missing456_458 : List (BitVec (edgeCount 12)) :=
  missing456_457 ++ missing457_458
abbrev records456_458 : List Blob :=
  records456_457 ++ records457_458
theorem aligned456_458 :
    AlignedValid 12 2 missing456_458 records456_458 :=
  aligned456_457.append aligned457_458

def missing458_459 : List (BitVec (edgeCount 12)) :=
  [missing458]
abbrev records458_459 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record458]
theorem aligned458_459 :
    AlignedValid 12 2 missing458_459 records458_459 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check458
    maskCheck458 AlignedValid.nil

def missing459_460 : List (BitVec (edgeCount 12)) :=
  [missing459]
abbrev records459_460 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record459]
theorem aligned459_460 :
    AlignedValid 12 2 missing459_460 records459_460 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check459
    maskCheck459 AlignedValid.nil

def missing458_460 : List (BitVec (edgeCount 12)) :=
  missing458_459 ++ missing459_460
abbrev records458_460 : List Blob :=
  records458_459 ++ records459_460
theorem aligned458_460 :
    AlignedValid 12 2 missing458_460 records458_460 :=
  aligned458_459.append aligned459_460

def missing456_460 : List (BitVec (edgeCount 12)) :=
  missing456_458 ++ missing458_460
abbrev records456_460 : List Blob :=
  records456_458 ++ records458_460
theorem aligned456_460 :
    AlignedValid 12 2 missing456_460 records456_460 :=
  aligned456_458.append aligned458_460

def missing460_461 : List (BitVec (edgeCount 12)) :=
  [missing460]
abbrev records460_461 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record460]
theorem aligned460_461 :
    AlignedValid 12 2 missing460_461 records460_461 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check460
    maskCheck460 AlignedValid.nil

def missing461_462 : List (BitVec (edgeCount 12)) :=
  [missing461]
abbrev records461_462 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record461]
theorem aligned461_462 :
    AlignedValid 12 2 missing461_462 records461_462 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check461
    maskCheck461 AlignedValid.nil

def missing460_462 : List (BitVec (edgeCount 12)) :=
  missing460_461 ++ missing461_462
abbrev records460_462 : List Blob :=
  records460_461 ++ records461_462
theorem aligned460_462 :
    AlignedValid 12 2 missing460_462 records460_462 :=
  aligned460_461.append aligned461_462

def missing462_463 : List (BitVec (edgeCount 12)) :=
  [missing462]
abbrev records462_463 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record462]
theorem aligned462_463 :
    AlignedValid 12 2 missing462_463 records462_463 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check462
    maskCheck462 AlignedValid.nil

def missing463_464 : List (BitVec (edgeCount 12)) :=
  [missing463]
abbrev records463_464 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record463]
theorem aligned463_464 :
    AlignedValid 12 2 missing463_464 records463_464 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check463
    maskCheck463 AlignedValid.nil

def missing462_464 : List (BitVec (edgeCount 12)) :=
  missing462_463 ++ missing463_464
abbrev records462_464 : List Blob :=
  records462_463 ++ records463_464
theorem aligned462_464 :
    AlignedValid 12 2 missing462_464 records462_464 :=
  aligned462_463.append aligned463_464

def missing460_464 : List (BitVec (edgeCount 12)) :=
  missing460_462 ++ missing462_464
abbrev records460_464 : List Blob :=
  records460_462 ++ records462_464
theorem aligned460_464 :
    AlignedValid 12 2 missing460_464 records460_464 :=
  aligned460_462.append aligned462_464

def missing456_464 : List (BitVec (edgeCount 12)) :=
  missing456_460 ++ missing460_464
abbrev records456_464 : List Blob :=
  records456_460 ++ records460_464
theorem aligned456_464 :
    AlignedValid 12 2 missing456_464 records456_464 :=
  aligned456_460.append aligned460_464

def missing448_464 : List (BitVec (edgeCount 12)) :=
  missing448_456 ++ missing456_464
abbrev records448_464 : List Blob :=
  records448_456 ++ records456_464
theorem aligned448_464 :
    AlignedValid 12 2 missing448_464 records448_464 :=
  aligned448_456.append aligned456_464

def missing464_465 : List (BitVec (edgeCount 12)) :=
  [missing464]
abbrev records464_465 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record464]
theorem aligned464_465 :
    AlignedValid 12 2 missing464_465 records464_465 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check464
    maskCheck464 AlignedValid.nil

def missing465_466 : List (BitVec (edgeCount 12)) :=
  [missing465]
abbrev records465_466 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record465]
theorem aligned465_466 :
    AlignedValid 12 2 missing465_466 records465_466 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check465
    maskCheck465 AlignedValid.nil

def missing464_466 : List (BitVec (edgeCount 12)) :=
  missing464_465 ++ missing465_466
abbrev records464_466 : List Blob :=
  records464_465 ++ records465_466
theorem aligned464_466 :
    AlignedValid 12 2 missing464_466 records464_466 :=
  aligned464_465.append aligned465_466

def missing466_467 : List (BitVec (edgeCount 12)) :=
  [missing466]
abbrev records466_467 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record466]
theorem aligned466_467 :
    AlignedValid 12 2 missing466_467 records466_467 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check466
    maskCheck466 AlignedValid.nil

def missing467_468 : List (BitVec (edgeCount 12)) :=
  [missing467]
abbrev records467_468 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record467]
theorem aligned467_468 :
    AlignedValid 12 2 missing467_468 records467_468 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check467
    maskCheck467 AlignedValid.nil

def missing466_468 : List (BitVec (edgeCount 12)) :=
  missing466_467 ++ missing467_468
abbrev records466_468 : List Blob :=
  records466_467 ++ records467_468
theorem aligned466_468 :
    AlignedValid 12 2 missing466_468 records466_468 :=
  aligned466_467.append aligned467_468

def missing464_468 : List (BitVec (edgeCount 12)) :=
  missing464_466 ++ missing466_468
abbrev records464_468 : List Blob :=
  records464_466 ++ records466_468
theorem aligned464_468 :
    AlignedValid 12 2 missing464_468 records464_468 :=
  aligned464_466.append aligned466_468

def missing468_469 : List (BitVec (edgeCount 12)) :=
  [missing468]
abbrev records468_469 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record468]
theorem aligned468_469 :
    AlignedValid 12 2 missing468_469 records468_469 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check468
    maskCheck468 AlignedValid.nil

def missing469_470 : List (BitVec (edgeCount 12)) :=
  [missing469]
abbrev records469_470 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record469]
theorem aligned469_470 :
    AlignedValid 12 2 missing469_470 records469_470 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check469
    maskCheck469 AlignedValid.nil

def missing468_470 : List (BitVec (edgeCount 12)) :=
  missing468_469 ++ missing469_470
abbrev records468_470 : List Blob :=
  records468_469 ++ records469_470
theorem aligned468_470 :
    AlignedValid 12 2 missing468_470 records468_470 :=
  aligned468_469.append aligned469_470

def missing470_471 : List (BitVec (edgeCount 12)) :=
  [missing470]
abbrev records470_471 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record470]
theorem aligned470_471 :
    AlignedValid 12 2 missing470_471 records470_471 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check470
    maskCheck470 AlignedValid.nil

def missing471_472 : List (BitVec (edgeCount 12)) :=
  [missing471]
abbrev records471_472 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record471]
theorem aligned471_472 :
    AlignedValid 12 2 missing471_472 records471_472 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check471
    maskCheck471 AlignedValid.nil

def missing470_472 : List (BitVec (edgeCount 12)) :=
  missing470_471 ++ missing471_472
abbrev records470_472 : List Blob :=
  records470_471 ++ records471_472
theorem aligned470_472 :
    AlignedValid 12 2 missing470_472 records470_472 :=
  aligned470_471.append aligned471_472

def missing468_472 : List (BitVec (edgeCount 12)) :=
  missing468_470 ++ missing470_472
abbrev records468_472 : List Blob :=
  records468_470 ++ records470_472
theorem aligned468_472 :
    AlignedValid 12 2 missing468_472 records468_472 :=
  aligned468_470.append aligned470_472

def missing464_472 : List (BitVec (edgeCount 12)) :=
  missing464_468 ++ missing468_472
abbrev records464_472 : List Blob :=
  records464_468 ++ records468_472
theorem aligned464_472 :
    AlignedValid 12 2 missing464_472 records464_472 :=
  aligned464_468.append aligned468_472

def missing472_473 : List (BitVec (edgeCount 12)) :=
  [missing472]
abbrev records472_473 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record472]
theorem aligned472_473 :
    AlignedValid 12 2 missing472_473 records472_473 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check472
    maskCheck472 AlignedValid.nil

def missing473_474 : List (BitVec (edgeCount 12)) :=
  [missing473]
abbrev records473_474 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record473]
theorem aligned473_474 :
    AlignedValid 12 2 missing473_474 records473_474 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check473
    maskCheck473 AlignedValid.nil

def missing472_474 : List (BitVec (edgeCount 12)) :=
  missing472_473 ++ missing473_474
abbrev records472_474 : List Blob :=
  records472_473 ++ records473_474
theorem aligned472_474 :
    AlignedValid 12 2 missing472_474 records472_474 :=
  aligned472_473.append aligned473_474

def missing474_475 : List (BitVec (edgeCount 12)) :=
  [missing474]
abbrev records474_475 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record474]
theorem aligned474_475 :
    AlignedValid 12 2 missing474_475 records474_475 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check474
    maskCheck474 AlignedValid.nil

def missing475_476 : List (BitVec (edgeCount 12)) :=
  [missing475]
abbrev records475_476 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record475]
theorem aligned475_476 :
    AlignedValid 12 2 missing475_476 records475_476 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check475
    maskCheck475 AlignedValid.nil

def missing474_476 : List (BitVec (edgeCount 12)) :=
  missing474_475 ++ missing475_476
abbrev records474_476 : List Blob :=
  records474_475 ++ records475_476
theorem aligned474_476 :
    AlignedValid 12 2 missing474_476 records474_476 :=
  aligned474_475.append aligned475_476

def missing472_476 : List (BitVec (edgeCount 12)) :=
  missing472_474 ++ missing474_476
abbrev records472_476 : List Blob :=
  records472_474 ++ records474_476
theorem aligned472_476 :
    AlignedValid 12 2 missing472_476 records472_476 :=
  aligned472_474.append aligned474_476

def missing476_477 : List (BitVec (edgeCount 12)) :=
  [missing476]
abbrev records476_477 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record476]
theorem aligned476_477 :
    AlignedValid 12 2 missing476_477 records476_477 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check476
    maskCheck476 AlignedValid.nil

def missing477_478 : List (BitVec (edgeCount 12)) :=
  [missing477]
abbrev records477_478 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record477]
theorem aligned477_478 :
    AlignedValid 12 2 missing477_478 records477_478 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check477
    maskCheck477 AlignedValid.nil

def missing476_478 : List (BitVec (edgeCount 12)) :=
  missing476_477 ++ missing477_478
abbrev records476_478 : List Blob :=
  records476_477 ++ records477_478
theorem aligned476_478 :
    AlignedValid 12 2 missing476_478 records476_478 :=
  aligned476_477.append aligned477_478

def missing478_479 : List (BitVec (edgeCount 12)) :=
  [missing478]
abbrev records478_479 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record478]
theorem aligned478_479 :
    AlignedValid 12 2 missing478_479 records478_479 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check478
    maskCheck478 AlignedValid.nil

def missing479_480 : List (BitVec (edgeCount 12)) :=
  [missing479]
abbrev records479_480 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record479]
theorem aligned479_480 :
    AlignedValid 12 2 missing479_480 records479_480 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check479
    maskCheck479 AlignedValid.nil

def missing478_480 : List (BitVec (edgeCount 12)) :=
  missing478_479 ++ missing479_480
abbrev records478_480 : List Blob :=
  records478_479 ++ records479_480
theorem aligned478_480 :
    AlignedValid 12 2 missing478_480 records478_480 :=
  aligned478_479.append aligned479_480

def missing476_480 : List (BitVec (edgeCount 12)) :=
  missing476_478 ++ missing478_480
abbrev records476_480 : List Blob :=
  records476_478 ++ records478_480
theorem aligned476_480 :
    AlignedValid 12 2 missing476_480 records476_480 :=
  aligned476_478.append aligned478_480

def missing472_480 : List (BitVec (edgeCount 12)) :=
  missing472_476 ++ missing476_480
abbrev records472_480 : List Blob :=
  records472_476 ++ records476_480
theorem aligned472_480 :
    AlignedValid 12 2 missing472_480 records472_480 :=
  aligned472_476.append aligned476_480

def missing464_480 : List (BitVec (edgeCount 12)) :=
  missing464_472 ++ missing472_480
abbrev records464_480 : List Blob :=
  records464_472 ++ records472_480
theorem aligned464_480 :
    AlignedValid 12 2 missing464_480 records464_480 :=
  aligned464_472.append aligned472_480

def missing448_480 : List (BitVec (edgeCount 12)) :=
  missing448_464 ++ missing464_480
abbrev records448_480 : List Blob :=
  records448_464 ++ records464_480
theorem aligned448_480 :
    AlignedValid 12 2 missing448_480 records448_480 :=
  aligned448_464.append aligned464_480

def missing480_481 : List (BitVec (edgeCount 12)) :=
  [missing480]
abbrev records480_481 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record480]
theorem aligned480_481 :
    AlignedValid 12 2 missing480_481 records480_481 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check480
    maskCheck480 AlignedValid.nil

def missing481_482 : List (BitVec (edgeCount 12)) :=
  [missing481]
abbrev records481_482 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record481]
theorem aligned481_482 :
    AlignedValid 12 2 missing481_482 records481_482 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check481
    maskCheck481 AlignedValid.nil

def missing480_482 : List (BitVec (edgeCount 12)) :=
  missing480_481 ++ missing481_482
abbrev records480_482 : List Blob :=
  records480_481 ++ records481_482
theorem aligned480_482 :
    AlignedValid 12 2 missing480_482 records480_482 :=
  aligned480_481.append aligned481_482

def missing482_483 : List (BitVec (edgeCount 12)) :=
  [missing482]
abbrev records482_483 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record482]
theorem aligned482_483 :
    AlignedValid 12 2 missing482_483 records482_483 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check482
    maskCheck482 AlignedValid.nil

def missing483_484 : List (BitVec (edgeCount 12)) :=
  [missing483]
abbrev records483_484 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record483]
theorem aligned483_484 :
    AlignedValid 12 2 missing483_484 records483_484 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check483
    maskCheck483 AlignedValid.nil

def missing482_484 : List (BitVec (edgeCount 12)) :=
  missing482_483 ++ missing483_484
abbrev records482_484 : List Blob :=
  records482_483 ++ records483_484
theorem aligned482_484 :
    AlignedValid 12 2 missing482_484 records482_484 :=
  aligned482_483.append aligned483_484

def missing480_484 : List (BitVec (edgeCount 12)) :=
  missing480_482 ++ missing482_484
abbrev records480_484 : List Blob :=
  records480_482 ++ records482_484
theorem aligned480_484 :
    AlignedValid 12 2 missing480_484 records480_484 :=
  aligned480_482.append aligned482_484

def missing484_485 : List (BitVec (edgeCount 12)) :=
  [missing484]
abbrev records484_485 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record484]
theorem aligned484_485 :
    AlignedValid 12 2 missing484_485 records484_485 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check484
    maskCheck484 AlignedValid.nil

def missing485_486 : List (BitVec (edgeCount 12)) :=
  [missing485]
abbrev records485_486 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record485]
theorem aligned485_486 :
    AlignedValid 12 2 missing485_486 records485_486 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check485
    maskCheck485 AlignedValid.nil

def missing484_486 : List (BitVec (edgeCount 12)) :=
  missing484_485 ++ missing485_486
abbrev records484_486 : List Blob :=
  records484_485 ++ records485_486
theorem aligned484_486 :
    AlignedValid 12 2 missing484_486 records484_486 :=
  aligned484_485.append aligned485_486

def missing486_487 : List (BitVec (edgeCount 12)) :=
  [missing486]
abbrev records486_487 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record486]
theorem aligned486_487 :
    AlignedValid 12 2 missing486_487 records486_487 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check486
    maskCheck486 AlignedValid.nil

def missing487_488 : List (BitVec (edgeCount 12)) :=
  [missing487]
abbrev records487_488 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record487]
theorem aligned487_488 :
    AlignedValid 12 2 missing487_488 records487_488 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check487
    maskCheck487 AlignedValid.nil

def missing486_488 : List (BitVec (edgeCount 12)) :=
  missing486_487 ++ missing487_488
abbrev records486_488 : List Blob :=
  records486_487 ++ records487_488
theorem aligned486_488 :
    AlignedValid 12 2 missing486_488 records486_488 :=
  aligned486_487.append aligned487_488

def missing484_488 : List (BitVec (edgeCount 12)) :=
  missing484_486 ++ missing486_488
abbrev records484_488 : List Blob :=
  records484_486 ++ records486_488
theorem aligned484_488 :
    AlignedValid 12 2 missing484_488 records484_488 :=
  aligned484_486.append aligned486_488

def missing480_488 : List (BitVec (edgeCount 12)) :=
  missing480_484 ++ missing484_488
abbrev records480_488 : List Blob :=
  records480_484 ++ records484_488
theorem aligned480_488 :
    AlignedValid 12 2 missing480_488 records480_488 :=
  aligned480_484.append aligned484_488

def missing488_489 : List (BitVec (edgeCount 12)) :=
  [missing488]
abbrev records488_489 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record488]
theorem aligned488_489 :
    AlignedValid 12 2 missing488_489 records488_489 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check488
    maskCheck488 AlignedValid.nil

def missing489_490 : List (BitVec (edgeCount 12)) :=
  [missing489]
abbrev records489_490 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record489]
theorem aligned489_490 :
    AlignedValid 12 2 missing489_490 records489_490 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check489
    maskCheck489 AlignedValid.nil

def missing488_490 : List (BitVec (edgeCount 12)) :=
  missing488_489 ++ missing489_490
abbrev records488_490 : List Blob :=
  records488_489 ++ records489_490
theorem aligned488_490 :
    AlignedValid 12 2 missing488_490 records488_490 :=
  aligned488_489.append aligned489_490

def missing490_491 : List (BitVec (edgeCount 12)) :=
  [missing490]
abbrev records490_491 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record490]
theorem aligned490_491 :
    AlignedValid 12 2 missing490_491 records490_491 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check490
    maskCheck490 AlignedValid.nil

def missing491_492 : List (BitVec (edgeCount 12)) :=
  [missing491]
abbrev records491_492 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record491]
theorem aligned491_492 :
    AlignedValid 12 2 missing491_492 records491_492 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check491
    maskCheck491 AlignedValid.nil

def missing490_492 : List (BitVec (edgeCount 12)) :=
  missing490_491 ++ missing491_492
abbrev records490_492 : List Blob :=
  records490_491 ++ records491_492
theorem aligned490_492 :
    AlignedValid 12 2 missing490_492 records490_492 :=
  aligned490_491.append aligned491_492

def missing488_492 : List (BitVec (edgeCount 12)) :=
  missing488_490 ++ missing490_492
abbrev records488_492 : List Blob :=
  records488_490 ++ records490_492
theorem aligned488_492 :
    AlignedValid 12 2 missing488_492 records488_492 :=
  aligned488_490.append aligned490_492

def missing492_493 : List (BitVec (edgeCount 12)) :=
  [missing492]
abbrev records492_493 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record492]
theorem aligned492_493 :
    AlignedValid 12 2 missing492_493 records492_493 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check492
    maskCheck492 AlignedValid.nil

def missing493_494 : List (BitVec (edgeCount 12)) :=
  [missing493]
abbrev records493_494 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record493]
theorem aligned493_494 :
    AlignedValid 12 2 missing493_494 records493_494 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check493
    maskCheck493 AlignedValid.nil

def missing492_494 : List (BitVec (edgeCount 12)) :=
  missing492_493 ++ missing493_494
abbrev records492_494 : List Blob :=
  records492_493 ++ records493_494
theorem aligned492_494 :
    AlignedValid 12 2 missing492_494 records492_494 :=
  aligned492_493.append aligned493_494

def missing494_495 : List (BitVec (edgeCount 12)) :=
  [missing494]
abbrev records494_495 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record494]
theorem aligned494_495 :
    AlignedValid 12 2 missing494_495 records494_495 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check494
    maskCheck494 AlignedValid.nil

def missing495_496 : List (BitVec (edgeCount 12)) :=
  [missing495]
abbrev records495_496 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record495]
theorem aligned495_496 :
    AlignedValid 12 2 missing495_496 records495_496 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check495
    maskCheck495 AlignedValid.nil

def missing494_496 : List (BitVec (edgeCount 12)) :=
  missing494_495 ++ missing495_496
abbrev records494_496 : List Blob :=
  records494_495 ++ records495_496
theorem aligned494_496 :
    AlignedValid 12 2 missing494_496 records494_496 :=
  aligned494_495.append aligned495_496

def missing492_496 : List (BitVec (edgeCount 12)) :=
  missing492_494 ++ missing494_496
abbrev records492_496 : List Blob :=
  records492_494 ++ records494_496
theorem aligned492_496 :
    AlignedValid 12 2 missing492_496 records492_496 :=
  aligned492_494.append aligned494_496

def missing488_496 : List (BitVec (edgeCount 12)) :=
  missing488_492 ++ missing492_496
abbrev records488_496 : List Blob :=
  records488_492 ++ records492_496
theorem aligned488_496 :
    AlignedValid 12 2 missing488_496 records488_496 :=
  aligned488_492.append aligned492_496

def missing480_496 : List (BitVec (edgeCount 12)) :=
  missing480_488 ++ missing488_496
abbrev records480_496 : List Blob :=
  records480_488 ++ records488_496
theorem aligned480_496 :
    AlignedValid 12 2 missing480_496 records480_496 :=
  aligned480_488.append aligned488_496

def missing496_497 : List (BitVec (edgeCount 12)) :=
  [missing496]
abbrev records496_497 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record496]
theorem aligned496_497 :
    AlignedValid 12 2 missing496_497 records496_497 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check496
    maskCheck496 AlignedValid.nil

def missing497_498 : List (BitVec (edgeCount 12)) :=
  [missing497]
abbrev records497_498 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record497]
theorem aligned497_498 :
    AlignedValid 12 2 missing497_498 records497_498 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check497
    maskCheck497 AlignedValid.nil

def missing496_498 : List (BitVec (edgeCount 12)) :=
  missing496_497 ++ missing497_498
abbrev records496_498 : List Blob :=
  records496_497 ++ records497_498
theorem aligned496_498 :
    AlignedValid 12 2 missing496_498 records496_498 :=
  aligned496_497.append aligned497_498

def missing498_499 : List (BitVec (edgeCount 12)) :=
  [missing498]
abbrev records498_499 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record498]
theorem aligned498_499 :
    AlignedValid 12 2 missing498_499 records498_499 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check498
    maskCheck498 AlignedValid.nil

def missing499_500 : List (BitVec (edgeCount 12)) :=
  [missing499]
abbrev records499_500 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record499]
theorem aligned499_500 :
    AlignedValid 12 2 missing499_500 records499_500 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check499
    maskCheck499 AlignedValid.nil

def missing498_500 : List (BitVec (edgeCount 12)) :=
  missing498_499 ++ missing499_500
abbrev records498_500 : List Blob :=
  records498_499 ++ records499_500
theorem aligned498_500 :
    AlignedValid 12 2 missing498_500 records498_500 :=
  aligned498_499.append aligned499_500

def missing496_500 : List (BitVec (edgeCount 12)) :=
  missing496_498 ++ missing498_500
abbrev records496_500 : List Blob :=
  records496_498 ++ records498_500
theorem aligned496_500 :
    AlignedValid 12 2 missing496_500 records496_500 :=
  aligned496_498.append aligned498_500

def missing500_501 : List (BitVec (edgeCount 12)) :=
  [missing500]
abbrev records500_501 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record500]
theorem aligned500_501 :
    AlignedValid 12 2 missing500_501 records500_501 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check500
    maskCheck500 AlignedValid.nil

def missing501_502 : List (BitVec (edgeCount 12)) :=
  [missing501]
abbrev records501_502 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record501]
theorem aligned501_502 :
    AlignedValid 12 2 missing501_502 records501_502 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check501
    maskCheck501 AlignedValid.nil

def missing500_502 : List (BitVec (edgeCount 12)) :=
  missing500_501 ++ missing501_502
abbrev records500_502 : List Blob :=
  records500_501 ++ records501_502
theorem aligned500_502 :
    AlignedValid 12 2 missing500_502 records500_502 :=
  aligned500_501.append aligned501_502

def missing502_503 : List (BitVec (edgeCount 12)) :=
  [missing502]
abbrev records502_503 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record502]
theorem aligned502_503 :
    AlignedValid 12 2 missing502_503 records502_503 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check502
    maskCheck502 AlignedValid.nil

def missing503_504 : List (BitVec (edgeCount 12)) :=
  [missing503]
abbrev records503_504 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record503]
theorem aligned503_504 :
    AlignedValid 12 2 missing503_504 records503_504 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check503
    maskCheck503 AlignedValid.nil

def missing502_504 : List (BitVec (edgeCount 12)) :=
  missing502_503 ++ missing503_504
abbrev records502_504 : List Blob :=
  records502_503 ++ records503_504
theorem aligned502_504 :
    AlignedValid 12 2 missing502_504 records502_504 :=
  aligned502_503.append aligned503_504

def missing500_504 : List (BitVec (edgeCount 12)) :=
  missing500_502 ++ missing502_504
abbrev records500_504 : List Blob :=
  records500_502 ++ records502_504
theorem aligned500_504 :
    AlignedValid 12 2 missing500_504 records500_504 :=
  aligned500_502.append aligned502_504

def missing496_504 : List (BitVec (edgeCount 12)) :=
  missing496_500 ++ missing500_504
abbrev records496_504 : List Blob :=
  records496_500 ++ records500_504
theorem aligned496_504 :
    AlignedValid 12 2 missing496_504 records496_504 :=
  aligned496_500.append aligned500_504

def missing504_505 : List (BitVec (edgeCount 12)) :=
  [missing504]
abbrev records504_505 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record504]
theorem aligned504_505 :
    AlignedValid 12 2 missing504_505 records504_505 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check504
    maskCheck504 AlignedValid.nil

def missing505_506 : List (BitVec (edgeCount 12)) :=
  [missing505]
abbrev records505_506 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record505]
theorem aligned505_506 :
    AlignedValid 12 2 missing505_506 records505_506 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check505
    maskCheck505 AlignedValid.nil

def missing504_506 : List (BitVec (edgeCount 12)) :=
  missing504_505 ++ missing505_506
abbrev records504_506 : List Blob :=
  records504_505 ++ records505_506
theorem aligned504_506 :
    AlignedValid 12 2 missing504_506 records504_506 :=
  aligned504_505.append aligned505_506

def missing506_507 : List (BitVec (edgeCount 12)) :=
  [missing506]
abbrev records506_507 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record506]
theorem aligned506_507 :
    AlignedValid 12 2 missing506_507 records506_507 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check506
    maskCheck506 AlignedValid.nil

def missing507_508 : List (BitVec (edgeCount 12)) :=
  [missing507]
abbrev records507_508 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record507]
theorem aligned507_508 :
    AlignedValid 12 2 missing507_508 records507_508 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check507
    maskCheck507 AlignedValid.nil

def missing506_508 : List (BitVec (edgeCount 12)) :=
  missing506_507 ++ missing507_508
abbrev records506_508 : List Blob :=
  records506_507 ++ records507_508
theorem aligned506_508 :
    AlignedValid 12 2 missing506_508 records506_508 :=
  aligned506_507.append aligned507_508

def missing504_508 : List (BitVec (edgeCount 12)) :=
  missing504_506 ++ missing506_508
abbrev records504_508 : List Blob :=
  records504_506 ++ records506_508
theorem aligned504_508 :
    AlignedValid 12 2 missing504_508 records504_508 :=
  aligned504_506.append aligned506_508

def missing508_509 : List (BitVec (edgeCount 12)) :=
  [missing508]
abbrev records508_509 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record508]
theorem aligned508_509 :
    AlignedValid 12 2 missing508_509 records508_509 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check508
    maskCheck508 AlignedValid.nil

def missing509_510 : List (BitVec (edgeCount 12)) :=
  [missing509]
abbrev records509_510 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record509]
theorem aligned509_510 :
    AlignedValid 12 2 missing509_510 records509_510 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check509
    maskCheck509 AlignedValid.nil

def missing508_510 : List (BitVec (edgeCount 12)) :=
  missing508_509 ++ missing509_510
abbrev records508_510 : List Blob :=
  records508_509 ++ records509_510
theorem aligned508_510 :
    AlignedValid 12 2 missing508_510 records508_510 :=
  aligned508_509.append aligned509_510

def missing510_511 : List (BitVec (edgeCount 12)) :=
  [missing510]
abbrev records510_511 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record510]
theorem aligned510_511 :
    AlignedValid 12 2 missing510_511 records510_511 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check510
    maskCheck510 AlignedValid.nil

def missing511_512 : List (BitVec (edgeCount 12)) :=
  [missing511]
abbrev records511_512 : List Blob :=
  [StrongPackedBucketN12A2Shard003.record511]
theorem aligned511_512 :
    AlignedValid 12 2 missing511_512 records511_512 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard003.check511
    maskCheck511 AlignedValid.nil

def missing510_512 : List (BitVec (edgeCount 12)) :=
  missing510_511 ++ missing511_512
abbrev records510_512 : List Blob :=
  records510_511 ++ records511_512
theorem aligned510_512 :
    AlignedValid 12 2 missing510_512 records510_512 :=
  aligned510_511.append aligned511_512

def missing508_512 : List (BitVec (edgeCount 12)) :=
  missing508_510 ++ missing510_512
abbrev records508_512 : List Blob :=
  records508_510 ++ records510_512
theorem aligned508_512 :
    AlignedValid 12 2 missing508_512 records508_512 :=
  aligned508_510.append aligned510_512

def missing504_512 : List (BitVec (edgeCount 12)) :=
  missing504_508 ++ missing508_512
abbrev records504_512 : List Blob :=
  records504_508 ++ records508_512
theorem aligned504_512 :
    AlignedValid 12 2 missing504_512 records504_512 :=
  aligned504_508.append aligned508_512

def missing496_512 : List (BitVec (edgeCount 12)) :=
  missing496_504 ++ missing504_512
abbrev records496_512 : List Blob :=
  records496_504 ++ records504_512
theorem aligned496_512 :
    AlignedValid 12 2 missing496_512 records496_512 :=
  aligned496_504.append aligned504_512

def missing480_512 : List (BitVec (edgeCount 12)) :=
  missing480_496 ++ missing496_512
abbrev records480_512 : List Blob :=
  records480_496 ++ records496_512
theorem aligned480_512 :
    AlignedValid 12 2 missing480_512 records480_512 :=
  aligned480_496.append aligned496_512

def missing448_512 : List (BitVec (edgeCount 12)) :=
  missing448_480 ++ missing480_512
abbrev records448_512 : List Blob :=
  records448_480 ++ records480_512
theorem aligned448_512 :
    AlignedValid 12 2 missing448_512 records448_512 :=
  aligned448_480.append aligned480_512

def missing384_512 : List (BitVec (edgeCount 12)) :=
  missing384_448 ++ missing448_512
abbrev records384_512 : List Blob :=
  records384_448 ++ records448_512
theorem aligned384_512 :
    AlignedValid 12 2 missing384_512 records384_512 :=
  aligned384_448.append aligned448_512

abbrev missing : List (BitVec (edgeCount 12)) := missing384_512
abbrev records : List Blob := records384_512
theorem aligned : AlignedValid 12 2 missing records := aligned384_512

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A2AlignedShard003
