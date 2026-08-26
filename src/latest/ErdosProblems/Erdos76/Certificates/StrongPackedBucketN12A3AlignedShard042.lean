/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A3Shard042

/-! Decode-only alignment checks for n=12, a=3, records 5376--5503. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard042

open PackedBucketCertificate

def missing5376 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51990398798712012800
theorem maskCheck5376 :
    checkMaskFor missing5376 StrongPackedBucketN12A3Shard042.record5376 = true := by
  decide

def missing5377 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2274353271611064320
theorem maskCheck5377 :
    checkMaskFor missing5377 StrongPackedBucketN12A3Shard042.record5377 = true := by
  decide

def missing5378 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4436081092748902400
theorem maskCheck5378 :
    checkMaskFor missing5378 StrongPackedBucketN12A3Shard042.record5378 = true := by
  decide

def missing5379 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4544167483805794304
theorem maskCheck5379 :
    checkMaskFor missing5379 StrongPackedBucketN12A3Shard042.record5379 = true := by
  decide

def missing5380 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5733117785431605248
theorem maskCheck5380 :
    checkMaskFor missing5380 StrongPackedBucketN12A3Shard042.record5380 = true := by
  decide

def missing5381 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6741924101962596352
theorem maskCheck5381 :
    checkMaskFor missing5381 StrongPackedBucketN12A3Shard042.record5381 = true := by
  decide

def missing5382 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8975709517138362368
theorem maskCheck5382 :
    checkMaskFor missing5382 StrongPackedBucketN12A3Shard042.record5382 = true := by
  decide

def missing5383 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10344803803858993152
theorem maskCheck5383 :
    checkMaskFor missing5383 StrongPackedBucketN12A3Shard042.record5383 = true := by
  decide

def missing5384 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11353610120389984256
theorem maskCheck5384 :
    checkMaskFor missing5384 StrongPackedBucketN12A3Shard042.record5384 = true := by
  decide

def missing5385 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11461696511446876160
theorem maskCheck5385 :
    checkMaskFor missing5385 StrongPackedBucketN12A3Shard042.record5385 = true := by
  decide

def missing5386 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13623424332584714240
theorem maskCheck5386 :
    checkMaskFor missing5386 StrongPackedBucketN12A3Shard042.record5386 = true := by
  decide

def missing5387 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14380029069982957568
theorem maskCheck5387 :
    checkMaskFor missing5387 StrongPackedBucketN12A3Shard042.record5387 = true := by
  decide

def missing5388 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14812374634210525184
theorem maskCheck5388 :
    checkMaskFor missing5388 StrongPackedBucketN12A3Shard042.record5388 = true := by
  decide

def missing5389 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28215087125265121280
theorem maskCheck5389 :
    checkMaskFor missing5389 StrongPackedBucketN12A3Shard042.record5389 = true := by
  decide

def missing5390 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28755519080549580800
theorem maskCheck5390 :
    checkMaskFor missing5390 StrongPackedBucketN12A3Shard042.record5390 = true := by
  decide

def missing5391 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32538542767540797440
theorem maskCheck5391 :
    checkMaskFor missing5391 StrongPackedBucketN12A3Shard042.record5391 = true := by
  decide

def missing5392 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42050145180547284992
theorem maskCheck5392 :
    checkMaskFor missing5392 StrongPackedBucketN12A3Shard042.record5392 = true := by
  decide

def missing5393 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42482490744774852608
theorem maskCheck5393 :
    checkMaskFor missing5393 StrongPackedBucketN12A3Shard042.record5393 = true := by
  decide

def missing5394 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43563354655343771648
theorem maskCheck5394 :
    checkMaskFor missing5394 StrongPackedBucketN12A3Shard042.record5394 = true := by
  decide

def missing5395 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50985286841250349056
theorem maskCheck5395 :
    checkMaskFor missing5395 StrongPackedBucketN12A3Shard042.record5395 = true := by
  decide

def missing5396 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51129402029326204928
theorem maskCheck5396 :
    checkMaskFor missing5396 StrongPackedBucketN12A3Shard042.record5396 = true := by
  decide

def missing5397 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117139273609379840
theorem maskCheck5397 :
    checkMaskFor missing5397 StrongPackedBucketN12A3Shard042.record5397 = true := by
  decide

def missing5398 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2125945590140370944
theorem maskCheck5398 :
    checkMaskFor missing5398 StrongPackedBucketN12A3Shard042.record5398 = true := by
  decide

def missing5399 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4359731005316136960
theorem maskCheck5399 :
    checkMaskFor missing5399 StrongPackedBucketN12A3Shard042.record5399 = true := by
  decide

def missing5400 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5152364539733344256
theorem maskCheck5400 :
    checkMaskFor missing5400 StrongPackedBucketN12A3Shard042.record5400 = true := by
  decide

def missing5401 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5584710103960911872
theorem maskCheck5401 :
    checkMaskFor missing5401 StrongPackedBucketN12A3Shard042.record5401 = true := by
  decide

def missing5402 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5692796495017803776
theorem maskCheck5402 :
    checkMaskFor missing5402 StrongPackedBucketN12A3Shard042.record5402 = true := by
  decide

def missing5403 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6665574014529830912
theorem maskCheck5403 :
    checkMaskFor missing5403 StrongPackedBucketN12A3Shard042.record5403 = true := by
  decide

def missing5404 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6701602811548794880
theorem maskCheck5404 :
    checkMaskFor missing5404 StrongPackedBucketN12A3Shard042.record5404 = true := by
  decide

def missing5405 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8935388226724560896
theorem maskCheck5405 :
    checkMaskFor missing5405 StrongPackedBucketN12A3Shard042.record5405 = true := by
  decide

def missing5406 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14087506200436408320
theorem maskCheck5406 :
    checkMaskFor missing5406 StrongPackedBucketN12A3Shard042.record5406 = true := by
  decide

def missing5407 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14231621388512264192
theorem maskCheck5407 :
    checkMaskFor missing5407 StrongPackedBucketN12A3Shard042.record5407 = true := by
  decide

def missing5408 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14303678982550192128
theorem maskCheck5408 :
    checkMaskFor missing5408 StrongPackedBucketN12A3Shard042.record5408 = true := by
  decide

def missing5409 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14736024546777759744
theorem maskCheck5409 :
    checkMaskFor missing5409 StrongPackedBucketN12A3Shard042.record5409 = true := by
  decide

def missing5410 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14844110937834651648
theorem maskCheck5410 :
    checkMaskFor missing5410 StrongPackedBucketN12A3Shard042.record5410 = true := by
  decide

def missing5411 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15852917254365642752
theorem maskCheck5411 :
    checkMaskFor missing5411 StrongPackedBucketN12A3Shard042.record5411 = true := by
  decide

def missing5412 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32390135086070104064
theorem maskCheck5412 :
    checkMaskFor missing5412 StrongPackedBucketN12A3Shard042.record5412 = true := by
  decide

def missing5413 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32606307868183887872
theorem maskCheck5413 :
    checkMaskFor missing5413 StrongPackedBucketN12A3Shard042.record5413 = true := by
  decide

def missing5414 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 33146739823468347392
theorem maskCheck5414 :
    checkMaskFor missing5414 StrongPackedBucketN12A3Shard042.record5414 = true := by
  decide

def missing5415 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37434166668725059584
theorem maskCheck5415 :
    checkMaskFor missing5415 StrongPackedBucketN12A3Shard042.record5415 = true := by
  decide

def missing5416 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37866512232952627200
theorem maskCheck5416 :
    checkMaskFor missing5416 StrongPackedBucketN12A3Shard042.record5416 = true := by
  decide

def missing5417 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38947376143521546240
theorem maskCheck5417 :
    checkMaskFor missing5417 StrongPackedBucketN12A3Shard042.record5417 = true := by
  decide

def missing5418 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41217190355716276224
theorem maskCheck5418 :
    checkMaskFor missing5418 StrongPackedBucketN12A3Shard042.record5418 = true := by
  decide

def missing5419 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41757622311000735744
theorem maskCheck5419 :
    checkMaskFor missing5419 StrongPackedBucketN12A3Shard042.record5419 = true := by
  decide

def missing5420 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41901737499076591616
theorem maskCheck5420 :
    checkMaskFor missing5420 StrongPackedBucketN12A3Shard042.record5420 = true := by
  decide

def missing5421 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42009823890133483520
theorem maskCheck5421 :
    checkMaskFor missing5421 StrongPackedBucketN12A3Shard042.record5421 = true := by
  decide

def missing5422 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42406140657342087168
theorem maskCheck5422 :
    checkMaskFor missing5422 StrongPackedBucketN12A3Shard042.record5422 = true := by
  decide

def missing5423 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42442169454361051136
theorem maskCheck5423 :
    checkMaskFor missing5423 StrongPackedBucketN12A3Shard042.record5423 = true := by
  decide

def missing5424 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43523033364929970176
theorem maskCheck5424 :
    checkMaskFor missing5424 StrongPackedBucketN12A3Shard042.record5424 = true := by
  decide

def missing5425 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50836879159779655680
theorem maskCheck5425 :
    checkMaskFor missing5425 StrongPackedBucketN12A3Shard042.record5425 = true := by
  decide

def missing5426 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50908936753817583616
theorem maskCheck5426 :
    checkMaskFor missing5426 StrongPackedBucketN12A3Shard042.record5426 = true := by
  decide

def missing5427 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51053051941893439488
theorem maskCheck5427 :
    checkMaskFor missing5427 StrongPackedBucketN12A3Shard042.record5427 = true := by
  decide

def missing5428 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51161138332950331392
theorem maskCheck5428 :
    checkMaskFor missing5428 StrongPackedBucketN12A3Shard042.record5428 = true := by
  decide

def missing5429 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51593483897177899008
theorem maskCheck5429 :
    checkMaskFor missing5429 StrongPackedBucketN12A3Shard042.record5429 = true := by
  decide

def missing5430 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 69211565639451279360
theorem maskCheck5430 :
    checkMaskFor missing5430 StrongPackedBucketN12A3Shard042.record5430 = true := by
  decide

def missing5431 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 69463767218584027136
theorem maskCheck5431 :
    checkMaskFor missing5431 StrongPackedBucketN12A3Shard042.record5431 = true := by
  decide

def missing5432 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117280011097735168
theorem maskCheck5432 :
    checkMaskFor missing5432 StrongPackedBucketN12A3Shard042.record5432 = true := by
  decide

def missing5433 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1981971139552870400
theorem maskCheck5433 :
    checkMaskFor missing5433 StrongPackedBucketN12A3Shard042.record5433 = true := by
  decide

def missing5434 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2126086327628726272
theorem maskCheck5434 :
    checkMaskFor missing5434 StrongPackedBucketN12A3Shard042.record5434 = true := by
  decide

def missing5435 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2198143921666654208
theorem maskCheck5435 :
    checkMaskFor missing5435 StrongPackedBucketN12A3Shard042.record5435 = true := by
  decide

def missing5436 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4143698960690708480
theorem maskCheck5436 :
    checkMaskFor missing5436 StrongPackedBucketN12A3Shard042.record5436 = true := by
  decide

def missing5437 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4215756554728636416
theorem maskCheck5437 :
    checkMaskFor missing5437 StrongPackedBucketN12A3Shard042.record5437 = true := by
  decide

def missing5438 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4359871742804492288
theorem maskCheck5438 :
    checkMaskFor missing5438 StrongPackedBucketN12A3Shard042.record5438 = true := by
  decide

def missing5439 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4467958133861384192
theorem maskCheck5439 :
    checkMaskFor missing5439 StrongPackedBucketN12A3Shard042.record5439 = true := by
  decide

def missing5440 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5152505277221699584
theorem maskCheck5440 :
    checkMaskFor missing5440 StrongPackedBucketN12A3Shard042.record5440 = true := by
  decide

def missing5441 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5440735653373411328
theorem maskCheck5441 :
    checkMaskFor missing5441 StrongPackedBucketN12A3Shard042.record5441 = true := by
  decide

def missing5442 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5584850841449267200
theorem maskCheck5442 :
    checkMaskFor missing5442 StrongPackedBucketN12A3Shard042.record5442 = true := by
  decide

def missing5443 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5656908435487195136
theorem maskCheck5443 :
    checkMaskFor missing5443 StrongPackedBucketN12A3Shard042.record5443 = true := by
  decide

def missing5444 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5692937232506159104
theorem maskCheck5444 :
    checkMaskFor missing5444 StrongPackedBucketN12A3Shard042.record5444 = true := by
  decide

def missing5445 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6449541969904402432
theorem maskCheck5445 :
    checkMaskFor missing5445 StrongPackedBucketN12A3Shard042.record5445 = true := by
  decide

def missing5446 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6521599563942330368
theorem maskCheck5446 :
    checkMaskFor missing5446 StrongPackedBucketN12A3Shard042.record5446 = true := by
  decide

def missing5447 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6557628360961294336
theorem maskCheck5447 :
    checkMaskFor missing5447 StrongPackedBucketN12A3Shard042.record5447 = true := by
  decide

def missing5448 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6665714752018186240
theorem maskCheck5448 :
    checkMaskFor missing5448 StrongPackedBucketN12A3Shard042.record5448 = true := by
  decide

def missing5449 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6701743549037150208
theorem maskCheck5449 :
    checkMaskFor missing5449 StrongPackedBucketN12A3Shard042.record5449 = true := by
  decide

def missing5450 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6773801143075078144
theorem maskCheck5450 :
    checkMaskFor missing5450 StrongPackedBucketN12A3Shard042.record5450 = true := by
  decide

def missing5451 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8683327385080168448
theorem maskCheck5451 :
    checkMaskFor missing5451 StrongPackedBucketN12A3Shard042.record5451 = true := by
  decide

def missing5452 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8719356182099132416
theorem maskCheck5452 :
    checkMaskFor missing5452 StrongPackedBucketN12A3Shard042.record5452 = true := by
  decide

def missing5453 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8791413776137060352
theorem maskCheck5453 :
    checkMaskFor missing5453 StrongPackedBucketN12A3Shard042.record5453 = true := by
  decide

def missing5454 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8935528964212916224
theorem maskCheck5454 :
    checkMaskFor missing5454 StrongPackedBucketN12A3Shard042.record5454 = true := by
  decide

def missing5455 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14087646937924763648
theorem maskCheck5455 :
    checkMaskFor missing5455 StrongPackedBucketN12A3Shard042.record5455 = true := by
  decide

def missing5456 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14231762126000619520
theorem maskCheck5456 :
    checkMaskFor missing5456 StrongPackedBucketN12A3Shard042.record5456 = true := by
  decide

def missing5457 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14303819720038547456
theorem maskCheck5457 :
    checkMaskFor missing5457 StrongPackedBucketN12A3Shard042.record5457 = true := by
  decide

def missing5458 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14519992502152331264
theorem maskCheck5458 :
    checkMaskFor missing5458 StrongPackedBucketN12A3Shard042.record5458 = true := by
  decide

def missing5459 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14592050096190259200
theorem maskCheck5459 :
    checkMaskFor missing5459 StrongPackedBucketN12A3Shard042.record5459 = true := by
  decide

def missing5460 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14736165284266115072
theorem maskCheck5460 :
    checkMaskFor missing5460 StrongPackedBucketN12A3Shard042.record5460 = true := by
  decide

def missing5461 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14844251675323006976
theorem maskCheck5461 :
    checkMaskFor missing5461 StrongPackedBucketN12A3Shard042.record5461 = true := by
  decide

def missing5462 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15600856412721250304
theorem maskCheck5462 :
    checkMaskFor missing5462 StrongPackedBucketN12A3Shard042.record5462 = true := by
  decide

def missing5463 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15708942803778142208
theorem maskCheck5463 :
    checkMaskFor missing5463 StrongPackedBucketN12A3Shard042.record5463 = true := by
  decide

def missing5464 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15853057991853998080
theorem maskCheck5464 :
    checkMaskFor missing5464 StrongPackedBucketN12A3Shard042.record5464 = true := by
  decide

def missing5465 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17870670624915980288
theorem maskCheck5465 :
    checkMaskFor missing5465 StrongPackedBucketN12A3Shard042.record5465 = true := by
  decide

def missing5466 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18987563332503863296
theorem maskCheck5466 :
    checkMaskFor missing5466 StrongPackedBucketN12A3Shard042.record5466 = true := by
  decide

def missing5467 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19275793708655575040
theorem maskCheck5467 :
    checkMaskFor missing5467 StrongPackedBucketN12A3Shard042.record5467 = true := by
  decide

def missing5468 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19491966490769358848
theorem maskCheck5468 :
    checkMaskFor missing5468 StrongPackedBucketN12A3Shard042.record5468 = true := by
  decide

def missing5469 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20356657619224494080
theorem maskCheck5469 :
    checkMaskFor missing5469 StrongPackedBucketN12A3Shard042.record5469 = true := by
  decide

def missing5470 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20608859198357241856
theorem maskCheck5470 :
    checkMaskFor missing5470 StrongPackedBucketN12A3Shard042.record5470 = true := by
  decide

def missing5471 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22626471831419224064
theorem maskCheck5471 :
    checkMaskFor missing5471 StrongPackedBucketN12A3Shard042.record5471 = true := by
  decide

def missing5472 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23311018974779539456
theorem maskCheck5472 :
    checkMaskFor missing5472 StrongPackedBucketN12A3Shard042.record5472 = true := by
  decide

def missing5473 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23527191756893323264
theorem maskCheck5473 :
    checkMaskFor missing5473 StrongPackedBucketN12A3Shard042.record5473 = true := by
  decide

def missing5474 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23563220553912287232
theorem maskCheck5474 :
    checkMaskFor missing5474 StrongPackedBucketN12A3Shard042.record5474 = true := by
  decide

def missing5475 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23815422133045035008
theorem maskCheck5475 :
    checkMaskFor missing5475 StrongPackedBucketN12A3Shard042.record5475 = true := by
  decide

def missing5476 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23851450930063998976
theorem maskCheck5476 :
    checkMaskFor missing5476 StrongPackedBucketN12A3Shard042.record5476 = true := by
  decide

def missing5477 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24067623712177782784
theorem maskCheck5477 :
    checkMaskFor missing5477 StrongPackedBucketN12A3Shard042.record5477 = true := by
  decide

def missing5478 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24932314840632918016
theorem maskCheck5478 :
    checkMaskFor missing5478 StrongPackedBucketN12A3Shard042.record5478 = true := by
  decide

def missing5479 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32462333417596387328
theorem maskCheck5479 :
    checkMaskFor missing5479 StrongPackedBucketN12A3Shard042.record5479 = true := by
  decide

def missing5480 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32714534996729135104
theorem maskCheck5480 :
    checkMaskFor missing5480 StrongPackedBucketN12A3Shard042.record5480 = true := by
  decide

def missing5481 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 33002765372880846848
theorem maskCheck5481 :
    checkMaskFor missing5481 StrongPackedBucketN12A3Shard042.record5481 = true := by
  decide

def missing5482 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37434307406213414912
theorem maskCheck5482 :
    checkMaskFor missing5482 StrongPackedBucketN12A3Shard042.record5482 = true := by
  decide

def missing5483 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37722537782365126656
theorem maskCheck5483 :
    checkMaskFor missing5483 StrongPackedBucketN12A3Shard042.record5483 = true := by
  decide

def missing5484 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37866652970440982528
theorem maskCheck5484 :
    checkMaskFor missing5484 StrongPackedBucketN12A3Shard042.record5484 = true := by
  decide

def missing5485 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37938710564478910464
theorem maskCheck5485 :
    checkMaskFor missing5485 StrongPackedBucketN12A3Shard042.record5485 = true := by
  decide

def missing5486 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38731344098896117760
theorem maskCheck5486 :
    checkMaskFor missing5486 StrongPackedBucketN12A3Shard042.record5486 = true := by
  decide

def missing5487 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38803401692934045696
theorem maskCheck5487 :
    checkMaskFor missing5487 StrongPackedBucketN12A3Shard042.record5487 = true := by
  decide

def missing5488 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38947516881009901568
theorem maskCheck5488 :
    checkMaskFor missing5488 StrongPackedBucketN12A3Shard042.record5488 = true := by
  decide

def missing5489 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39055603272066793472
theorem maskCheck5489 :
    checkMaskFor missing5489 StrongPackedBucketN12A3Shard042.record5489 = true := by
  decide

def missing5490 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40965129514071883776
theorem maskCheck5490 :
    checkMaskFor missing5490 StrongPackedBucketN12A3Shard042.record5490 = true := by
  decide

def missing5491 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41073215905128775680
theorem maskCheck5491 :
    checkMaskFor missing5491 StrongPackedBucketN12A3Shard042.record5491 = true := by
  decide

def missing5492 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41217331093204631552
theorem maskCheck5492 :
    checkMaskFor missing5492 StrongPackedBucketN12A3Shard042.record5492 = true := by
  decide

def missing5493 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41757763048489091072
theorem maskCheck5493 :
    checkMaskFor missing5493 StrongPackedBucketN12A3Shard042.record5493 = true := by
  decide

def missing5494 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41901878236564946944
theorem maskCheck5494 :
    checkMaskFor missing5494 StrongPackedBucketN12A3Shard042.record5494 = true := by
  decide

def missing5495 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41973935830602874880
theorem maskCheck5495 :
    checkMaskFor missing5495 StrongPackedBucketN12A3Shard042.record5495 = true := by
  decide

def missing5496 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42009964627621838848
theorem maskCheck5496 :
    checkMaskFor missing5496 StrongPackedBucketN12A3Shard042.record5496 = true := by
  decide

def missing5497 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42190108612716658688
theorem maskCheck5497 :
    checkMaskFor missing5497 StrongPackedBucketN12A3Shard042.record5497 = true := by
  decide

def missing5498 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42262166206754586624
theorem maskCheck5498 :
    checkMaskFor missing5498 StrongPackedBucketN12A3Shard042.record5498 = true := by
  decide

def missing5499 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42298195003773550592
theorem maskCheck5499 :
    checkMaskFor missing5499 StrongPackedBucketN12A3Shard042.record5499 = true := by
  decide

def missing5500 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42406281394830442496
theorem maskCheck5500 :
    checkMaskFor missing5500 StrongPackedBucketN12A3Shard042.record5500 = true := by
  decide

def missing5501 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42442310191849406464
theorem maskCheck5501 :
    checkMaskFor missing5501 StrongPackedBucketN12A3Shard042.record5501 = true := by
  decide

def missing5502 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42514367785887334400
theorem maskCheck5502 :
    checkMaskFor missing5502 StrongPackedBucketN12A3Shard042.record5502 = true := by
  decide

def missing5503 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43270972523285577728
theorem maskCheck5503 :
    checkMaskFor missing5503 StrongPackedBucketN12A3Shard042.record5503 = true := by
  decide

def missing5376_5377 : List (BitVec (edgeCount 12)) :=
  [missing5376]
abbrev records5376_5377 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5376]
theorem aligned5376_5377 :
    AlignedValid 12 3 missing5376_5377 records5376_5377 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5376
    maskCheck5376 AlignedValid.nil

def missing5377_5378 : List (BitVec (edgeCount 12)) :=
  [missing5377]
abbrev records5377_5378 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5377]
theorem aligned5377_5378 :
    AlignedValid 12 3 missing5377_5378 records5377_5378 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5377
    maskCheck5377 AlignedValid.nil

def missing5376_5378 : List (BitVec (edgeCount 12)) :=
  missing5376_5377 ++ missing5377_5378
abbrev records5376_5378 : List Blob :=
  records5376_5377 ++ records5377_5378
theorem aligned5376_5378 :
    AlignedValid 12 3 missing5376_5378 records5376_5378 :=
  aligned5376_5377.append aligned5377_5378

def missing5378_5379 : List (BitVec (edgeCount 12)) :=
  [missing5378]
abbrev records5378_5379 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5378]
theorem aligned5378_5379 :
    AlignedValid 12 3 missing5378_5379 records5378_5379 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5378
    maskCheck5378 AlignedValid.nil

def missing5379_5380 : List (BitVec (edgeCount 12)) :=
  [missing5379]
abbrev records5379_5380 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5379]
theorem aligned5379_5380 :
    AlignedValid 12 3 missing5379_5380 records5379_5380 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5379
    maskCheck5379 AlignedValid.nil

def missing5378_5380 : List (BitVec (edgeCount 12)) :=
  missing5378_5379 ++ missing5379_5380
abbrev records5378_5380 : List Blob :=
  records5378_5379 ++ records5379_5380
theorem aligned5378_5380 :
    AlignedValid 12 3 missing5378_5380 records5378_5380 :=
  aligned5378_5379.append aligned5379_5380

def missing5376_5380 : List (BitVec (edgeCount 12)) :=
  missing5376_5378 ++ missing5378_5380
abbrev records5376_5380 : List Blob :=
  records5376_5378 ++ records5378_5380
theorem aligned5376_5380 :
    AlignedValid 12 3 missing5376_5380 records5376_5380 :=
  aligned5376_5378.append aligned5378_5380

def missing5380_5381 : List (BitVec (edgeCount 12)) :=
  [missing5380]
abbrev records5380_5381 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5380]
theorem aligned5380_5381 :
    AlignedValid 12 3 missing5380_5381 records5380_5381 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5380
    maskCheck5380 AlignedValid.nil

def missing5381_5382 : List (BitVec (edgeCount 12)) :=
  [missing5381]
abbrev records5381_5382 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5381]
theorem aligned5381_5382 :
    AlignedValid 12 3 missing5381_5382 records5381_5382 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5381
    maskCheck5381 AlignedValid.nil

def missing5380_5382 : List (BitVec (edgeCount 12)) :=
  missing5380_5381 ++ missing5381_5382
abbrev records5380_5382 : List Blob :=
  records5380_5381 ++ records5381_5382
theorem aligned5380_5382 :
    AlignedValid 12 3 missing5380_5382 records5380_5382 :=
  aligned5380_5381.append aligned5381_5382

def missing5382_5383 : List (BitVec (edgeCount 12)) :=
  [missing5382]
abbrev records5382_5383 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5382]
theorem aligned5382_5383 :
    AlignedValid 12 3 missing5382_5383 records5382_5383 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5382
    maskCheck5382 AlignedValid.nil

def missing5383_5384 : List (BitVec (edgeCount 12)) :=
  [missing5383]
abbrev records5383_5384 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5383]
theorem aligned5383_5384 :
    AlignedValid 12 3 missing5383_5384 records5383_5384 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5383
    maskCheck5383 AlignedValid.nil

def missing5382_5384 : List (BitVec (edgeCount 12)) :=
  missing5382_5383 ++ missing5383_5384
abbrev records5382_5384 : List Blob :=
  records5382_5383 ++ records5383_5384
theorem aligned5382_5384 :
    AlignedValid 12 3 missing5382_5384 records5382_5384 :=
  aligned5382_5383.append aligned5383_5384

def missing5380_5384 : List (BitVec (edgeCount 12)) :=
  missing5380_5382 ++ missing5382_5384
abbrev records5380_5384 : List Blob :=
  records5380_5382 ++ records5382_5384
theorem aligned5380_5384 :
    AlignedValid 12 3 missing5380_5384 records5380_5384 :=
  aligned5380_5382.append aligned5382_5384

def missing5376_5384 : List (BitVec (edgeCount 12)) :=
  missing5376_5380 ++ missing5380_5384
abbrev records5376_5384 : List Blob :=
  records5376_5380 ++ records5380_5384
theorem aligned5376_5384 :
    AlignedValid 12 3 missing5376_5384 records5376_5384 :=
  aligned5376_5380.append aligned5380_5384

def missing5384_5385 : List (BitVec (edgeCount 12)) :=
  [missing5384]
abbrev records5384_5385 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5384]
theorem aligned5384_5385 :
    AlignedValid 12 3 missing5384_5385 records5384_5385 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5384
    maskCheck5384 AlignedValid.nil

def missing5385_5386 : List (BitVec (edgeCount 12)) :=
  [missing5385]
abbrev records5385_5386 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5385]
theorem aligned5385_5386 :
    AlignedValid 12 3 missing5385_5386 records5385_5386 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5385
    maskCheck5385 AlignedValid.nil

def missing5384_5386 : List (BitVec (edgeCount 12)) :=
  missing5384_5385 ++ missing5385_5386
abbrev records5384_5386 : List Blob :=
  records5384_5385 ++ records5385_5386
theorem aligned5384_5386 :
    AlignedValid 12 3 missing5384_5386 records5384_5386 :=
  aligned5384_5385.append aligned5385_5386

def missing5386_5387 : List (BitVec (edgeCount 12)) :=
  [missing5386]
abbrev records5386_5387 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5386]
theorem aligned5386_5387 :
    AlignedValid 12 3 missing5386_5387 records5386_5387 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5386
    maskCheck5386 AlignedValid.nil

def missing5387_5388 : List (BitVec (edgeCount 12)) :=
  [missing5387]
abbrev records5387_5388 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5387]
theorem aligned5387_5388 :
    AlignedValid 12 3 missing5387_5388 records5387_5388 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5387
    maskCheck5387 AlignedValid.nil

def missing5386_5388 : List (BitVec (edgeCount 12)) :=
  missing5386_5387 ++ missing5387_5388
abbrev records5386_5388 : List Blob :=
  records5386_5387 ++ records5387_5388
theorem aligned5386_5388 :
    AlignedValid 12 3 missing5386_5388 records5386_5388 :=
  aligned5386_5387.append aligned5387_5388

def missing5384_5388 : List (BitVec (edgeCount 12)) :=
  missing5384_5386 ++ missing5386_5388
abbrev records5384_5388 : List Blob :=
  records5384_5386 ++ records5386_5388
theorem aligned5384_5388 :
    AlignedValid 12 3 missing5384_5388 records5384_5388 :=
  aligned5384_5386.append aligned5386_5388

def missing5388_5389 : List (BitVec (edgeCount 12)) :=
  [missing5388]
abbrev records5388_5389 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5388]
theorem aligned5388_5389 :
    AlignedValid 12 3 missing5388_5389 records5388_5389 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5388
    maskCheck5388 AlignedValid.nil

def missing5389_5390 : List (BitVec (edgeCount 12)) :=
  [missing5389]
abbrev records5389_5390 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5389]
theorem aligned5389_5390 :
    AlignedValid 12 3 missing5389_5390 records5389_5390 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5389
    maskCheck5389 AlignedValid.nil

def missing5388_5390 : List (BitVec (edgeCount 12)) :=
  missing5388_5389 ++ missing5389_5390
abbrev records5388_5390 : List Blob :=
  records5388_5389 ++ records5389_5390
theorem aligned5388_5390 :
    AlignedValid 12 3 missing5388_5390 records5388_5390 :=
  aligned5388_5389.append aligned5389_5390

def missing5390_5391 : List (BitVec (edgeCount 12)) :=
  [missing5390]
abbrev records5390_5391 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5390]
theorem aligned5390_5391 :
    AlignedValid 12 3 missing5390_5391 records5390_5391 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5390
    maskCheck5390 AlignedValid.nil

def missing5391_5392 : List (BitVec (edgeCount 12)) :=
  [missing5391]
abbrev records5391_5392 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5391]
theorem aligned5391_5392 :
    AlignedValid 12 3 missing5391_5392 records5391_5392 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5391
    maskCheck5391 AlignedValid.nil

def missing5390_5392 : List (BitVec (edgeCount 12)) :=
  missing5390_5391 ++ missing5391_5392
abbrev records5390_5392 : List Blob :=
  records5390_5391 ++ records5391_5392
theorem aligned5390_5392 :
    AlignedValid 12 3 missing5390_5392 records5390_5392 :=
  aligned5390_5391.append aligned5391_5392

def missing5388_5392 : List (BitVec (edgeCount 12)) :=
  missing5388_5390 ++ missing5390_5392
abbrev records5388_5392 : List Blob :=
  records5388_5390 ++ records5390_5392
theorem aligned5388_5392 :
    AlignedValid 12 3 missing5388_5392 records5388_5392 :=
  aligned5388_5390.append aligned5390_5392

def missing5384_5392 : List (BitVec (edgeCount 12)) :=
  missing5384_5388 ++ missing5388_5392
abbrev records5384_5392 : List Blob :=
  records5384_5388 ++ records5388_5392
theorem aligned5384_5392 :
    AlignedValid 12 3 missing5384_5392 records5384_5392 :=
  aligned5384_5388.append aligned5388_5392

def missing5376_5392 : List (BitVec (edgeCount 12)) :=
  missing5376_5384 ++ missing5384_5392
abbrev records5376_5392 : List Blob :=
  records5376_5384 ++ records5384_5392
theorem aligned5376_5392 :
    AlignedValid 12 3 missing5376_5392 records5376_5392 :=
  aligned5376_5384.append aligned5384_5392

def missing5392_5393 : List (BitVec (edgeCount 12)) :=
  [missing5392]
abbrev records5392_5393 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5392]
theorem aligned5392_5393 :
    AlignedValid 12 3 missing5392_5393 records5392_5393 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5392
    maskCheck5392 AlignedValid.nil

def missing5393_5394 : List (BitVec (edgeCount 12)) :=
  [missing5393]
abbrev records5393_5394 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5393]
theorem aligned5393_5394 :
    AlignedValid 12 3 missing5393_5394 records5393_5394 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5393
    maskCheck5393 AlignedValid.nil

def missing5392_5394 : List (BitVec (edgeCount 12)) :=
  missing5392_5393 ++ missing5393_5394
abbrev records5392_5394 : List Blob :=
  records5392_5393 ++ records5393_5394
theorem aligned5392_5394 :
    AlignedValid 12 3 missing5392_5394 records5392_5394 :=
  aligned5392_5393.append aligned5393_5394

def missing5394_5395 : List (BitVec (edgeCount 12)) :=
  [missing5394]
abbrev records5394_5395 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5394]
theorem aligned5394_5395 :
    AlignedValid 12 3 missing5394_5395 records5394_5395 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5394
    maskCheck5394 AlignedValid.nil

def missing5395_5396 : List (BitVec (edgeCount 12)) :=
  [missing5395]
abbrev records5395_5396 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5395]
theorem aligned5395_5396 :
    AlignedValid 12 3 missing5395_5396 records5395_5396 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5395
    maskCheck5395 AlignedValid.nil

def missing5394_5396 : List (BitVec (edgeCount 12)) :=
  missing5394_5395 ++ missing5395_5396
abbrev records5394_5396 : List Blob :=
  records5394_5395 ++ records5395_5396
theorem aligned5394_5396 :
    AlignedValid 12 3 missing5394_5396 records5394_5396 :=
  aligned5394_5395.append aligned5395_5396

def missing5392_5396 : List (BitVec (edgeCount 12)) :=
  missing5392_5394 ++ missing5394_5396
abbrev records5392_5396 : List Blob :=
  records5392_5394 ++ records5394_5396
theorem aligned5392_5396 :
    AlignedValid 12 3 missing5392_5396 records5392_5396 :=
  aligned5392_5394.append aligned5394_5396

def missing5396_5397 : List (BitVec (edgeCount 12)) :=
  [missing5396]
abbrev records5396_5397 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5396]
theorem aligned5396_5397 :
    AlignedValid 12 3 missing5396_5397 records5396_5397 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5396
    maskCheck5396 AlignedValid.nil

def missing5397_5398 : List (BitVec (edgeCount 12)) :=
  [missing5397]
abbrev records5397_5398 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5397]
theorem aligned5397_5398 :
    AlignedValid 12 3 missing5397_5398 records5397_5398 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5397
    maskCheck5397 AlignedValid.nil

def missing5396_5398 : List (BitVec (edgeCount 12)) :=
  missing5396_5397 ++ missing5397_5398
abbrev records5396_5398 : List Blob :=
  records5396_5397 ++ records5397_5398
theorem aligned5396_5398 :
    AlignedValid 12 3 missing5396_5398 records5396_5398 :=
  aligned5396_5397.append aligned5397_5398

def missing5398_5399 : List (BitVec (edgeCount 12)) :=
  [missing5398]
abbrev records5398_5399 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5398]
theorem aligned5398_5399 :
    AlignedValid 12 3 missing5398_5399 records5398_5399 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5398
    maskCheck5398 AlignedValid.nil

def missing5399_5400 : List (BitVec (edgeCount 12)) :=
  [missing5399]
abbrev records5399_5400 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5399]
theorem aligned5399_5400 :
    AlignedValid 12 3 missing5399_5400 records5399_5400 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5399
    maskCheck5399 AlignedValid.nil

def missing5398_5400 : List (BitVec (edgeCount 12)) :=
  missing5398_5399 ++ missing5399_5400
abbrev records5398_5400 : List Blob :=
  records5398_5399 ++ records5399_5400
theorem aligned5398_5400 :
    AlignedValid 12 3 missing5398_5400 records5398_5400 :=
  aligned5398_5399.append aligned5399_5400

def missing5396_5400 : List (BitVec (edgeCount 12)) :=
  missing5396_5398 ++ missing5398_5400
abbrev records5396_5400 : List Blob :=
  records5396_5398 ++ records5398_5400
theorem aligned5396_5400 :
    AlignedValid 12 3 missing5396_5400 records5396_5400 :=
  aligned5396_5398.append aligned5398_5400

def missing5392_5400 : List (BitVec (edgeCount 12)) :=
  missing5392_5396 ++ missing5396_5400
abbrev records5392_5400 : List Blob :=
  records5392_5396 ++ records5396_5400
theorem aligned5392_5400 :
    AlignedValid 12 3 missing5392_5400 records5392_5400 :=
  aligned5392_5396.append aligned5396_5400

def missing5400_5401 : List (BitVec (edgeCount 12)) :=
  [missing5400]
abbrev records5400_5401 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5400]
theorem aligned5400_5401 :
    AlignedValid 12 3 missing5400_5401 records5400_5401 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5400
    maskCheck5400 AlignedValid.nil

def missing5401_5402 : List (BitVec (edgeCount 12)) :=
  [missing5401]
abbrev records5401_5402 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5401]
theorem aligned5401_5402 :
    AlignedValid 12 3 missing5401_5402 records5401_5402 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5401
    maskCheck5401 AlignedValid.nil

def missing5400_5402 : List (BitVec (edgeCount 12)) :=
  missing5400_5401 ++ missing5401_5402
abbrev records5400_5402 : List Blob :=
  records5400_5401 ++ records5401_5402
theorem aligned5400_5402 :
    AlignedValid 12 3 missing5400_5402 records5400_5402 :=
  aligned5400_5401.append aligned5401_5402

def missing5402_5403 : List (BitVec (edgeCount 12)) :=
  [missing5402]
abbrev records5402_5403 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5402]
theorem aligned5402_5403 :
    AlignedValid 12 3 missing5402_5403 records5402_5403 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5402
    maskCheck5402 AlignedValid.nil

def missing5403_5404 : List (BitVec (edgeCount 12)) :=
  [missing5403]
abbrev records5403_5404 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5403]
theorem aligned5403_5404 :
    AlignedValid 12 3 missing5403_5404 records5403_5404 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5403
    maskCheck5403 AlignedValid.nil

def missing5402_5404 : List (BitVec (edgeCount 12)) :=
  missing5402_5403 ++ missing5403_5404
abbrev records5402_5404 : List Blob :=
  records5402_5403 ++ records5403_5404
theorem aligned5402_5404 :
    AlignedValid 12 3 missing5402_5404 records5402_5404 :=
  aligned5402_5403.append aligned5403_5404

def missing5400_5404 : List (BitVec (edgeCount 12)) :=
  missing5400_5402 ++ missing5402_5404
abbrev records5400_5404 : List Blob :=
  records5400_5402 ++ records5402_5404
theorem aligned5400_5404 :
    AlignedValid 12 3 missing5400_5404 records5400_5404 :=
  aligned5400_5402.append aligned5402_5404

def missing5404_5405 : List (BitVec (edgeCount 12)) :=
  [missing5404]
abbrev records5404_5405 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5404]
theorem aligned5404_5405 :
    AlignedValid 12 3 missing5404_5405 records5404_5405 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5404
    maskCheck5404 AlignedValid.nil

def missing5405_5406 : List (BitVec (edgeCount 12)) :=
  [missing5405]
abbrev records5405_5406 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5405]
theorem aligned5405_5406 :
    AlignedValid 12 3 missing5405_5406 records5405_5406 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5405
    maskCheck5405 AlignedValid.nil

def missing5404_5406 : List (BitVec (edgeCount 12)) :=
  missing5404_5405 ++ missing5405_5406
abbrev records5404_5406 : List Blob :=
  records5404_5405 ++ records5405_5406
theorem aligned5404_5406 :
    AlignedValid 12 3 missing5404_5406 records5404_5406 :=
  aligned5404_5405.append aligned5405_5406

def missing5406_5407 : List (BitVec (edgeCount 12)) :=
  [missing5406]
abbrev records5406_5407 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5406]
theorem aligned5406_5407 :
    AlignedValid 12 3 missing5406_5407 records5406_5407 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5406
    maskCheck5406 AlignedValid.nil

def missing5407_5408 : List (BitVec (edgeCount 12)) :=
  [missing5407]
abbrev records5407_5408 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5407]
theorem aligned5407_5408 :
    AlignedValid 12 3 missing5407_5408 records5407_5408 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5407
    maskCheck5407 AlignedValid.nil

def missing5406_5408 : List (BitVec (edgeCount 12)) :=
  missing5406_5407 ++ missing5407_5408
abbrev records5406_5408 : List Blob :=
  records5406_5407 ++ records5407_5408
theorem aligned5406_5408 :
    AlignedValid 12 3 missing5406_5408 records5406_5408 :=
  aligned5406_5407.append aligned5407_5408

def missing5404_5408 : List (BitVec (edgeCount 12)) :=
  missing5404_5406 ++ missing5406_5408
abbrev records5404_5408 : List Blob :=
  records5404_5406 ++ records5406_5408
theorem aligned5404_5408 :
    AlignedValid 12 3 missing5404_5408 records5404_5408 :=
  aligned5404_5406.append aligned5406_5408

def missing5400_5408 : List (BitVec (edgeCount 12)) :=
  missing5400_5404 ++ missing5404_5408
abbrev records5400_5408 : List Blob :=
  records5400_5404 ++ records5404_5408
theorem aligned5400_5408 :
    AlignedValid 12 3 missing5400_5408 records5400_5408 :=
  aligned5400_5404.append aligned5404_5408

def missing5392_5408 : List (BitVec (edgeCount 12)) :=
  missing5392_5400 ++ missing5400_5408
abbrev records5392_5408 : List Blob :=
  records5392_5400 ++ records5400_5408
theorem aligned5392_5408 :
    AlignedValid 12 3 missing5392_5408 records5392_5408 :=
  aligned5392_5400.append aligned5400_5408

def missing5376_5408 : List (BitVec (edgeCount 12)) :=
  missing5376_5392 ++ missing5392_5408
abbrev records5376_5408 : List Blob :=
  records5376_5392 ++ records5392_5408
theorem aligned5376_5408 :
    AlignedValid 12 3 missing5376_5408 records5376_5408 :=
  aligned5376_5392.append aligned5392_5408

def missing5408_5409 : List (BitVec (edgeCount 12)) :=
  [missing5408]
abbrev records5408_5409 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5408]
theorem aligned5408_5409 :
    AlignedValid 12 3 missing5408_5409 records5408_5409 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5408
    maskCheck5408 AlignedValid.nil

def missing5409_5410 : List (BitVec (edgeCount 12)) :=
  [missing5409]
abbrev records5409_5410 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5409]
theorem aligned5409_5410 :
    AlignedValid 12 3 missing5409_5410 records5409_5410 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5409
    maskCheck5409 AlignedValid.nil

def missing5408_5410 : List (BitVec (edgeCount 12)) :=
  missing5408_5409 ++ missing5409_5410
abbrev records5408_5410 : List Blob :=
  records5408_5409 ++ records5409_5410
theorem aligned5408_5410 :
    AlignedValid 12 3 missing5408_5410 records5408_5410 :=
  aligned5408_5409.append aligned5409_5410

def missing5410_5411 : List (BitVec (edgeCount 12)) :=
  [missing5410]
abbrev records5410_5411 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5410]
theorem aligned5410_5411 :
    AlignedValid 12 3 missing5410_5411 records5410_5411 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5410
    maskCheck5410 AlignedValid.nil

def missing5411_5412 : List (BitVec (edgeCount 12)) :=
  [missing5411]
abbrev records5411_5412 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5411]
theorem aligned5411_5412 :
    AlignedValid 12 3 missing5411_5412 records5411_5412 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5411
    maskCheck5411 AlignedValid.nil

def missing5410_5412 : List (BitVec (edgeCount 12)) :=
  missing5410_5411 ++ missing5411_5412
abbrev records5410_5412 : List Blob :=
  records5410_5411 ++ records5411_5412
theorem aligned5410_5412 :
    AlignedValid 12 3 missing5410_5412 records5410_5412 :=
  aligned5410_5411.append aligned5411_5412

def missing5408_5412 : List (BitVec (edgeCount 12)) :=
  missing5408_5410 ++ missing5410_5412
abbrev records5408_5412 : List Blob :=
  records5408_5410 ++ records5410_5412
theorem aligned5408_5412 :
    AlignedValid 12 3 missing5408_5412 records5408_5412 :=
  aligned5408_5410.append aligned5410_5412

def missing5412_5413 : List (BitVec (edgeCount 12)) :=
  [missing5412]
abbrev records5412_5413 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5412]
theorem aligned5412_5413 :
    AlignedValid 12 3 missing5412_5413 records5412_5413 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5412
    maskCheck5412 AlignedValid.nil

def missing5413_5414 : List (BitVec (edgeCount 12)) :=
  [missing5413]
abbrev records5413_5414 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5413]
theorem aligned5413_5414 :
    AlignedValid 12 3 missing5413_5414 records5413_5414 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5413
    maskCheck5413 AlignedValid.nil

def missing5412_5414 : List (BitVec (edgeCount 12)) :=
  missing5412_5413 ++ missing5413_5414
abbrev records5412_5414 : List Blob :=
  records5412_5413 ++ records5413_5414
theorem aligned5412_5414 :
    AlignedValid 12 3 missing5412_5414 records5412_5414 :=
  aligned5412_5413.append aligned5413_5414

def missing5414_5415 : List (BitVec (edgeCount 12)) :=
  [missing5414]
abbrev records5414_5415 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5414]
theorem aligned5414_5415 :
    AlignedValid 12 3 missing5414_5415 records5414_5415 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5414
    maskCheck5414 AlignedValid.nil

def missing5415_5416 : List (BitVec (edgeCount 12)) :=
  [missing5415]
abbrev records5415_5416 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5415]
theorem aligned5415_5416 :
    AlignedValid 12 3 missing5415_5416 records5415_5416 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5415
    maskCheck5415 AlignedValid.nil

def missing5414_5416 : List (BitVec (edgeCount 12)) :=
  missing5414_5415 ++ missing5415_5416
abbrev records5414_5416 : List Blob :=
  records5414_5415 ++ records5415_5416
theorem aligned5414_5416 :
    AlignedValid 12 3 missing5414_5416 records5414_5416 :=
  aligned5414_5415.append aligned5415_5416

def missing5412_5416 : List (BitVec (edgeCount 12)) :=
  missing5412_5414 ++ missing5414_5416
abbrev records5412_5416 : List Blob :=
  records5412_5414 ++ records5414_5416
theorem aligned5412_5416 :
    AlignedValid 12 3 missing5412_5416 records5412_5416 :=
  aligned5412_5414.append aligned5414_5416

def missing5408_5416 : List (BitVec (edgeCount 12)) :=
  missing5408_5412 ++ missing5412_5416
abbrev records5408_5416 : List Blob :=
  records5408_5412 ++ records5412_5416
theorem aligned5408_5416 :
    AlignedValid 12 3 missing5408_5416 records5408_5416 :=
  aligned5408_5412.append aligned5412_5416

def missing5416_5417 : List (BitVec (edgeCount 12)) :=
  [missing5416]
abbrev records5416_5417 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5416]
theorem aligned5416_5417 :
    AlignedValid 12 3 missing5416_5417 records5416_5417 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5416
    maskCheck5416 AlignedValid.nil

def missing5417_5418 : List (BitVec (edgeCount 12)) :=
  [missing5417]
abbrev records5417_5418 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5417]
theorem aligned5417_5418 :
    AlignedValid 12 3 missing5417_5418 records5417_5418 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5417
    maskCheck5417 AlignedValid.nil

def missing5416_5418 : List (BitVec (edgeCount 12)) :=
  missing5416_5417 ++ missing5417_5418
abbrev records5416_5418 : List Blob :=
  records5416_5417 ++ records5417_5418
theorem aligned5416_5418 :
    AlignedValid 12 3 missing5416_5418 records5416_5418 :=
  aligned5416_5417.append aligned5417_5418

def missing5418_5419 : List (BitVec (edgeCount 12)) :=
  [missing5418]
abbrev records5418_5419 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5418]
theorem aligned5418_5419 :
    AlignedValid 12 3 missing5418_5419 records5418_5419 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5418
    maskCheck5418 AlignedValid.nil

def missing5419_5420 : List (BitVec (edgeCount 12)) :=
  [missing5419]
abbrev records5419_5420 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5419]
theorem aligned5419_5420 :
    AlignedValid 12 3 missing5419_5420 records5419_5420 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5419
    maskCheck5419 AlignedValid.nil

def missing5418_5420 : List (BitVec (edgeCount 12)) :=
  missing5418_5419 ++ missing5419_5420
abbrev records5418_5420 : List Blob :=
  records5418_5419 ++ records5419_5420
theorem aligned5418_5420 :
    AlignedValid 12 3 missing5418_5420 records5418_5420 :=
  aligned5418_5419.append aligned5419_5420

def missing5416_5420 : List (BitVec (edgeCount 12)) :=
  missing5416_5418 ++ missing5418_5420
abbrev records5416_5420 : List Blob :=
  records5416_5418 ++ records5418_5420
theorem aligned5416_5420 :
    AlignedValid 12 3 missing5416_5420 records5416_5420 :=
  aligned5416_5418.append aligned5418_5420

def missing5420_5421 : List (BitVec (edgeCount 12)) :=
  [missing5420]
abbrev records5420_5421 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5420]
theorem aligned5420_5421 :
    AlignedValid 12 3 missing5420_5421 records5420_5421 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5420
    maskCheck5420 AlignedValid.nil

def missing5421_5422 : List (BitVec (edgeCount 12)) :=
  [missing5421]
abbrev records5421_5422 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5421]
theorem aligned5421_5422 :
    AlignedValid 12 3 missing5421_5422 records5421_5422 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5421
    maskCheck5421 AlignedValid.nil

def missing5420_5422 : List (BitVec (edgeCount 12)) :=
  missing5420_5421 ++ missing5421_5422
abbrev records5420_5422 : List Blob :=
  records5420_5421 ++ records5421_5422
theorem aligned5420_5422 :
    AlignedValid 12 3 missing5420_5422 records5420_5422 :=
  aligned5420_5421.append aligned5421_5422

def missing5422_5423 : List (BitVec (edgeCount 12)) :=
  [missing5422]
abbrev records5422_5423 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5422]
theorem aligned5422_5423 :
    AlignedValid 12 3 missing5422_5423 records5422_5423 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5422
    maskCheck5422 AlignedValid.nil

def missing5423_5424 : List (BitVec (edgeCount 12)) :=
  [missing5423]
abbrev records5423_5424 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5423]
theorem aligned5423_5424 :
    AlignedValid 12 3 missing5423_5424 records5423_5424 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5423
    maskCheck5423 AlignedValid.nil

def missing5422_5424 : List (BitVec (edgeCount 12)) :=
  missing5422_5423 ++ missing5423_5424
abbrev records5422_5424 : List Blob :=
  records5422_5423 ++ records5423_5424
theorem aligned5422_5424 :
    AlignedValid 12 3 missing5422_5424 records5422_5424 :=
  aligned5422_5423.append aligned5423_5424

def missing5420_5424 : List (BitVec (edgeCount 12)) :=
  missing5420_5422 ++ missing5422_5424
abbrev records5420_5424 : List Blob :=
  records5420_5422 ++ records5422_5424
theorem aligned5420_5424 :
    AlignedValid 12 3 missing5420_5424 records5420_5424 :=
  aligned5420_5422.append aligned5422_5424

def missing5416_5424 : List (BitVec (edgeCount 12)) :=
  missing5416_5420 ++ missing5420_5424
abbrev records5416_5424 : List Blob :=
  records5416_5420 ++ records5420_5424
theorem aligned5416_5424 :
    AlignedValid 12 3 missing5416_5424 records5416_5424 :=
  aligned5416_5420.append aligned5420_5424

def missing5408_5424 : List (BitVec (edgeCount 12)) :=
  missing5408_5416 ++ missing5416_5424
abbrev records5408_5424 : List Blob :=
  records5408_5416 ++ records5416_5424
theorem aligned5408_5424 :
    AlignedValid 12 3 missing5408_5424 records5408_5424 :=
  aligned5408_5416.append aligned5416_5424

def missing5424_5425 : List (BitVec (edgeCount 12)) :=
  [missing5424]
abbrev records5424_5425 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5424]
theorem aligned5424_5425 :
    AlignedValid 12 3 missing5424_5425 records5424_5425 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5424
    maskCheck5424 AlignedValid.nil

def missing5425_5426 : List (BitVec (edgeCount 12)) :=
  [missing5425]
abbrev records5425_5426 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5425]
theorem aligned5425_5426 :
    AlignedValid 12 3 missing5425_5426 records5425_5426 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5425
    maskCheck5425 AlignedValid.nil

def missing5424_5426 : List (BitVec (edgeCount 12)) :=
  missing5424_5425 ++ missing5425_5426
abbrev records5424_5426 : List Blob :=
  records5424_5425 ++ records5425_5426
theorem aligned5424_5426 :
    AlignedValid 12 3 missing5424_5426 records5424_5426 :=
  aligned5424_5425.append aligned5425_5426

def missing5426_5427 : List (BitVec (edgeCount 12)) :=
  [missing5426]
abbrev records5426_5427 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5426]
theorem aligned5426_5427 :
    AlignedValid 12 3 missing5426_5427 records5426_5427 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5426
    maskCheck5426 AlignedValid.nil

def missing5427_5428 : List (BitVec (edgeCount 12)) :=
  [missing5427]
abbrev records5427_5428 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5427]
theorem aligned5427_5428 :
    AlignedValid 12 3 missing5427_5428 records5427_5428 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5427
    maskCheck5427 AlignedValid.nil

def missing5426_5428 : List (BitVec (edgeCount 12)) :=
  missing5426_5427 ++ missing5427_5428
abbrev records5426_5428 : List Blob :=
  records5426_5427 ++ records5427_5428
theorem aligned5426_5428 :
    AlignedValid 12 3 missing5426_5428 records5426_5428 :=
  aligned5426_5427.append aligned5427_5428

def missing5424_5428 : List (BitVec (edgeCount 12)) :=
  missing5424_5426 ++ missing5426_5428
abbrev records5424_5428 : List Blob :=
  records5424_5426 ++ records5426_5428
theorem aligned5424_5428 :
    AlignedValid 12 3 missing5424_5428 records5424_5428 :=
  aligned5424_5426.append aligned5426_5428

def missing5428_5429 : List (BitVec (edgeCount 12)) :=
  [missing5428]
abbrev records5428_5429 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5428]
theorem aligned5428_5429 :
    AlignedValid 12 3 missing5428_5429 records5428_5429 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5428
    maskCheck5428 AlignedValid.nil

def missing5429_5430 : List (BitVec (edgeCount 12)) :=
  [missing5429]
abbrev records5429_5430 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5429]
theorem aligned5429_5430 :
    AlignedValid 12 3 missing5429_5430 records5429_5430 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5429
    maskCheck5429 AlignedValid.nil

def missing5428_5430 : List (BitVec (edgeCount 12)) :=
  missing5428_5429 ++ missing5429_5430
abbrev records5428_5430 : List Blob :=
  records5428_5429 ++ records5429_5430
theorem aligned5428_5430 :
    AlignedValid 12 3 missing5428_5430 records5428_5430 :=
  aligned5428_5429.append aligned5429_5430

def missing5430_5431 : List (BitVec (edgeCount 12)) :=
  [missing5430]
abbrev records5430_5431 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5430]
theorem aligned5430_5431 :
    AlignedValid 12 3 missing5430_5431 records5430_5431 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5430
    maskCheck5430 AlignedValid.nil

def missing5431_5432 : List (BitVec (edgeCount 12)) :=
  [missing5431]
abbrev records5431_5432 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5431]
theorem aligned5431_5432 :
    AlignedValid 12 3 missing5431_5432 records5431_5432 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5431
    maskCheck5431 AlignedValid.nil

def missing5430_5432 : List (BitVec (edgeCount 12)) :=
  missing5430_5431 ++ missing5431_5432
abbrev records5430_5432 : List Blob :=
  records5430_5431 ++ records5431_5432
theorem aligned5430_5432 :
    AlignedValid 12 3 missing5430_5432 records5430_5432 :=
  aligned5430_5431.append aligned5431_5432

def missing5428_5432 : List (BitVec (edgeCount 12)) :=
  missing5428_5430 ++ missing5430_5432
abbrev records5428_5432 : List Blob :=
  records5428_5430 ++ records5430_5432
theorem aligned5428_5432 :
    AlignedValid 12 3 missing5428_5432 records5428_5432 :=
  aligned5428_5430.append aligned5430_5432

def missing5424_5432 : List (BitVec (edgeCount 12)) :=
  missing5424_5428 ++ missing5428_5432
abbrev records5424_5432 : List Blob :=
  records5424_5428 ++ records5428_5432
theorem aligned5424_5432 :
    AlignedValid 12 3 missing5424_5432 records5424_5432 :=
  aligned5424_5428.append aligned5428_5432

def missing5432_5433 : List (BitVec (edgeCount 12)) :=
  [missing5432]
abbrev records5432_5433 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5432]
theorem aligned5432_5433 :
    AlignedValid 12 3 missing5432_5433 records5432_5433 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5432
    maskCheck5432 AlignedValid.nil

def missing5433_5434 : List (BitVec (edgeCount 12)) :=
  [missing5433]
abbrev records5433_5434 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5433]
theorem aligned5433_5434 :
    AlignedValid 12 3 missing5433_5434 records5433_5434 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5433
    maskCheck5433 AlignedValid.nil

def missing5432_5434 : List (BitVec (edgeCount 12)) :=
  missing5432_5433 ++ missing5433_5434
abbrev records5432_5434 : List Blob :=
  records5432_5433 ++ records5433_5434
theorem aligned5432_5434 :
    AlignedValid 12 3 missing5432_5434 records5432_5434 :=
  aligned5432_5433.append aligned5433_5434

def missing5434_5435 : List (BitVec (edgeCount 12)) :=
  [missing5434]
abbrev records5434_5435 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5434]
theorem aligned5434_5435 :
    AlignedValid 12 3 missing5434_5435 records5434_5435 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5434
    maskCheck5434 AlignedValid.nil

def missing5435_5436 : List (BitVec (edgeCount 12)) :=
  [missing5435]
abbrev records5435_5436 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5435]
theorem aligned5435_5436 :
    AlignedValid 12 3 missing5435_5436 records5435_5436 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5435
    maskCheck5435 AlignedValid.nil

def missing5434_5436 : List (BitVec (edgeCount 12)) :=
  missing5434_5435 ++ missing5435_5436
abbrev records5434_5436 : List Blob :=
  records5434_5435 ++ records5435_5436
theorem aligned5434_5436 :
    AlignedValid 12 3 missing5434_5436 records5434_5436 :=
  aligned5434_5435.append aligned5435_5436

def missing5432_5436 : List (BitVec (edgeCount 12)) :=
  missing5432_5434 ++ missing5434_5436
abbrev records5432_5436 : List Blob :=
  records5432_5434 ++ records5434_5436
theorem aligned5432_5436 :
    AlignedValid 12 3 missing5432_5436 records5432_5436 :=
  aligned5432_5434.append aligned5434_5436

def missing5436_5437 : List (BitVec (edgeCount 12)) :=
  [missing5436]
abbrev records5436_5437 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5436]
theorem aligned5436_5437 :
    AlignedValid 12 3 missing5436_5437 records5436_5437 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5436
    maskCheck5436 AlignedValid.nil

def missing5437_5438 : List (BitVec (edgeCount 12)) :=
  [missing5437]
abbrev records5437_5438 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5437]
theorem aligned5437_5438 :
    AlignedValid 12 3 missing5437_5438 records5437_5438 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5437
    maskCheck5437 AlignedValid.nil

def missing5436_5438 : List (BitVec (edgeCount 12)) :=
  missing5436_5437 ++ missing5437_5438
abbrev records5436_5438 : List Blob :=
  records5436_5437 ++ records5437_5438
theorem aligned5436_5438 :
    AlignedValid 12 3 missing5436_5438 records5436_5438 :=
  aligned5436_5437.append aligned5437_5438

def missing5438_5439 : List (BitVec (edgeCount 12)) :=
  [missing5438]
abbrev records5438_5439 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5438]
theorem aligned5438_5439 :
    AlignedValid 12 3 missing5438_5439 records5438_5439 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5438
    maskCheck5438 AlignedValid.nil

def missing5439_5440 : List (BitVec (edgeCount 12)) :=
  [missing5439]
abbrev records5439_5440 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5439]
theorem aligned5439_5440 :
    AlignedValid 12 3 missing5439_5440 records5439_5440 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5439
    maskCheck5439 AlignedValid.nil

def missing5438_5440 : List (BitVec (edgeCount 12)) :=
  missing5438_5439 ++ missing5439_5440
abbrev records5438_5440 : List Blob :=
  records5438_5439 ++ records5439_5440
theorem aligned5438_5440 :
    AlignedValid 12 3 missing5438_5440 records5438_5440 :=
  aligned5438_5439.append aligned5439_5440

def missing5436_5440 : List (BitVec (edgeCount 12)) :=
  missing5436_5438 ++ missing5438_5440
abbrev records5436_5440 : List Blob :=
  records5436_5438 ++ records5438_5440
theorem aligned5436_5440 :
    AlignedValid 12 3 missing5436_5440 records5436_5440 :=
  aligned5436_5438.append aligned5438_5440

def missing5432_5440 : List (BitVec (edgeCount 12)) :=
  missing5432_5436 ++ missing5436_5440
abbrev records5432_5440 : List Blob :=
  records5432_5436 ++ records5436_5440
theorem aligned5432_5440 :
    AlignedValid 12 3 missing5432_5440 records5432_5440 :=
  aligned5432_5436.append aligned5436_5440

def missing5424_5440 : List (BitVec (edgeCount 12)) :=
  missing5424_5432 ++ missing5432_5440
abbrev records5424_5440 : List Blob :=
  records5424_5432 ++ records5432_5440
theorem aligned5424_5440 :
    AlignedValid 12 3 missing5424_5440 records5424_5440 :=
  aligned5424_5432.append aligned5432_5440

def missing5408_5440 : List (BitVec (edgeCount 12)) :=
  missing5408_5424 ++ missing5424_5440
abbrev records5408_5440 : List Blob :=
  records5408_5424 ++ records5424_5440
theorem aligned5408_5440 :
    AlignedValid 12 3 missing5408_5440 records5408_5440 :=
  aligned5408_5424.append aligned5424_5440

def missing5376_5440 : List (BitVec (edgeCount 12)) :=
  missing5376_5408 ++ missing5408_5440
abbrev records5376_5440 : List Blob :=
  records5376_5408 ++ records5408_5440
theorem aligned5376_5440 :
    AlignedValid 12 3 missing5376_5440 records5376_5440 :=
  aligned5376_5408.append aligned5408_5440

def missing5440_5441 : List (BitVec (edgeCount 12)) :=
  [missing5440]
abbrev records5440_5441 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5440]
theorem aligned5440_5441 :
    AlignedValid 12 3 missing5440_5441 records5440_5441 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5440
    maskCheck5440 AlignedValid.nil

def missing5441_5442 : List (BitVec (edgeCount 12)) :=
  [missing5441]
abbrev records5441_5442 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5441]
theorem aligned5441_5442 :
    AlignedValid 12 3 missing5441_5442 records5441_5442 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5441
    maskCheck5441 AlignedValid.nil

def missing5440_5442 : List (BitVec (edgeCount 12)) :=
  missing5440_5441 ++ missing5441_5442
abbrev records5440_5442 : List Blob :=
  records5440_5441 ++ records5441_5442
theorem aligned5440_5442 :
    AlignedValid 12 3 missing5440_5442 records5440_5442 :=
  aligned5440_5441.append aligned5441_5442

def missing5442_5443 : List (BitVec (edgeCount 12)) :=
  [missing5442]
abbrev records5442_5443 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5442]
theorem aligned5442_5443 :
    AlignedValid 12 3 missing5442_5443 records5442_5443 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5442
    maskCheck5442 AlignedValid.nil

def missing5443_5444 : List (BitVec (edgeCount 12)) :=
  [missing5443]
abbrev records5443_5444 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5443]
theorem aligned5443_5444 :
    AlignedValid 12 3 missing5443_5444 records5443_5444 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5443
    maskCheck5443 AlignedValid.nil

def missing5442_5444 : List (BitVec (edgeCount 12)) :=
  missing5442_5443 ++ missing5443_5444
abbrev records5442_5444 : List Blob :=
  records5442_5443 ++ records5443_5444
theorem aligned5442_5444 :
    AlignedValid 12 3 missing5442_5444 records5442_5444 :=
  aligned5442_5443.append aligned5443_5444

def missing5440_5444 : List (BitVec (edgeCount 12)) :=
  missing5440_5442 ++ missing5442_5444
abbrev records5440_5444 : List Blob :=
  records5440_5442 ++ records5442_5444
theorem aligned5440_5444 :
    AlignedValid 12 3 missing5440_5444 records5440_5444 :=
  aligned5440_5442.append aligned5442_5444

def missing5444_5445 : List (BitVec (edgeCount 12)) :=
  [missing5444]
abbrev records5444_5445 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5444]
theorem aligned5444_5445 :
    AlignedValid 12 3 missing5444_5445 records5444_5445 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5444
    maskCheck5444 AlignedValid.nil

def missing5445_5446 : List (BitVec (edgeCount 12)) :=
  [missing5445]
abbrev records5445_5446 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5445]
theorem aligned5445_5446 :
    AlignedValid 12 3 missing5445_5446 records5445_5446 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5445
    maskCheck5445 AlignedValid.nil

def missing5444_5446 : List (BitVec (edgeCount 12)) :=
  missing5444_5445 ++ missing5445_5446
abbrev records5444_5446 : List Blob :=
  records5444_5445 ++ records5445_5446
theorem aligned5444_5446 :
    AlignedValid 12 3 missing5444_5446 records5444_5446 :=
  aligned5444_5445.append aligned5445_5446

def missing5446_5447 : List (BitVec (edgeCount 12)) :=
  [missing5446]
abbrev records5446_5447 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5446]
theorem aligned5446_5447 :
    AlignedValid 12 3 missing5446_5447 records5446_5447 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5446
    maskCheck5446 AlignedValid.nil

def missing5447_5448 : List (BitVec (edgeCount 12)) :=
  [missing5447]
abbrev records5447_5448 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5447]
theorem aligned5447_5448 :
    AlignedValid 12 3 missing5447_5448 records5447_5448 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5447
    maskCheck5447 AlignedValid.nil

def missing5446_5448 : List (BitVec (edgeCount 12)) :=
  missing5446_5447 ++ missing5447_5448
abbrev records5446_5448 : List Blob :=
  records5446_5447 ++ records5447_5448
theorem aligned5446_5448 :
    AlignedValid 12 3 missing5446_5448 records5446_5448 :=
  aligned5446_5447.append aligned5447_5448

def missing5444_5448 : List (BitVec (edgeCount 12)) :=
  missing5444_5446 ++ missing5446_5448
abbrev records5444_5448 : List Blob :=
  records5444_5446 ++ records5446_5448
theorem aligned5444_5448 :
    AlignedValid 12 3 missing5444_5448 records5444_5448 :=
  aligned5444_5446.append aligned5446_5448

def missing5440_5448 : List (BitVec (edgeCount 12)) :=
  missing5440_5444 ++ missing5444_5448
abbrev records5440_5448 : List Blob :=
  records5440_5444 ++ records5444_5448
theorem aligned5440_5448 :
    AlignedValid 12 3 missing5440_5448 records5440_5448 :=
  aligned5440_5444.append aligned5444_5448

def missing5448_5449 : List (BitVec (edgeCount 12)) :=
  [missing5448]
abbrev records5448_5449 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5448]
theorem aligned5448_5449 :
    AlignedValid 12 3 missing5448_5449 records5448_5449 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5448
    maskCheck5448 AlignedValid.nil

def missing5449_5450 : List (BitVec (edgeCount 12)) :=
  [missing5449]
abbrev records5449_5450 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5449]
theorem aligned5449_5450 :
    AlignedValid 12 3 missing5449_5450 records5449_5450 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5449
    maskCheck5449 AlignedValid.nil

def missing5448_5450 : List (BitVec (edgeCount 12)) :=
  missing5448_5449 ++ missing5449_5450
abbrev records5448_5450 : List Blob :=
  records5448_5449 ++ records5449_5450
theorem aligned5448_5450 :
    AlignedValid 12 3 missing5448_5450 records5448_5450 :=
  aligned5448_5449.append aligned5449_5450

def missing5450_5451 : List (BitVec (edgeCount 12)) :=
  [missing5450]
abbrev records5450_5451 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5450]
theorem aligned5450_5451 :
    AlignedValid 12 3 missing5450_5451 records5450_5451 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5450
    maskCheck5450 AlignedValid.nil

def missing5451_5452 : List (BitVec (edgeCount 12)) :=
  [missing5451]
abbrev records5451_5452 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5451]
theorem aligned5451_5452 :
    AlignedValid 12 3 missing5451_5452 records5451_5452 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5451
    maskCheck5451 AlignedValid.nil

def missing5450_5452 : List (BitVec (edgeCount 12)) :=
  missing5450_5451 ++ missing5451_5452
abbrev records5450_5452 : List Blob :=
  records5450_5451 ++ records5451_5452
theorem aligned5450_5452 :
    AlignedValid 12 3 missing5450_5452 records5450_5452 :=
  aligned5450_5451.append aligned5451_5452

def missing5448_5452 : List (BitVec (edgeCount 12)) :=
  missing5448_5450 ++ missing5450_5452
abbrev records5448_5452 : List Blob :=
  records5448_5450 ++ records5450_5452
theorem aligned5448_5452 :
    AlignedValid 12 3 missing5448_5452 records5448_5452 :=
  aligned5448_5450.append aligned5450_5452

def missing5452_5453 : List (BitVec (edgeCount 12)) :=
  [missing5452]
abbrev records5452_5453 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5452]
theorem aligned5452_5453 :
    AlignedValid 12 3 missing5452_5453 records5452_5453 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5452
    maskCheck5452 AlignedValid.nil

def missing5453_5454 : List (BitVec (edgeCount 12)) :=
  [missing5453]
abbrev records5453_5454 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5453]
theorem aligned5453_5454 :
    AlignedValid 12 3 missing5453_5454 records5453_5454 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5453
    maskCheck5453 AlignedValid.nil

def missing5452_5454 : List (BitVec (edgeCount 12)) :=
  missing5452_5453 ++ missing5453_5454
abbrev records5452_5454 : List Blob :=
  records5452_5453 ++ records5453_5454
theorem aligned5452_5454 :
    AlignedValid 12 3 missing5452_5454 records5452_5454 :=
  aligned5452_5453.append aligned5453_5454

def missing5454_5455 : List (BitVec (edgeCount 12)) :=
  [missing5454]
abbrev records5454_5455 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5454]
theorem aligned5454_5455 :
    AlignedValid 12 3 missing5454_5455 records5454_5455 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5454
    maskCheck5454 AlignedValid.nil

def missing5455_5456 : List (BitVec (edgeCount 12)) :=
  [missing5455]
abbrev records5455_5456 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5455]
theorem aligned5455_5456 :
    AlignedValid 12 3 missing5455_5456 records5455_5456 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5455
    maskCheck5455 AlignedValid.nil

def missing5454_5456 : List (BitVec (edgeCount 12)) :=
  missing5454_5455 ++ missing5455_5456
abbrev records5454_5456 : List Blob :=
  records5454_5455 ++ records5455_5456
theorem aligned5454_5456 :
    AlignedValid 12 3 missing5454_5456 records5454_5456 :=
  aligned5454_5455.append aligned5455_5456

def missing5452_5456 : List (BitVec (edgeCount 12)) :=
  missing5452_5454 ++ missing5454_5456
abbrev records5452_5456 : List Blob :=
  records5452_5454 ++ records5454_5456
theorem aligned5452_5456 :
    AlignedValid 12 3 missing5452_5456 records5452_5456 :=
  aligned5452_5454.append aligned5454_5456

def missing5448_5456 : List (BitVec (edgeCount 12)) :=
  missing5448_5452 ++ missing5452_5456
abbrev records5448_5456 : List Blob :=
  records5448_5452 ++ records5452_5456
theorem aligned5448_5456 :
    AlignedValid 12 3 missing5448_5456 records5448_5456 :=
  aligned5448_5452.append aligned5452_5456

def missing5440_5456 : List (BitVec (edgeCount 12)) :=
  missing5440_5448 ++ missing5448_5456
abbrev records5440_5456 : List Blob :=
  records5440_5448 ++ records5448_5456
theorem aligned5440_5456 :
    AlignedValid 12 3 missing5440_5456 records5440_5456 :=
  aligned5440_5448.append aligned5448_5456

def missing5456_5457 : List (BitVec (edgeCount 12)) :=
  [missing5456]
abbrev records5456_5457 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5456]
theorem aligned5456_5457 :
    AlignedValid 12 3 missing5456_5457 records5456_5457 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5456
    maskCheck5456 AlignedValid.nil

def missing5457_5458 : List (BitVec (edgeCount 12)) :=
  [missing5457]
abbrev records5457_5458 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5457]
theorem aligned5457_5458 :
    AlignedValid 12 3 missing5457_5458 records5457_5458 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5457
    maskCheck5457 AlignedValid.nil

def missing5456_5458 : List (BitVec (edgeCount 12)) :=
  missing5456_5457 ++ missing5457_5458
abbrev records5456_5458 : List Blob :=
  records5456_5457 ++ records5457_5458
theorem aligned5456_5458 :
    AlignedValid 12 3 missing5456_5458 records5456_5458 :=
  aligned5456_5457.append aligned5457_5458

def missing5458_5459 : List (BitVec (edgeCount 12)) :=
  [missing5458]
abbrev records5458_5459 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5458]
theorem aligned5458_5459 :
    AlignedValid 12 3 missing5458_5459 records5458_5459 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5458
    maskCheck5458 AlignedValid.nil

def missing5459_5460 : List (BitVec (edgeCount 12)) :=
  [missing5459]
abbrev records5459_5460 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5459]
theorem aligned5459_5460 :
    AlignedValid 12 3 missing5459_5460 records5459_5460 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5459
    maskCheck5459 AlignedValid.nil

def missing5458_5460 : List (BitVec (edgeCount 12)) :=
  missing5458_5459 ++ missing5459_5460
abbrev records5458_5460 : List Blob :=
  records5458_5459 ++ records5459_5460
theorem aligned5458_5460 :
    AlignedValid 12 3 missing5458_5460 records5458_5460 :=
  aligned5458_5459.append aligned5459_5460

def missing5456_5460 : List (BitVec (edgeCount 12)) :=
  missing5456_5458 ++ missing5458_5460
abbrev records5456_5460 : List Blob :=
  records5456_5458 ++ records5458_5460
theorem aligned5456_5460 :
    AlignedValid 12 3 missing5456_5460 records5456_5460 :=
  aligned5456_5458.append aligned5458_5460

def missing5460_5461 : List (BitVec (edgeCount 12)) :=
  [missing5460]
abbrev records5460_5461 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5460]
theorem aligned5460_5461 :
    AlignedValid 12 3 missing5460_5461 records5460_5461 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5460
    maskCheck5460 AlignedValid.nil

def missing5461_5462 : List (BitVec (edgeCount 12)) :=
  [missing5461]
abbrev records5461_5462 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5461]
theorem aligned5461_5462 :
    AlignedValid 12 3 missing5461_5462 records5461_5462 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5461
    maskCheck5461 AlignedValid.nil

def missing5460_5462 : List (BitVec (edgeCount 12)) :=
  missing5460_5461 ++ missing5461_5462
abbrev records5460_5462 : List Blob :=
  records5460_5461 ++ records5461_5462
theorem aligned5460_5462 :
    AlignedValid 12 3 missing5460_5462 records5460_5462 :=
  aligned5460_5461.append aligned5461_5462

def missing5462_5463 : List (BitVec (edgeCount 12)) :=
  [missing5462]
abbrev records5462_5463 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5462]
theorem aligned5462_5463 :
    AlignedValid 12 3 missing5462_5463 records5462_5463 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5462
    maskCheck5462 AlignedValid.nil

def missing5463_5464 : List (BitVec (edgeCount 12)) :=
  [missing5463]
abbrev records5463_5464 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5463]
theorem aligned5463_5464 :
    AlignedValid 12 3 missing5463_5464 records5463_5464 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5463
    maskCheck5463 AlignedValid.nil

def missing5462_5464 : List (BitVec (edgeCount 12)) :=
  missing5462_5463 ++ missing5463_5464
abbrev records5462_5464 : List Blob :=
  records5462_5463 ++ records5463_5464
theorem aligned5462_5464 :
    AlignedValid 12 3 missing5462_5464 records5462_5464 :=
  aligned5462_5463.append aligned5463_5464

def missing5460_5464 : List (BitVec (edgeCount 12)) :=
  missing5460_5462 ++ missing5462_5464
abbrev records5460_5464 : List Blob :=
  records5460_5462 ++ records5462_5464
theorem aligned5460_5464 :
    AlignedValid 12 3 missing5460_5464 records5460_5464 :=
  aligned5460_5462.append aligned5462_5464

def missing5456_5464 : List (BitVec (edgeCount 12)) :=
  missing5456_5460 ++ missing5460_5464
abbrev records5456_5464 : List Blob :=
  records5456_5460 ++ records5460_5464
theorem aligned5456_5464 :
    AlignedValid 12 3 missing5456_5464 records5456_5464 :=
  aligned5456_5460.append aligned5460_5464

def missing5464_5465 : List (BitVec (edgeCount 12)) :=
  [missing5464]
abbrev records5464_5465 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5464]
theorem aligned5464_5465 :
    AlignedValid 12 3 missing5464_5465 records5464_5465 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5464
    maskCheck5464 AlignedValid.nil

def missing5465_5466 : List (BitVec (edgeCount 12)) :=
  [missing5465]
abbrev records5465_5466 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5465]
theorem aligned5465_5466 :
    AlignedValid 12 3 missing5465_5466 records5465_5466 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5465
    maskCheck5465 AlignedValid.nil

def missing5464_5466 : List (BitVec (edgeCount 12)) :=
  missing5464_5465 ++ missing5465_5466
abbrev records5464_5466 : List Blob :=
  records5464_5465 ++ records5465_5466
theorem aligned5464_5466 :
    AlignedValid 12 3 missing5464_5466 records5464_5466 :=
  aligned5464_5465.append aligned5465_5466

def missing5466_5467 : List (BitVec (edgeCount 12)) :=
  [missing5466]
abbrev records5466_5467 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5466]
theorem aligned5466_5467 :
    AlignedValid 12 3 missing5466_5467 records5466_5467 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5466
    maskCheck5466 AlignedValid.nil

def missing5467_5468 : List (BitVec (edgeCount 12)) :=
  [missing5467]
abbrev records5467_5468 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5467]
theorem aligned5467_5468 :
    AlignedValid 12 3 missing5467_5468 records5467_5468 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5467
    maskCheck5467 AlignedValid.nil

def missing5466_5468 : List (BitVec (edgeCount 12)) :=
  missing5466_5467 ++ missing5467_5468
abbrev records5466_5468 : List Blob :=
  records5466_5467 ++ records5467_5468
theorem aligned5466_5468 :
    AlignedValid 12 3 missing5466_5468 records5466_5468 :=
  aligned5466_5467.append aligned5467_5468

def missing5464_5468 : List (BitVec (edgeCount 12)) :=
  missing5464_5466 ++ missing5466_5468
abbrev records5464_5468 : List Blob :=
  records5464_5466 ++ records5466_5468
theorem aligned5464_5468 :
    AlignedValid 12 3 missing5464_5468 records5464_5468 :=
  aligned5464_5466.append aligned5466_5468

def missing5468_5469 : List (BitVec (edgeCount 12)) :=
  [missing5468]
abbrev records5468_5469 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5468]
theorem aligned5468_5469 :
    AlignedValid 12 3 missing5468_5469 records5468_5469 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5468
    maskCheck5468 AlignedValid.nil

def missing5469_5470 : List (BitVec (edgeCount 12)) :=
  [missing5469]
abbrev records5469_5470 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5469]
theorem aligned5469_5470 :
    AlignedValid 12 3 missing5469_5470 records5469_5470 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5469
    maskCheck5469 AlignedValid.nil

def missing5468_5470 : List (BitVec (edgeCount 12)) :=
  missing5468_5469 ++ missing5469_5470
abbrev records5468_5470 : List Blob :=
  records5468_5469 ++ records5469_5470
theorem aligned5468_5470 :
    AlignedValid 12 3 missing5468_5470 records5468_5470 :=
  aligned5468_5469.append aligned5469_5470

def missing5470_5471 : List (BitVec (edgeCount 12)) :=
  [missing5470]
abbrev records5470_5471 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5470]
theorem aligned5470_5471 :
    AlignedValid 12 3 missing5470_5471 records5470_5471 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5470
    maskCheck5470 AlignedValid.nil

def missing5471_5472 : List (BitVec (edgeCount 12)) :=
  [missing5471]
abbrev records5471_5472 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5471]
theorem aligned5471_5472 :
    AlignedValid 12 3 missing5471_5472 records5471_5472 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5471
    maskCheck5471 AlignedValid.nil

def missing5470_5472 : List (BitVec (edgeCount 12)) :=
  missing5470_5471 ++ missing5471_5472
abbrev records5470_5472 : List Blob :=
  records5470_5471 ++ records5471_5472
theorem aligned5470_5472 :
    AlignedValid 12 3 missing5470_5472 records5470_5472 :=
  aligned5470_5471.append aligned5471_5472

def missing5468_5472 : List (BitVec (edgeCount 12)) :=
  missing5468_5470 ++ missing5470_5472
abbrev records5468_5472 : List Blob :=
  records5468_5470 ++ records5470_5472
theorem aligned5468_5472 :
    AlignedValid 12 3 missing5468_5472 records5468_5472 :=
  aligned5468_5470.append aligned5470_5472

def missing5464_5472 : List (BitVec (edgeCount 12)) :=
  missing5464_5468 ++ missing5468_5472
abbrev records5464_5472 : List Blob :=
  records5464_5468 ++ records5468_5472
theorem aligned5464_5472 :
    AlignedValid 12 3 missing5464_5472 records5464_5472 :=
  aligned5464_5468.append aligned5468_5472

def missing5456_5472 : List (BitVec (edgeCount 12)) :=
  missing5456_5464 ++ missing5464_5472
abbrev records5456_5472 : List Blob :=
  records5456_5464 ++ records5464_5472
theorem aligned5456_5472 :
    AlignedValid 12 3 missing5456_5472 records5456_5472 :=
  aligned5456_5464.append aligned5464_5472

def missing5440_5472 : List (BitVec (edgeCount 12)) :=
  missing5440_5456 ++ missing5456_5472
abbrev records5440_5472 : List Blob :=
  records5440_5456 ++ records5456_5472
theorem aligned5440_5472 :
    AlignedValid 12 3 missing5440_5472 records5440_5472 :=
  aligned5440_5456.append aligned5456_5472

def missing5472_5473 : List (BitVec (edgeCount 12)) :=
  [missing5472]
abbrev records5472_5473 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5472]
theorem aligned5472_5473 :
    AlignedValid 12 3 missing5472_5473 records5472_5473 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5472
    maskCheck5472 AlignedValid.nil

def missing5473_5474 : List (BitVec (edgeCount 12)) :=
  [missing5473]
abbrev records5473_5474 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5473]
theorem aligned5473_5474 :
    AlignedValid 12 3 missing5473_5474 records5473_5474 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5473
    maskCheck5473 AlignedValid.nil

def missing5472_5474 : List (BitVec (edgeCount 12)) :=
  missing5472_5473 ++ missing5473_5474
abbrev records5472_5474 : List Blob :=
  records5472_5473 ++ records5473_5474
theorem aligned5472_5474 :
    AlignedValid 12 3 missing5472_5474 records5472_5474 :=
  aligned5472_5473.append aligned5473_5474

def missing5474_5475 : List (BitVec (edgeCount 12)) :=
  [missing5474]
abbrev records5474_5475 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5474]
theorem aligned5474_5475 :
    AlignedValid 12 3 missing5474_5475 records5474_5475 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5474
    maskCheck5474 AlignedValid.nil

def missing5475_5476 : List (BitVec (edgeCount 12)) :=
  [missing5475]
abbrev records5475_5476 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5475]
theorem aligned5475_5476 :
    AlignedValid 12 3 missing5475_5476 records5475_5476 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5475
    maskCheck5475 AlignedValid.nil

def missing5474_5476 : List (BitVec (edgeCount 12)) :=
  missing5474_5475 ++ missing5475_5476
abbrev records5474_5476 : List Blob :=
  records5474_5475 ++ records5475_5476
theorem aligned5474_5476 :
    AlignedValid 12 3 missing5474_5476 records5474_5476 :=
  aligned5474_5475.append aligned5475_5476

def missing5472_5476 : List (BitVec (edgeCount 12)) :=
  missing5472_5474 ++ missing5474_5476
abbrev records5472_5476 : List Blob :=
  records5472_5474 ++ records5474_5476
theorem aligned5472_5476 :
    AlignedValid 12 3 missing5472_5476 records5472_5476 :=
  aligned5472_5474.append aligned5474_5476

def missing5476_5477 : List (BitVec (edgeCount 12)) :=
  [missing5476]
abbrev records5476_5477 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5476]
theorem aligned5476_5477 :
    AlignedValid 12 3 missing5476_5477 records5476_5477 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5476
    maskCheck5476 AlignedValid.nil

def missing5477_5478 : List (BitVec (edgeCount 12)) :=
  [missing5477]
abbrev records5477_5478 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5477]
theorem aligned5477_5478 :
    AlignedValid 12 3 missing5477_5478 records5477_5478 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5477
    maskCheck5477 AlignedValid.nil

def missing5476_5478 : List (BitVec (edgeCount 12)) :=
  missing5476_5477 ++ missing5477_5478
abbrev records5476_5478 : List Blob :=
  records5476_5477 ++ records5477_5478
theorem aligned5476_5478 :
    AlignedValid 12 3 missing5476_5478 records5476_5478 :=
  aligned5476_5477.append aligned5477_5478

def missing5478_5479 : List (BitVec (edgeCount 12)) :=
  [missing5478]
abbrev records5478_5479 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5478]
theorem aligned5478_5479 :
    AlignedValid 12 3 missing5478_5479 records5478_5479 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5478
    maskCheck5478 AlignedValid.nil

def missing5479_5480 : List (BitVec (edgeCount 12)) :=
  [missing5479]
abbrev records5479_5480 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5479]
theorem aligned5479_5480 :
    AlignedValid 12 3 missing5479_5480 records5479_5480 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5479
    maskCheck5479 AlignedValid.nil

def missing5478_5480 : List (BitVec (edgeCount 12)) :=
  missing5478_5479 ++ missing5479_5480
abbrev records5478_5480 : List Blob :=
  records5478_5479 ++ records5479_5480
theorem aligned5478_5480 :
    AlignedValid 12 3 missing5478_5480 records5478_5480 :=
  aligned5478_5479.append aligned5479_5480

def missing5476_5480 : List (BitVec (edgeCount 12)) :=
  missing5476_5478 ++ missing5478_5480
abbrev records5476_5480 : List Blob :=
  records5476_5478 ++ records5478_5480
theorem aligned5476_5480 :
    AlignedValid 12 3 missing5476_5480 records5476_5480 :=
  aligned5476_5478.append aligned5478_5480

def missing5472_5480 : List (BitVec (edgeCount 12)) :=
  missing5472_5476 ++ missing5476_5480
abbrev records5472_5480 : List Blob :=
  records5472_5476 ++ records5476_5480
theorem aligned5472_5480 :
    AlignedValid 12 3 missing5472_5480 records5472_5480 :=
  aligned5472_5476.append aligned5476_5480

def missing5480_5481 : List (BitVec (edgeCount 12)) :=
  [missing5480]
abbrev records5480_5481 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5480]
theorem aligned5480_5481 :
    AlignedValid 12 3 missing5480_5481 records5480_5481 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5480
    maskCheck5480 AlignedValid.nil

def missing5481_5482 : List (BitVec (edgeCount 12)) :=
  [missing5481]
abbrev records5481_5482 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5481]
theorem aligned5481_5482 :
    AlignedValid 12 3 missing5481_5482 records5481_5482 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5481
    maskCheck5481 AlignedValid.nil

def missing5480_5482 : List (BitVec (edgeCount 12)) :=
  missing5480_5481 ++ missing5481_5482
abbrev records5480_5482 : List Blob :=
  records5480_5481 ++ records5481_5482
theorem aligned5480_5482 :
    AlignedValid 12 3 missing5480_5482 records5480_5482 :=
  aligned5480_5481.append aligned5481_5482

def missing5482_5483 : List (BitVec (edgeCount 12)) :=
  [missing5482]
abbrev records5482_5483 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5482]
theorem aligned5482_5483 :
    AlignedValid 12 3 missing5482_5483 records5482_5483 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5482
    maskCheck5482 AlignedValid.nil

def missing5483_5484 : List (BitVec (edgeCount 12)) :=
  [missing5483]
abbrev records5483_5484 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5483]
theorem aligned5483_5484 :
    AlignedValid 12 3 missing5483_5484 records5483_5484 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5483
    maskCheck5483 AlignedValid.nil

def missing5482_5484 : List (BitVec (edgeCount 12)) :=
  missing5482_5483 ++ missing5483_5484
abbrev records5482_5484 : List Blob :=
  records5482_5483 ++ records5483_5484
theorem aligned5482_5484 :
    AlignedValid 12 3 missing5482_5484 records5482_5484 :=
  aligned5482_5483.append aligned5483_5484

def missing5480_5484 : List (BitVec (edgeCount 12)) :=
  missing5480_5482 ++ missing5482_5484
abbrev records5480_5484 : List Blob :=
  records5480_5482 ++ records5482_5484
theorem aligned5480_5484 :
    AlignedValid 12 3 missing5480_5484 records5480_5484 :=
  aligned5480_5482.append aligned5482_5484

def missing5484_5485 : List (BitVec (edgeCount 12)) :=
  [missing5484]
abbrev records5484_5485 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5484]
theorem aligned5484_5485 :
    AlignedValid 12 3 missing5484_5485 records5484_5485 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5484
    maskCheck5484 AlignedValid.nil

def missing5485_5486 : List (BitVec (edgeCount 12)) :=
  [missing5485]
abbrev records5485_5486 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5485]
theorem aligned5485_5486 :
    AlignedValid 12 3 missing5485_5486 records5485_5486 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5485
    maskCheck5485 AlignedValid.nil

def missing5484_5486 : List (BitVec (edgeCount 12)) :=
  missing5484_5485 ++ missing5485_5486
abbrev records5484_5486 : List Blob :=
  records5484_5485 ++ records5485_5486
theorem aligned5484_5486 :
    AlignedValid 12 3 missing5484_5486 records5484_5486 :=
  aligned5484_5485.append aligned5485_5486

def missing5486_5487 : List (BitVec (edgeCount 12)) :=
  [missing5486]
abbrev records5486_5487 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5486]
theorem aligned5486_5487 :
    AlignedValid 12 3 missing5486_5487 records5486_5487 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5486
    maskCheck5486 AlignedValid.nil

def missing5487_5488 : List (BitVec (edgeCount 12)) :=
  [missing5487]
abbrev records5487_5488 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5487]
theorem aligned5487_5488 :
    AlignedValid 12 3 missing5487_5488 records5487_5488 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5487
    maskCheck5487 AlignedValid.nil

def missing5486_5488 : List (BitVec (edgeCount 12)) :=
  missing5486_5487 ++ missing5487_5488
abbrev records5486_5488 : List Blob :=
  records5486_5487 ++ records5487_5488
theorem aligned5486_5488 :
    AlignedValid 12 3 missing5486_5488 records5486_5488 :=
  aligned5486_5487.append aligned5487_5488

def missing5484_5488 : List (BitVec (edgeCount 12)) :=
  missing5484_5486 ++ missing5486_5488
abbrev records5484_5488 : List Blob :=
  records5484_5486 ++ records5486_5488
theorem aligned5484_5488 :
    AlignedValid 12 3 missing5484_5488 records5484_5488 :=
  aligned5484_5486.append aligned5486_5488

def missing5480_5488 : List (BitVec (edgeCount 12)) :=
  missing5480_5484 ++ missing5484_5488
abbrev records5480_5488 : List Blob :=
  records5480_5484 ++ records5484_5488
theorem aligned5480_5488 :
    AlignedValid 12 3 missing5480_5488 records5480_5488 :=
  aligned5480_5484.append aligned5484_5488

def missing5472_5488 : List (BitVec (edgeCount 12)) :=
  missing5472_5480 ++ missing5480_5488
abbrev records5472_5488 : List Blob :=
  records5472_5480 ++ records5480_5488
theorem aligned5472_5488 :
    AlignedValid 12 3 missing5472_5488 records5472_5488 :=
  aligned5472_5480.append aligned5480_5488

def missing5488_5489 : List (BitVec (edgeCount 12)) :=
  [missing5488]
abbrev records5488_5489 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5488]
theorem aligned5488_5489 :
    AlignedValid 12 3 missing5488_5489 records5488_5489 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5488
    maskCheck5488 AlignedValid.nil

def missing5489_5490 : List (BitVec (edgeCount 12)) :=
  [missing5489]
abbrev records5489_5490 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5489]
theorem aligned5489_5490 :
    AlignedValid 12 3 missing5489_5490 records5489_5490 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5489
    maskCheck5489 AlignedValid.nil

def missing5488_5490 : List (BitVec (edgeCount 12)) :=
  missing5488_5489 ++ missing5489_5490
abbrev records5488_5490 : List Blob :=
  records5488_5489 ++ records5489_5490
theorem aligned5488_5490 :
    AlignedValid 12 3 missing5488_5490 records5488_5490 :=
  aligned5488_5489.append aligned5489_5490

def missing5490_5491 : List (BitVec (edgeCount 12)) :=
  [missing5490]
abbrev records5490_5491 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5490]
theorem aligned5490_5491 :
    AlignedValid 12 3 missing5490_5491 records5490_5491 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5490
    maskCheck5490 AlignedValid.nil

def missing5491_5492 : List (BitVec (edgeCount 12)) :=
  [missing5491]
abbrev records5491_5492 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5491]
theorem aligned5491_5492 :
    AlignedValid 12 3 missing5491_5492 records5491_5492 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5491
    maskCheck5491 AlignedValid.nil

def missing5490_5492 : List (BitVec (edgeCount 12)) :=
  missing5490_5491 ++ missing5491_5492
abbrev records5490_5492 : List Blob :=
  records5490_5491 ++ records5491_5492
theorem aligned5490_5492 :
    AlignedValid 12 3 missing5490_5492 records5490_5492 :=
  aligned5490_5491.append aligned5491_5492

def missing5488_5492 : List (BitVec (edgeCount 12)) :=
  missing5488_5490 ++ missing5490_5492
abbrev records5488_5492 : List Blob :=
  records5488_5490 ++ records5490_5492
theorem aligned5488_5492 :
    AlignedValid 12 3 missing5488_5492 records5488_5492 :=
  aligned5488_5490.append aligned5490_5492

def missing5492_5493 : List (BitVec (edgeCount 12)) :=
  [missing5492]
abbrev records5492_5493 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5492]
theorem aligned5492_5493 :
    AlignedValid 12 3 missing5492_5493 records5492_5493 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5492
    maskCheck5492 AlignedValid.nil

def missing5493_5494 : List (BitVec (edgeCount 12)) :=
  [missing5493]
abbrev records5493_5494 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5493]
theorem aligned5493_5494 :
    AlignedValid 12 3 missing5493_5494 records5493_5494 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5493
    maskCheck5493 AlignedValid.nil

def missing5492_5494 : List (BitVec (edgeCount 12)) :=
  missing5492_5493 ++ missing5493_5494
abbrev records5492_5494 : List Blob :=
  records5492_5493 ++ records5493_5494
theorem aligned5492_5494 :
    AlignedValid 12 3 missing5492_5494 records5492_5494 :=
  aligned5492_5493.append aligned5493_5494

def missing5494_5495 : List (BitVec (edgeCount 12)) :=
  [missing5494]
abbrev records5494_5495 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5494]
theorem aligned5494_5495 :
    AlignedValid 12 3 missing5494_5495 records5494_5495 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5494
    maskCheck5494 AlignedValid.nil

def missing5495_5496 : List (BitVec (edgeCount 12)) :=
  [missing5495]
abbrev records5495_5496 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5495]
theorem aligned5495_5496 :
    AlignedValid 12 3 missing5495_5496 records5495_5496 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5495
    maskCheck5495 AlignedValid.nil

def missing5494_5496 : List (BitVec (edgeCount 12)) :=
  missing5494_5495 ++ missing5495_5496
abbrev records5494_5496 : List Blob :=
  records5494_5495 ++ records5495_5496
theorem aligned5494_5496 :
    AlignedValid 12 3 missing5494_5496 records5494_5496 :=
  aligned5494_5495.append aligned5495_5496

def missing5492_5496 : List (BitVec (edgeCount 12)) :=
  missing5492_5494 ++ missing5494_5496
abbrev records5492_5496 : List Blob :=
  records5492_5494 ++ records5494_5496
theorem aligned5492_5496 :
    AlignedValid 12 3 missing5492_5496 records5492_5496 :=
  aligned5492_5494.append aligned5494_5496

def missing5488_5496 : List (BitVec (edgeCount 12)) :=
  missing5488_5492 ++ missing5492_5496
abbrev records5488_5496 : List Blob :=
  records5488_5492 ++ records5492_5496
theorem aligned5488_5496 :
    AlignedValid 12 3 missing5488_5496 records5488_5496 :=
  aligned5488_5492.append aligned5492_5496

def missing5496_5497 : List (BitVec (edgeCount 12)) :=
  [missing5496]
abbrev records5496_5497 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5496]
theorem aligned5496_5497 :
    AlignedValid 12 3 missing5496_5497 records5496_5497 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5496
    maskCheck5496 AlignedValid.nil

def missing5497_5498 : List (BitVec (edgeCount 12)) :=
  [missing5497]
abbrev records5497_5498 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5497]
theorem aligned5497_5498 :
    AlignedValid 12 3 missing5497_5498 records5497_5498 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5497
    maskCheck5497 AlignedValid.nil

def missing5496_5498 : List (BitVec (edgeCount 12)) :=
  missing5496_5497 ++ missing5497_5498
abbrev records5496_5498 : List Blob :=
  records5496_5497 ++ records5497_5498
theorem aligned5496_5498 :
    AlignedValid 12 3 missing5496_5498 records5496_5498 :=
  aligned5496_5497.append aligned5497_5498

def missing5498_5499 : List (BitVec (edgeCount 12)) :=
  [missing5498]
abbrev records5498_5499 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5498]
theorem aligned5498_5499 :
    AlignedValid 12 3 missing5498_5499 records5498_5499 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5498
    maskCheck5498 AlignedValid.nil

def missing5499_5500 : List (BitVec (edgeCount 12)) :=
  [missing5499]
abbrev records5499_5500 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5499]
theorem aligned5499_5500 :
    AlignedValid 12 3 missing5499_5500 records5499_5500 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5499
    maskCheck5499 AlignedValid.nil

def missing5498_5500 : List (BitVec (edgeCount 12)) :=
  missing5498_5499 ++ missing5499_5500
abbrev records5498_5500 : List Blob :=
  records5498_5499 ++ records5499_5500
theorem aligned5498_5500 :
    AlignedValid 12 3 missing5498_5500 records5498_5500 :=
  aligned5498_5499.append aligned5499_5500

def missing5496_5500 : List (BitVec (edgeCount 12)) :=
  missing5496_5498 ++ missing5498_5500
abbrev records5496_5500 : List Blob :=
  records5496_5498 ++ records5498_5500
theorem aligned5496_5500 :
    AlignedValid 12 3 missing5496_5500 records5496_5500 :=
  aligned5496_5498.append aligned5498_5500

def missing5500_5501 : List (BitVec (edgeCount 12)) :=
  [missing5500]
abbrev records5500_5501 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5500]
theorem aligned5500_5501 :
    AlignedValid 12 3 missing5500_5501 records5500_5501 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5500
    maskCheck5500 AlignedValid.nil

def missing5501_5502 : List (BitVec (edgeCount 12)) :=
  [missing5501]
abbrev records5501_5502 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5501]
theorem aligned5501_5502 :
    AlignedValid 12 3 missing5501_5502 records5501_5502 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5501
    maskCheck5501 AlignedValid.nil

def missing5500_5502 : List (BitVec (edgeCount 12)) :=
  missing5500_5501 ++ missing5501_5502
abbrev records5500_5502 : List Blob :=
  records5500_5501 ++ records5501_5502
theorem aligned5500_5502 :
    AlignedValid 12 3 missing5500_5502 records5500_5502 :=
  aligned5500_5501.append aligned5501_5502

def missing5502_5503 : List (BitVec (edgeCount 12)) :=
  [missing5502]
abbrev records5502_5503 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5502]
theorem aligned5502_5503 :
    AlignedValid 12 3 missing5502_5503 records5502_5503 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5502
    maskCheck5502 AlignedValid.nil

def missing5503_5504 : List (BitVec (edgeCount 12)) :=
  [missing5503]
abbrev records5503_5504 : List Blob :=
  [StrongPackedBucketN12A3Shard042.record5503]
theorem aligned5503_5504 :
    AlignedValid 12 3 missing5503_5504 records5503_5504 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard042.check5503
    maskCheck5503 AlignedValid.nil

def missing5502_5504 : List (BitVec (edgeCount 12)) :=
  missing5502_5503 ++ missing5503_5504
abbrev records5502_5504 : List Blob :=
  records5502_5503 ++ records5503_5504
theorem aligned5502_5504 :
    AlignedValid 12 3 missing5502_5504 records5502_5504 :=
  aligned5502_5503.append aligned5503_5504

def missing5500_5504 : List (BitVec (edgeCount 12)) :=
  missing5500_5502 ++ missing5502_5504
abbrev records5500_5504 : List Blob :=
  records5500_5502 ++ records5502_5504
theorem aligned5500_5504 :
    AlignedValid 12 3 missing5500_5504 records5500_5504 :=
  aligned5500_5502.append aligned5502_5504

def missing5496_5504 : List (BitVec (edgeCount 12)) :=
  missing5496_5500 ++ missing5500_5504
abbrev records5496_5504 : List Blob :=
  records5496_5500 ++ records5500_5504
theorem aligned5496_5504 :
    AlignedValid 12 3 missing5496_5504 records5496_5504 :=
  aligned5496_5500.append aligned5500_5504

def missing5488_5504 : List (BitVec (edgeCount 12)) :=
  missing5488_5496 ++ missing5496_5504
abbrev records5488_5504 : List Blob :=
  records5488_5496 ++ records5496_5504
theorem aligned5488_5504 :
    AlignedValid 12 3 missing5488_5504 records5488_5504 :=
  aligned5488_5496.append aligned5496_5504

def missing5472_5504 : List (BitVec (edgeCount 12)) :=
  missing5472_5488 ++ missing5488_5504
abbrev records5472_5504 : List Blob :=
  records5472_5488 ++ records5488_5504
theorem aligned5472_5504 :
    AlignedValid 12 3 missing5472_5504 records5472_5504 :=
  aligned5472_5488.append aligned5488_5504

def missing5440_5504 : List (BitVec (edgeCount 12)) :=
  missing5440_5472 ++ missing5472_5504
abbrev records5440_5504 : List Blob :=
  records5440_5472 ++ records5472_5504
theorem aligned5440_5504 :
    AlignedValid 12 3 missing5440_5504 records5440_5504 :=
  aligned5440_5472.append aligned5472_5504

def missing5376_5504 : List (BitVec (edgeCount 12)) :=
  missing5376_5440 ++ missing5440_5504
abbrev records5376_5504 : List Blob :=
  records5376_5440 ++ records5440_5504
theorem aligned5376_5504 :
    AlignedValid 12 3 missing5376_5504 records5376_5504 :=
  aligned5376_5440.append aligned5440_5504

abbrev missing : List (BitVec (edgeCount 12)) := missing5376_5504
abbrev records : List Blob := records5376_5504
theorem aligned : AlignedValid 12 3 missing records := aligned5376_5504

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard042
