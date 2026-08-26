/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard096

/-! Decode-only alignment checks for n=12, a=4, records 12288--12415. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard096

open PackedBucketCertificate

def missing12288 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46945945072311468032
theorem maskCheck12288 :
    checkMaskFor missing12288 StrongPackedBucketN12A4Shard096.record12288 = true := by
  decide

def missing12289 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47090060260387323904
theorem maskCheck12289 :
    checkMaskFor missing12289 StrongPackedBucketN12A4Shard096.record12289 = true := by
  decide

def missing12290 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47954751388842459136
theorem maskCheck12290 :
    checkMaskFor missing12290 StrongPackedBucketN12A4Shard096.record12290 = true := by
  decide

def missing12291 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50981170338435432448
theorem maskCheck12291 :
    checkMaskFor missing12291 StrongPackedBucketN12A4Shard096.record12291 = true := by
  decide

def missing12292 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51125285526511288320
theorem maskCheck12292 :
    checkMaskFor missing12292 StrongPackedBucketN12A4Shard096.record12292 = true := by
  decide

def missing12293 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55881086733014532096
theorem maskCheck12293 :
    checkMaskFor missing12293 StrongPackedBucketN12A4Shard096.record12293 = true := by
  decide

def missing12294 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56169317109166243840
theorem maskCheck12294 :
    checkMaskFor missing12294 StrongPackedBucketN12A4Shard096.record12294 = true := by
  decide

def missing12295 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56385489891280027648
theorem maskCheck12295 :
    checkMaskFor missing12295 StrongPackedBucketN12A4Shard096.record12295 = true := by
  decide

def missing12296 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57250181019735162880
theorem maskCheck12296 :
    checkMaskFor missing12296 StrongPackedBucketN12A4Shard096.record12296 = true := by
  decide

def missing12297 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60420715157403992064
theorem maskCheck12297 :
    checkMaskFor missing12297 StrongPackedBucketN12A4Shard096.record12297 = true := by
  decide

def missing12298 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64816228393717596160
theorem maskCheck12298 :
    checkMaskFor missing12298 StrongPackedBucketN12A4Shard096.record12298 = true := by
  decide

def missing12299 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2270658981261213696
theorem maskCheck12299 :
    checkMaskFor missing12299 StrongPackedBucketN12A4Shard096.record12299 = true := by
  decide

def missing12300 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4000041238171484160
theorem maskCheck12300 :
    checkMaskFor missing12300 StrongPackedBucketN12A4Shard096.record12300 = true := by
  decide

def missing12301 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4432386802399051776
theorem maskCheck12301 :
    checkMaskFor missing12301 StrongPackedBucketN12A4Shard096.record12301 = true := by
  decide

def missing12302 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4504444396436979712
theorem maskCheck12302 :
    checkMaskFor missing12302 StrongPackedBucketN12A4Shard096.record12302 = true := by
  decide

def missing12303 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4540473193455943680
theorem maskCheck12303 :
    checkMaskFor missing12303 StrongPackedBucketN12A4Shard096.record12303 = true := by
  decide

def missing12304 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5729423495081754624
theorem maskCheck12304 :
    checkMaskFor missing12304 StrongPackedBucketN12A4Shard096.record12304 = true := by
  decide

def missing12305 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6305884247385178112
theorem maskCheck12305 :
    checkMaskFor missing12305 StrongPackedBucketN12A4Shard096.record12305 = true := by
  decide

def missing12306 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6738229811612745728
theorem maskCheck12306 :
    checkMaskFor missing12306 StrongPackedBucketN12A4Shard096.record12306 = true := by
  decide

def missing12307 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6810287405650673664
theorem maskCheck12307 :
    checkMaskFor missing12307 StrongPackedBucketN12A4Shard096.record12307 = true := by
  decide

def missing12308 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6846316202669637632
theorem maskCheck12308 :
    checkMaskFor missing12308 StrongPackedBucketN12A4Shard096.record12308 = true := by
  decide

def missing12309 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8323496880447160320
theorem maskCheck12309 :
    checkMaskFor missing12309 StrongPackedBucketN12A4Shard096.record12309 = true := by
  decide

def missing12310 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8467612068523016192
theorem maskCheck12310 :
    checkMaskFor missing12310 StrongPackedBucketN12A4Shard096.record12310 = true := by
  decide

def missing12311 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8539669662560944128
theorem maskCheck12311 :
    checkMaskFor missing12311 StrongPackedBucketN12A4Shard096.record12311 = true := by
  decide

def missing12312 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8575698459579908096
theorem maskCheck12312 :
    checkMaskFor missing12312 StrongPackedBucketN12A4Shard096.record12312 = true := by
  decide

def missing12313 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8972015226788511744
theorem maskCheck12313 :
    checkMaskFor missing12313 StrongPackedBucketN12A4Shard096.record12313 = true := by
  decide

def missing12314 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9080101617845403648
theorem maskCheck12314 :
    checkMaskFor missing12314 StrongPackedBucketN12A4Shard096.record12314 = true := by
  decide

def missing12315 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10341109513509142528
theorem maskCheck12315 :
    checkMaskFor missing12315 StrongPackedBucketN12A4Shard096.record12315 = true := by
  decide

def missing12316 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10917570265812566016
theorem maskCheck12316 :
    checkMaskFor missing12316 StrongPackedBucketN12A4Shard096.record12316 = true := by
  decide

def missing12317 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11349915830040133632
theorem maskCheck12317 :
    checkMaskFor missing12317 StrongPackedBucketN12A4Shard096.record12317 = true := by
  decide

def missing12318 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11458002221097025536
theorem maskCheck12318 :
    checkMaskFor missing12318 StrongPackedBucketN12A4Shard096.record12318 = true := by
  decide

def missing12319 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12935182898874548224
theorem maskCheck12319 :
    checkMaskFor missing12319 StrongPackedBucketN12A4Shard096.record12319 = true := by
  decide

def missing12320 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13079298086950404096
theorem maskCheck12320 :
    checkMaskFor missing12320 StrongPackedBucketN12A4Shard096.record12320 = true := by
  decide

def missing12321 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13187384478007296000
theorem maskCheck12321 :
    checkMaskFor missing12321 StrongPackedBucketN12A4Shard096.record12321 = true := by
  decide

def missing12322 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13619730042234863616
theorem maskCheck12322 :
    checkMaskFor missing12322 StrongPackedBucketN12A4Shard096.record12322 = true := by
  decide

def missing12323 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14376334779633106944
theorem maskCheck12323 :
    checkMaskFor missing12323 StrongPackedBucketN12A4Shard096.record12323 = true := by
  decide

def missing12324 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14808680343860674560
theorem maskCheck12324 :
    checkMaskFor missing12324 StrongPackedBucketN12A4Shard096.record12324 = true := by
  decide

def missing12325 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14916766734917566464
theorem maskCheck12325 :
    checkMaskFor missing12325 StrongPackedBucketN12A4Shard096.record12325 = true := by
  decide

def missing12326 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15241025908088242176
theorem maskCheck12326 :
    checkMaskFor missing12326 StrongPackedBucketN12A4Shard096.record12326 = true := by
  decide

def missing12327 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15385141096164098048
theorem maskCheck12327 :
    checkMaskFor missing12327 StrongPackedBucketN12A4Shard096.record12327 = true := by
  decide

def missing12328 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15493227487220989952
theorem maskCheck12328 :
    checkMaskFor missing12328 StrongPackedBucketN12A4Shard096.record12328 = true := by
  decide

def missing12329 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17402753729226080256
theorem maskCheck12329 :
    checkMaskFor missing12329 StrongPackedBucketN12A4Shard096.record12329 = true := by
  decide

def missing12330 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17510840120282972160
theorem maskCheck12330 :
    checkMaskFor missing12330 StrongPackedBucketN12A4Shard096.record12330 = true := by
  decide

def missing12331 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19564481550363918336
theorem maskCheck12331 :
    checkMaskFor missing12331 StrongPackedBucketN12A4Shard096.record12331 = true := by
  decide

def missing12332 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20140942302667341824
theorem maskCheck12332 :
    checkMaskFor missing12332 StrongPackedBucketN12A4Shard096.record12332 = true := by
  decide

def missing12333 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20573287866894909440
theorem maskCheck12333 :
    checkMaskFor missing12333 StrongPackedBucketN12A4Shard096.record12333 = true := by
  decide

def missing12334 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20645345460932837376
theorem maskCheck12334 :
    checkMaskFor missing12334 StrongPackedBucketN12A4Shard096.record12334 = true := by
  decide

def missing12335 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22158554935729324032
theorem maskCheck12335 :
    checkMaskFor missing12335 StrongPackedBucketN12A4Shard096.record12335 = true := by
  decide

def missing12336 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22302670123805179904
theorem maskCheck12336 :
    checkMaskFor missing12336 StrongPackedBucketN12A4Shard096.record12336 = true := by
  decide

def missing12337 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22374727717843107840
theorem maskCheck12337 :
    checkMaskFor missing12337 StrongPackedBucketN12A4Shard096.record12337 = true := by
  decide

def missing12338 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22807073282070675456
theorem maskCheck12338 :
    checkMaskFor missing12338 StrongPackedBucketN12A4Shard096.record12338 = true := by
  decide

def missing12339 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23599706816487882752
theorem maskCheck12339 :
    checkMaskFor missing12339 StrongPackedBucketN12A4Shard096.record12339 = true := by
  decide

def missing12340 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24104109974753378304
theorem maskCheck12340 :
    checkMaskFor missing12340 StrongPackedBucketN12A4Shard096.record12340 = true := by
  decide

def missing12341 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24464397944943017984
theorem maskCheck12341 :
    checkMaskFor missing12341 StrongPackedBucketN12A4Shard096.record12341 = true := by
  decide

def missing12342 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24680570727056801792
theorem maskCheck12342 :
    checkMaskFor missing12342 StrongPackedBucketN12A4Shard096.record12342 = true := by
  decide

def missing12343 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 26698183360118784000
theorem maskCheck12343 :
    checkMaskFor missing12343 StrongPackedBucketN12A4Shard096.record12343 = true := by
  decide

def missing12344 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28211392834915270656
theorem maskCheck12344 :
    checkMaskFor missing12344 StrongPackedBucketN12A4Shard096.record12344 = true := by
  decide

def missing12345 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28643738399142838272
theorem maskCheck12345 :
    checkMaskFor missing12345 StrongPackedBucketN12A4Shard096.record12345 = true := by
  decide

def missing12346 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29076083963370405888
theorem maskCheck12346 :
    checkMaskFor missing12346 StrongPackedBucketN12A4Shard096.record12346 = true := by
  decide

def missing12347 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29220199151446261760
theorem maskCheck12347 :
    checkMaskFor missing12347 StrongPackedBucketN12A4Shard096.record12347 = true := by
  decide

def missing12348 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 31237811784508243968
theorem maskCheck12348 :
    checkMaskFor missing12348 StrongPackedBucketN12A4Shard096.record12348 = true := by
  decide

def missing12349 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32534848477190946816
theorem maskCheck12349 :
    checkMaskFor missing12349 StrongPackedBucketN12A4Shard096.record12349 = true := by
  decide

def missing12350 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38011225624073469952
theorem maskCheck12350 :
    checkMaskFor missing12350 StrongPackedBucketN12A4Shard096.record12350 = true := by
  decide

def missing12351 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38587686376376893440
theorem maskCheck12351 :
    checkMaskFor missing12351 StrongPackedBucketN12A4Shard096.record12351 = true := by
  decide

def missing12352 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39020031940604461056
theorem maskCheck12352 :
    checkMaskFor missing12352 StrongPackedBucketN12A4Shard096.record12352 = true := by
  decide

def missing12353 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39092089534642388992
theorem maskCheck12353 :
    checkMaskFor missing12353 StrongPackedBucketN12A4Shard096.record12353 = true := by
  decide

def missing12354 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39128118331661352960
theorem maskCheck12354 :
    checkMaskFor missing12354 StrongPackedBucketN12A4Shard096.record12354 = true := by
  decide

def missing12355 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40605299009438875648
theorem maskCheck12355 :
    checkMaskFor missing12355 StrongPackedBucketN12A4Shard096.record12355 = true := by
  decide

def missing12356 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40749414197514731520
theorem maskCheck12356 :
    checkMaskFor missing12356 StrongPackedBucketN12A4Shard096.record12356 = true := by
  decide

def missing12357 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40821471791552659456
theorem maskCheck12357 :
    checkMaskFor missing12357 StrongPackedBucketN12A4Shard096.record12357 = true := by
  decide

def missing12358 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40857500588571623424
theorem maskCheck12358 :
    checkMaskFor missing12358 StrongPackedBucketN12A4Shard096.record12358 = true := by
  decide

def missing12359 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41253817355780227072
theorem maskCheck12359 :
    checkMaskFor missing12359 StrongPackedBucketN12A4Shard096.record12359 = true := by
  decide

def missing12360 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41289846152799191040
theorem maskCheck12360 :
    checkMaskFor missing12360 StrongPackedBucketN12A4Shard096.record12360 = true := by
  decide

def missing12361 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41361903746837118976
theorem maskCheck12361 :
    checkMaskFor missing12361 StrongPackedBucketN12A4Shard096.record12361 = true := by
  decide

def missing12362 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42046450890197434368
theorem maskCheck12362 :
    checkMaskFor missing12362 StrongPackedBucketN12A4Shard096.record12362 = true := by
  decide

def missing12363 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42478796454425001984
theorem maskCheck12363 :
    checkMaskFor missing12363 StrongPackedBucketN12A4Shard096.record12363 = true := by
  decide

def missing12364 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42550854048462929920
theorem maskCheck12364 :
    checkMaskFor missing12364 StrongPackedBucketN12A4Shard096.record12364 = true := by
  decide

def missing12365 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42586882845481893888
theorem maskCheck12365 :
    checkMaskFor missing12365 StrongPackedBucketN12A4Shard096.record12365 = true := by
  decide

def missing12366 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42911142018652569600
theorem maskCheck12366 :
    checkMaskFor missing12366 StrongPackedBucketN12A4Shard096.record12366 = true := by
  decide

def missing12367 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43055257206728425472
theorem maskCheck12367 :
    checkMaskFor missing12367 StrongPackedBucketN12A4Shard096.record12367 = true := by
  decide

def missing12368 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43127314800766353408
theorem maskCheck12368 :
    checkMaskFor missing12368 StrongPackedBucketN12A4Shard096.record12368 = true := by
  decide

def missing12369 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43163343597785317376
theorem maskCheck12369 :
    checkMaskFor missing12369 StrongPackedBucketN12A4Shard096.record12369 = true := by
  decide

def missing12370 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43559660364993921024
theorem maskCheck12370 :
    checkMaskFor missing12370 StrongPackedBucketN12A4Shard096.record12370 = true := by
  decide

def missing12371 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43667746756050812928
theorem maskCheck12371 :
    checkMaskFor missing12371 StrongPackedBucketN12A4Shard096.record12371 = true := by
  decide

def missing12372 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45072869839790407680
theorem maskCheck12372 :
    checkMaskFor missing12372 StrongPackedBucketN12A4Shard096.record12372 = true := by
  decide

def missing12373 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45144927433828335616
theorem maskCheck12373 :
    checkMaskFor missing12373 StrongPackedBucketN12A4Shard096.record12373 = true := by
  decide

def missing12374 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45180956230847299584
theorem maskCheck12374 :
    checkMaskFor missing12374 StrongPackedBucketN12A4Shard096.record12374 = true := by
  decide

def missing12375 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45289042621904191488
theorem maskCheck12375 :
    checkMaskFor missing12375 StrongPackedBucketN12A4Shard096.record12375 = true := by
  decide

def missing12376 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45397129012961083392
theorem maskCheck12376 :
    checkMaskFor missing12376 StrongPackedBucketN12A4Shard096.record12376 = true := by
  decide

def missing12377 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46658136908624822272
theorem maskCheck12377 :
    checkMaskFor missing12377 StrongPackedBucketN12A4Shard096.record12377 = true := by
  decide

def missing12378 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47090482472852389888
theorem maskCheck12378 :
    checkMaskFor missing12378 StrongPackedBucketN12A4Shard096.record12378 = true := by
  decide

def missing12379 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47198568863909281792
theorem maskCheck12379 :
    checkMaskFor missing12379 StrongPackedBucketN12A4Shard096.record12379 = true := by
  decide

def missing12380 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47522828037079957504
theorem maskCheck12380 :
    checkMaskFor missing12380 StrongPackedBucketN12A4Shard096.record12380 = true := by
  decide

def missing12381 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47666943225155813376
theorem maskCheck12381 :
    checkMaskFor missing12381 StrongPackedBucketN12A4Shard096.record12381 = true := by
  decide

def missing12382 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47775029616212705280
theorem maskCheck12382 :
    checkMaskFor missing12382 StrongPackedBucketN12A4Shard096.record12382 = true := by
  decide

def missing12383 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48207375180440272896
theorem maskCheck12383 :
    checkMaskFor missing12383 StrongPackedBucketN12A4Shard096.record12383 = true := by
  decide

def missing12384 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49684555858217795584
theorem maskCheck12384 :
    checkMaskFor missing12384 StrongPackedBucketN12A4Shard096.record12384 = true := by
  decide

def missing12385 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49792642249274687488
theorem maskCheck12385 :
    checkMaskFor missing12385 StrongPackedBucketN12A4Shard096.record12385 = true := by
  decide

def missing12386 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49936757437350543360
theorem maskCheck12386 :
    checkMaskFor missing12386 StrongPackedBucketN12A4Shard096.record12386 = true := by
  decide

def missing12387 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50981592550900498432
theorem maskCheck12387 :
    checkMaskFor missing12387 StrongPackedBucketN12A4Shard096.record12387 = true := by
  decide

def missing12388 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51125707738976354304
theorem maskCheck12388 :
    checkMaskFor missing12388 StrongPackedBucketN12A4Shard096.record12388 = true := by
  decide

def missing12389 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51233794130033246208
theorem maskCheck12389 :
    checkMaskFor missing12389 StrongPackedBucketN12A4Shard096.record12389 = true := by
  decide

def missing12390 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51990398867431489536
theorem maskCheck12390 :
    checkMaskFor missing12390 StrongPackedBucketN12A4Shard096.record12390 = true := by
  decide

def missing12391 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 52098485258488381440
theorem maskCheck12391 :
    checkMaskFor missing12391 StrongPackedBucketN12A4Shard096.record12391 = true := by
  decide

def missing12392 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55881508945479598080
theorem maskCheck12392 :
    checkMaskFor missing12392 StrongPackedBucketN12A4Shard096.record12392 = true := by
  decide

def missing12393 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56313854509707165696
theorem maskCheck12393 :
    checkMaskFor missing12393 StrongPackedBucketN12A4Shard096.record12393 = true := by
  decide

def missing12394 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56385912103745093632
theorem maskCheck12394 :
    checkMaskFor missing12394 StrongPackedBucketN12A4Shard096.record12394 = true := by
  decide

def missing12395 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56746200073934733312
theorem maskCheck12395 :
    checkMaskFor missing12395 StrongPackedBucketN12A4Shard096.record12395 = true := by
  decide

def missing12396 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56890315262010589184
theorem maskCheck12396 :
    checkMaskFor missing12396 StrongPackedBucketN12A4Shard096.record12396 = true := by
  decide

def missing12397 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56962372856048517120
theorem maskCheck12397 :
    checkMaskFor missing12397 StrongPackedBucketN12A4Shard096.record12397 = true := by
  decide

def missing12398 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57394718420276084736
theorem maskCheck12398 :
    checkMaskFor missing12398 StrongPackedBucketN12A4Shard096.record12398 = true := by
  decide

def missing12399 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58907927895072571392
theorem maskCheck12399 :
    checkMaskFor missing12399 StrongPackedBucketN12A4Shard096.record12399 = true := by
  decide

def missing12400 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58979985489110499328
theorem maskCheck12400 :
    checkMaskFor missing12400 StrongPackedBucketN12A4Shard096.record12400 = true := by
  decide

def missing12401 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59124100677186355200
theorem maskCheck12401 :
    checkMaskFor missing12401 StrongPackedBucketN12A4Shard096.record12401 = true := by
  decide

def missing12402 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60204964587755274240
theorem maskCheck12402 :
    checkMaskFor missing12402 StrongPackedBucketN12A4Shard096.record12402 = true := by
  decide

def missing12403 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60421137369869058048
theorem maskCheck12403 :
    checkMaskFor missing12403 StrongPackedBucketN12A4Shard096.record12403 = true := by
  decide

def missing12404 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 61285828498324193280
theorem maskCheck12404 :
    checkMaskFor missing12404 StrongPackedBucketN12A4Shard096.record12404 = true := by
  decide

def missing12405 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64816650606182662144
theorem maskCheck12405 :
    checkMaskFor missing12405 StrongPackedBucketN12A4Shard096.record12405 = true := by
  decide

def missing12406 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64960765794258518016
theorem maskCheck12406 :
    checkMaskFor missing12406 StrongPackedBucketN12A4Shard096.record12406 = true := by
  decide

def missing12407 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65825456922713653248
theorem maskCheck12407 :
    checkMaskFor missing12407 StrongPackedBucketN12A4Shard096.record12407 = true := by
  decide

def missing12408 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2274458893446807552
theorem maskCheck12408 :
    checkMaskFor missing12408 StrongPackedBucketN12A4Shard096.record12408 = true := by
  decide

def missing12409 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4436186714584645632
theorem maskCheck12409 :
    checkMaskFor missing12409 StrongPackedBucketN12A4Shard096.record12409 = true := by
  decide

def missing12410 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4508244308622573568
theorem maskCheck12410 :
    checkMaskFor missing12410 StrongPackedBucketN12A4Shard096.record12410 = true := by
  decide

def missing12411 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5733223407267348480
theorem maskCheck12411 :
    checkMaskFor missing12411 StrongPackedBucketN12A4Shard096.record12411 = true := by
  decide

def missing12412 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6742029723798339584
theorem maskCheck12412 :
    checkMaskFor missing12412 StrongPackedBucketN12A4Shard096.record12412 = true := by
  decide

def missing12413 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6814087317836267520
theorem maskCheck12413 :
    checkMaskFor missing12413 StrongPackedBucketN12A4Shard096.record12413 = true := by
  decide

def missing12414 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8975815138974105600
theorem maskCheck12414 :
    checkMaskFor missing12414 StrongPackedBucketN12A4Shard096.record12414 = true := by
  decide

def missing12415 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10344909425694736384
theorem maskCheck12415 :
    checkMaskFor missing12415 StrongPackedBucketN12A4Shard096.record12415 = true := by
  decide

def missing12288_12289 : List (BitVec (edgeCount 12)) :=
  [missing12288]
abbrev records12288_12289 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12288]
theorem aligned12288_12289 :
    AlignedValid 12 4 missing12288_12289 records12288_12289 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12288
    maskCheck12288 AlignedValid.nil

def missing12289_12290 : List (BitVec (edgeCount 12)) :=
  [missing12289]
abbrev records12289_12290 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12289]
theorem aligned12289_12290 :
    AlignedValid 12 4 missing12289_12290 records12289_12290 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12289
    maskCheck12289 AlignedValid.nil

def missing12288_12290 : List (BitVec (edgeCount 12)) :=
  missing12288_12289 ++ missing12289_12290
abbrev records12288_12290 : List Blob :=
  records12288_12289 ++ records12289_12290
theorem aligned12288_12290 :
    AlignedValid 12 4 missing12288_12290 records12288_12290 :=
  aligned12288_12289.append aligned12289_12290

def missing12290_12291 : List (BitVec (edgeCount 12)) :=
  [missing12290]
abbrev records12290_12291 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12290]
theorem aligned12290_12291 :
    AlignedValid 12 4 missing12290_12291 records12290_12291 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12290
    maskCheck12290 AlignedValid.nil

def missing12291_12292 : List (BitVec (edgeCount 12)) :=
  [missing12291]
abbrev records12291_12292 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12291]
theorem aligned12291_12292 :
    AlignedValid 12 4 missing12291_12292 records12291_12292 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12291
    maskCheck12291 AlignedValid.nil

def missing12290_12292 : List (BitVec (edgeCount 12)) :=
  missing12290_12291 ++ missing12291_12292
abbrev records12290_12292 : List Blob :=
  records12290_12291 ++ records12291_12292
theorem aligned12290_12292 :
    AlignedValid 12 4 missing12290_12292 records12290_12292 :=
  aligned12290_12291.append aligned12291_12292

def missing12288_12292 : List (BitVec (edgeCount 12)) :=
  missing12288_12290 ++ missing12290_12292
abbrev records12288_12292 : List Blob :=
  records12288_12290 ++ records12290_12292
theorem aligned12288_12292 :
    AlignedValid 12 4 missing12288_12292 records12288_12292 :=
  aligned12288_12290.append aligned12290_12292

def missing12292_12293 : List (BitVec (edgeCount 12)) :=
  [missing12292]
abbrev records12292_12293 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12292]
theorem aligned12292_12293 :
    AlignedValid 12 4 missing12292_12293 records12292_12293 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12292
    maskCheck12292 AlignedValid.nil

def missing12293_12294 : List (BitVec (edgeCount 12)) :=
  [missing12293]
abbrev records12293_12294 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12293]
theorem aligned12293_12294 :
    AlignedValid 12 4 missing12293_12294 records12293_12294 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12293
    maskCheck12293 AlignedValid.nil

def missing12292_12294 : List (BitVec (edgeCount 12)) :=
  missing12292_12293 ++ missing12293_12294
abbrev records12292_12294 : List Blob :=
  records12292_12293 ++ records12293_12294
theorem aligned12292_12294 :
    AlignedValid 12 4 missing12292_12294 records12292_12294 :=
  aligned12292_12293.append aligned12293_12294

def missing12294_12295 : List (BitVec (edgeCount 12)) :=
  [missing12294]
abbrev records12294_12295 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12294]
theorem aligned12294_12295 :
    AlignedValid 12 4 missing12294_12295 records12294_12295 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12294
    maskCheck12294 AlignedValid.nil

def missing12295_12296 : List (BitVec (edgeCount 12)) :=
  [missing12295]
abbrev records12295_12296 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12295]
theorem aligned12295_12296 :
    AlignedValid 12 4 missing12295_12296 records12295_12296 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12295
    maskCheck12295 AlignedValid.nil

def missing12294_12296 : List (BitVec (edgeCount 12)) :=
  missing12294_12295 ++ missing12295_12296
abbrev records12294_12296 : List Blob :=
  records12294_12295 ++ records12295_12296
theorem aligned12294_12296 :
    AlignedValid 12 4 missing12294_12296 records12294_12296 :=
  aligned12294_12295.append aligned12295_12296

def missing12292_12296 : List (BitVec (edgeCount 12)) :=
  missing12292_12294 ++ missing12294_12296
abbrev records12292_12296 : List Blob :=
  records12292_12294 ++ records12294_12296
theorem aligned12292_12296 :
    AlignedValid 12 4 missing12292_12296 records12292_12296 :=
  aligned12292_12294.append aligned12294_12296

def missing12288_12296 : List (BitVec (edgeCount 12)) :=
  missing12288_12292 ++ missing12292_12296
abbrev records12288_12296 : List Blob :=
  records12288_12292 ++ records12292_12296
theorem aligned12288_12296 :
    AlignedValid 12 4 missing12288_12296 records12288_12296 :=
  aligned12288_12292.append aligned12292_12296

def missing12296_12297 : List (BitVec (edgeCount 12)) :=
  [missing12296]
abbrev records12296_12297 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12296]
theorem aligned12296_12297 :
    AlignedValid 12 4 missing12296_12297 records12296_12297 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12296
    maskCheck12296 AlignedValid.nil

def missing12297_12298 : List (BitVec (edgeCount 12)) :=
  [missing12297]
abbrev records12297_12298 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12297]
theorem aligned12297_12298 :
    AlignedValid 12 4 missing12297_12298 records12297_12298 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12297
    maskCheck12297 AlignedValid.nil

def missing12296_12298 : List (BitVec (edgeCount 12)) :=
  missing12296_12297 ++ missing12297_12298
abbrev records12296_12298 : List Blob :=
  records12296_12297 ++ records12297_12298
theorem aligned12296_12298 :
    AlignedValid 12 4 missing12296_12298 records12296_12298 :=
  aligned12296_12297.append aligned12297_12298

def missing12298_12299 : List (BitVec (edgeCount 12)) :=
  [missing12298]
abbrev records12298_12299 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12298]
theorem aligned12298_12299 :
    AlignedValid 12 4 missing12298_12299 records12298_12299 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12298
    maskCheck12298 AlignedValid.nil

def missing12299_12300 : List (BitVec (edgeCount 12)) :=
  [missing12299]
abbrev records12299_12300 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12299]
theorem aligned12299_12300 :
    AlignedValid 12 4 missing12299_12300 records12299_12300 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12299
    maskCheck12299 AlignedValid.nil

def missing12298_12300 : List (BitVec (edgeCount 12)) :=
  missing12298_12299 ++ missing12299_12300
abbrev records12298_12300 : List Blob :=
  records12298_12299 ++ records12299_12300
theorem aligned12298_12300 :
    AlignedValid 12 4 missing12298_12300 records12298_12300 :=
  aligned12298_12299.append aligned12299_12300

def missing12296_12300 : List (BitVec (edgeCount 12)) :=
  missing12296_12298 ++ missing12298_12300
abbrev records12296_12300 : List Blob :=
  records12296_12298 ++ records12298_12300
theorem aligned12296_12300 :
    AlignedValid 12 4 missing12296_12300 records12296_12300 :=
  aligned12296_12298.append aligned12298_12300

def missing12300_12301 : List (BitVec (edgeCount 12)) :=
  [missing12300]
abbrev records12300_12301 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12300]
theorem aligned12300_12301 :
    AlignedValid 12 4 missing12300_12301 records12300_12301 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12300
    maskCheck12300 AlignedValid.nil

def missing12301_12302 : List (BitVec (edgeCount 12)) :=
  [missing12301]
abbrev records12301_12302 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12301]
theorem aligned12301_12302 :
    AlignedValid 12 4 missing12301_12302 records12301_12302 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12301
    maskCheck12301 AlignedValid.nil

def missing12300_12302 : List (BitVec (edgeCount 12)) :=
  missing12300_12301 ++ missing12301_12302
abbrev records12300_12302 : List Blob :=
  records12300_12301 ++ records12301_12302
theorem aligned12300_12302 :
    AlignedValid 12 4 missing12300_12302 records12300_12302 :=
  aligned12300_12301.append aligned12301_12302

def missing12302_12303 : List (BitVec (edgeCount 12)) :=
  [missing12302]
abbrev records12302_12303 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12302]
theorem aligned12302_12303 :
    AlignedValid 12 4 missing12302_12303 records12302_12303 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12302
    maskCheck12302 AlignedValid.nil

def missing12303_12304 : List (BitVec (edgeCount 12)) :=
  [missing12303]
abbrev records12303_12304 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12303]
theorem aligned12303_12304 :
    AlignedValid 12 4 missing12303_12304 records12303_12304 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12303
    maskCheck12303 AlignedValid.nil

def missing12302_12304 : List (BitVec (edgeCount 12)) :=
  missing12302_12303 ++ missing12303_12304
abbrev records12302_12304 : List Blob :=
  records12302_12303 ++ records12303_12304
theorem aligned12302_12304 :
    AlignedValid 12 4 missing12302_12304 records12302_12304 :=
  aligned12302_12303.append aligned12303_12304

def missing12300_12304 : List (BitVec (edgeCount 12)) :=
  missing12300_12302 ++ missing12302_12304
abbrev records12300_12304 : List Blob :=
  records12300_12302 ++ records12302_12304
theorem aligned12300_12304 :
    AlignedValid 12 4 missing12300_12304 records12300_12304 :=
  aligned12300_12302.append aligned12302_12304

def missing12296_12304 : List (BitVec (edgeCount 12)) :=
  missing12296_12300 ++ missing12300_12304
abbrev records12296_12304 : List Blob :=
  records12296_12300 ++ records12300_12304
theorem aligned12296_12304 :
    AlignedValid 12 4 missing12296_12304 records12296_12304 :=
  aligned12296_12300.append aligned12300_12304

def missing12288_12304 : List (BitVec (edgeCount 12)) :=
  missing12288_12296 ++ missing12296_12304
abbrev records12288_12304 : List Blob :=
  records12288_12296 ++ records12296_12304
theorem aligned12288_12304 :
    AlignedValid 12 4 missing12288_12304 records12288_12304 :=
  aligned12288_12296.append aligned12296_12304

def missing12304_12305 : List (BitVec (edgeCount 12)) :=
  [missing12304]
abbrev records12304_12305 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12304]
theorem aligned12304_12305 :
    AlignedValid 12 4 missing12304_12305 records12304_12305 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12304
    maskCheck12304 AlignedValid.nil

def missing12305_12306 : List (BitVec (edgeCount 12)) :=
  [missing12305]
abbrev records12305_12306 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12305]
theorem aligned12305_12306 :
    AlignedValid 12 4 missing12305_12306 records12305_12306 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12305
    maskCheck12305 AlignedValid.nil

def missing12304_12306 : List (BitVec (edgeCount 12)) :=
  missing12304_12305 ++ missing12305_12306
abbrev records12304_12306 : List Blob :=
  records12304_12305 ++ records12305_12306
theorem aligned12304_12306 :
    AlignedValid 12 4 missing12304_12306 records12304_12306 :=
  aligned12304_12305.append aligned12305_12306

def missing12306_12307 : List (BitVec (edgeCount 12)) :=
  [missing12306]
abbrev records12306_12307 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12306]
theorem aligned12306_12307 :
    AlignedValid 12 4 missing12306_12307 records12306_12307 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12306
    maskCheck12306 AlignedValid.nil

def missing12307_12308 : List (BitVec (edgeCount 12)) :=
  [missing12307]
abbrev records12307_12308 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12307]
theorem aligned12307_12308 :
    AlignedValid 12 4 missing12307_12308 records12307_12308 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12307
    maskCheck12307 AlignedValid.nil

def missing12306_12308 : List (BitVec (edgeCount 12)) :=
  missing12306_12307 ++ missing12307_12308
abbrev records12306_12308 : List Blob :=
  records12306_12307 ++ records12307_12308
theorem aligned12306_12308 :
    AlignedValid 12 4 missing12306_12308 records12306_12308 :=
  aligned12306_12307.append aligned12307_12308

def missing12304_12308 : List (BitVec (edgeCount 12)) :=
  missing12304_12306 ++ missing12306_12308
abbrev records12304_12308 : List Blob :=
  records12304_12306 ++ records12306_12308
theorem aligned12304_12308 :
    AlignedValid 12 4 missing12304_12308 records12304_12308 :=
  aligned12304_12306.append aligned12306_12308

def missing12308_12309 : List (BitVec (edgeCount 12)) :=
  [missing12308]
abbrev records12308_12309 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12308]
theorem aligned12308_12309 :
    AlignedValid 12 4 missing12308_12309 records12308_12309 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12308
    maskCheck12308 AlignedValid.nil

def missing12309_12310 : List (BitVec (edgeCount 12)) :=
  [missing12309]
abbrev records12309_12310 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12309]
theorem aligned12309_12310 :
    AlignedValid 12 4 missing12309_12310 records12309_12310 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12309
    maskCheck12309 AlignedValid.nil

def missing12308_12310 : List (BitVec (edgeCount 12)) :=
  missing12308_12309 ++ missing12309_12310
abbrev records12308_12310 : List Blob :=
  records12308_12309 ++ records12309_12310
theorem aligned12308_12310 :
    AlignedValid 12 4 missing12308_12310 records12308_12310 :=
  aligned12308_12309.append aligned12309_12310

def missing12310_12311 : List (BitVec (edgeCount 12)) :=
  [missing12310]
abbrev records12310_12311 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12310]
theorem aligned12310_12311 :
    AlignedValid 12 4 missing12310_12311 records12310_12311 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12310
    maskCheck12310 AlignedValid.nil

def missing12311_12312 : List (BitVec (edgeCount 12)) :=
  [missing12311]
abbrev records12311_12312 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12311]
theorem aligned12311_12312 :
    AlignedValid 12 4 missing12311_12312 records12311_12312 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12311
    maskCheck12311 AlignedValid.nil

def missing12310_12312 : List (BitVec (edgeCount 12)) :=
  missing12310_12311 ++ missing12311_12312
abbrev records12310_12312 : List Blob :=
  records12310_12311 ++ records12311_12312
theorem aligned12310_12312 :
    AlignedValid 12 4 missing12310_12312 records12310_12312 :=
  aligned12310_12311.append aligned12311_12312

def missing12308_12312 : List (BitVec (edgeCount 12)) :=
  missing12308_12310 ++ missing12310_12312
abbrev records12308_12312 : List Blob :=
  records12308_12310 ++ records12310_12312
theorem aligned12308_12312 :
    AlignedValid 12 4 missing12308_12312 records12308_12312 :=
  aligned12308_12310.append aligned12310_12312

def missing12304_12312 : List (BitVec (edgeCount 12)) :=
  missing12304_12308 ++ missing12308_12312
abbrev records12304_12312 : List Blob :=
  records12304_12308 ++ records12308_12312
theorem aligned12304_12312 :
    AlignedValid 12 4 missing12304_12312 records12304_12312 :=
  aligned12304_12308.append aligned12308_12312

def missing12312_12313 : List (BitVec (edgeCount 12)) :=
  [missing12312]
abbrev records12312_12313 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12312]
theorem aligned12312_12313 :
    AlignedValid 12 4 missing12312_12313 records12312_12313 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12312
    maskCheck12312 AlignedValid.nil

def missing12313_12314 : List (BitVec (edgeCount 12)) :=
  [missing12313]
abbrev records12313_12314 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12313]
theorem aligned12313_12314 :
    AlignedValid 12 4 missing12313_12314 records12313_12314 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12313
    maskCheck12313 AlignedValid.nil

def missing12312_12314 : List (BitVec (edgeCount 12)) :=
  missing12312_12313 ++ missing12313_12314
abbrev records12312_12314 : List Blob :=
  records12312_12313 ++ records12313_12314
theorem aligned12312_12314 :
    AlignedValid 12 4 missing12312_12314 records12312_12314 :=
  aligned12312_12313.append aligned12313_12314

def missing12314_12315 : List (BitVec (edgeCount 12)) :=
  [missing12314]
abbrev records12314_12315 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12314]
theorem aligned12314_12315 :
    AlignedValid 12 4 missing12314_12315 records12314_12315 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12314
    maskCheck12314 AlignedValid.nil

def missing12315_12316 : List (BitVec (edgeCount 12)) :=
  [missing12315]
abbrev records12315_12316 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12315]
theorem aligned12315_12316 :
    AlignedValid 12 4 missing12315_12316 records12315_12316 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12315
    maskCheck12315 AlignedValid.nil

def missing12314_12316 : List (BitVec (edgeCount 12)) :=
  missing12314_12315 ++ missing12315_12316
abbrev records12314_12316 : List Blob :=
  records12314_12315 ++ records12315_12316
theorem aligned12314_12316 :
    AlignedValid 12 4 missing12314_12316 records12314_12316 :=
  aligned12314_12315.append aligned12315_12316

def missing12312_12316 : List (BitVec (edgeCount 12)) :=
  missing12312_12314 ++ missing12314_12316
abbrev records12312_12316 : List Blob :=
  records12312_12314 ++ records12314_12316
theorem aligned12312_12316 :
    AlignedValid 12 4 missing12312_12316 records12312_12316 :=
  aligned12312_12314.append aligned12314_12316

def missing12316_12317 : List (BitVec (edgeCount 12)) :=
  [missing12316]
abbrev records12316_12317 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12316]
theorem aligned12316_12317 :
    AlignedValid 12 4 missing12316_12317 records12316_12317 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12316
    maskCheck12316 AlignedValid.nil

def missing12317_12318 : List (BitVec (edgeCount 12)) :=
  [missing12317]
abbrev records12317_12318 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12317]
theorem aligned12317_12318 :
    AlignedValid 12 4 missing12317_12318 records12317_12318 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12317
    maskCheck12317 AlignedValid.nil

def missing12316_12318 : List (BitVec (edgeCount 12)) :=
  missing12316_12317 ++ missing12317_12318
abbrev records12316_12318 : List Blob :=
  records12316_12317 ++ records12317_12318
theorem aligned12316_12318 :
    AlignedValid 12 4 missing12316_12318 records12316_12318 :=
  aligned12316_12317.append aligned12317_12318

def missing12318_12319 : List (BitVec (edgeCount 12)) :=
  [missing12318]
abbrev records12318_12319 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12318]
theorem aligned12318_12319 :
    AlignedValid 12 4 missing12318_12319 records12318_12319 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12318
    maskCheck12318 AlignedValid.nil

def missing12319_12320 : List (BitVec (edgeCount 12)) :=
  [missing12319]
abbrev records12319_12320 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12319]
theorem aligned12319_12320 :
    AlignedValid 12 4 missing12319_12320 records12319_12320 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12319
    maskCheck12319 AlignedValid.nil

def missing12318_12320 : List (BitVec (edgeCount 12)) :=
  missing12318_12319 ++ missing12319_12320
abbrev records12318_12320 : List Blob :=
  records12318_12319 ++ records12319_12320
theorem aligned12318_12320 :
    AlignedValid 12 4 missing12318_12320 records12318_12320 :=
  aligned12318_12319.append aligned12319_12320

def missing12316_12320 : List (BitVec (edgeCount 12)) :=
  missing12316_12318 ++ missing12318_12320
abbrev records12316_12320 : List Blob :=
  records12316_12318 ++ records12318_12320
theorem aligned12316_12320 :
    AlignedValid 12 4 missing12316_12320 records12316_12320 :=
  aligned12316_12318.append aligned12318_12320

def missing12312_12320 : List (BitVec (edgeCount 12)) :=
  missing12312_12316 ++ missing12316_12320
abbrev records12312_12320 : List Blob :=
  records12312_12316 ++ records12316_12320
theorem aligned12312_12320 :
    AlignedValid 12 4 missing12312_12320 records12312_12320 :=
  aligned12312_12316.append aligned12316_12320

def missing12304_12320 : List (BitVec (edgeCount 12)) :=
  missing12304_12312 ++ missing12312_12320
abbrev records12304_12320 : List Blob :=
  records12304_12312 ++ records12312_12320
theorem aligned12304_12320 :
    AlignedValid 12 4 missing12304_12320 records12304_12320 :=
  aligned12304_12312.append aligned12312_12320

def missing12288_12320 : List (BitVec (edgeCount 12)) :=
  missing12288_12304 ++ missing12304_12320
abbrev records12288_12320 : List Blob :=
  records12288_12304 ++ records12304_12320
theorem aligned12288_12320 :
    AlignedValid 12 4 missing12288_12320 records12288_12320 :=
  aligned12288_12304.append aligned12304_12320

def missing12320_12321 : List (BitVec (edgeCount 12)) :=
  [missing12320]
abbrev records12320_12321 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12320]
theorem aligned12320_12321 :
    AlignedValid 12 4 missing12320_12321 records12320_12321 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12320
    maskCheck12320 AlignedValid.nil

def missing12321_12322 : List (BitVec (edgeCount 12)) :=
  [missing12321]
abbrev records12321_12322 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12321]
theorem aligned12321_12322 :
    AlignedValid 12 4 missing12321_12322 records12321_12322 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12321
    maskCheck12321 AlignedValid.nil

def missing12320_12322 : List (BitVec (edgeCount 12)) :=
  missing12320_12321 ++ missing12321_12322
abbrev records12320_12322 : List Blob :=
  records12320_12321 ++ records12321_12322
theorem aligned12320_12322 :
    AlignedValid 12 4 missing12320_12322 records12320_12322 :=
  aligned12320_12321.append aligned12321_12322

def missing12322_12323 : List (BitVec (edgeCount 12)) :=
  [missing12322]
abbrev records12322_12323 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12322]
theorem aligned12322_12323 :
    AlignedValid 12 4 missing12322_12323 records12322_12323 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12322
    maskCheck12322 AlignedValid.nil

def missing12323_12324 : List (BitVec (edgeCount 12)) :=
  [missing12323]
abbrev records12323_12324 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12323]
theorem aligned12323_12324 :
    AlignedValid 12 4 missing12323_12324 records12323_12324 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12323
    maskCheck12323 AlignedValid.nil

def missing12322_12324 : List (BitVec (edgeCount 12)) :=
  missing12322_12323 ++ missing12323_12324
abbrev records12322_12324 : List Blob :=
  records12322_12323 ++ records12323_12324
theorem aligned12322_12324 :
    AlignedValid 12 4 missing12322_12324 records12322_12324 :=
  aligned12322_12323.append aligned12323_12324

def missing12320_12324 : List (BitVec (edgeCount 12)) :=
  missing12320_12322 ++ missing12322_12324
abbrev records12320_12324 : List Blob :=
  records12320_12322 ++ records12322_12324
theorem aligned12320_12324 :
    AlignedValid 12 4 missing12320_12324 records12320_12324 :=
  aligned12320_12322.append aligned12322_12324

def missing12324_12325 : List (BitVec (edgeCount 12)) :=
  [missing12324]
abbrev records12324_12325 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12324]
theorem aligned12324_12325 :
    AlignedValid 12 4 missing12324_12325 records12324_12325 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12324
    maskCheck12324 AlignedValid.nil

def missing12325_12326 : List (BitVec (edgeCount 12)) :=
  [missing12325]
abbrev records12325_12326 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12325]
theorem aligned12325_12326 :
    AlignedValid 12 4 missing12325_12326 records12325_12326 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12325
    maskCheck12325 AlignedValid.nil

def missing12324_12326 : List (BitVec (edgeCount 12)) :=
  missing12324_12325 ++ missing12325_12326
abbrev records12324_12326 : List Blob :=
  records12324_12325 ++ records12325_12326
theorem aligned12324_12326 :
    AlignedValid 12 4 missing12324_12326 records12324_12326 :=
  aligned12324_12325.append aligned12325_12326

def missing12326_12327 : List (BitVec (edgeCount 12)) :=
  [missing12326]
abbrev records12326_12327 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12326]
theorem aligned12326_12327 :
    AlignedValid 12 4 missing12326_12327 records12326_12327 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12326
    maskCheck12326 AlignedValid.nil

def missing12327_12328 : List (BitVec (edgeCount 12)) :=
  [missing12327]
abbrev records12327_12328 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12327]
theorem aligned12327_12328 :
    AlignedValid 12 4 missing12327_12328 records12327_12328 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12327
    maskCheck12327 AlignedValid.nil

def missing12326_12328 : List (BitVec (edgeCount 12)) :=
  missing12326_12327 ++ missing12327_12328
abbrev records12326_12328 : List Blob :=
  records12326_12327 ++ records12327_12328
theorem aligned12326_12328 :
    AlignedValid 12 4 missing12326_12328 records12326_12328 :=
  aligned12326_12327.append aligned12327_12328

def missing12324_12328 : List (BitVec (edgeCount 12)) :=
  missing12324_12326 ++ missing12326_12328
abbrev records12324_12328 : List Blob :=
  records12324_12326 ++ records12326_12328
theorem aligned12324_12328 :
    AlignedValid 12 4 missing12324_12328 records12324_12328 :=
  aligned12324_12326.append aligned12326_12328

def missing12320_12328 : List (BitVec (edgeCount 12)) :=
  missing12320_12324 ++ missing12324_12328
abbrev records12320_12328 : List Blob :=
  records12320_12324 ++ records12324_12328
theorem aligned12320_12328 :
    AlignedValid 12 4 missing12320_12328 records12320_12328 :=
  aligned12320_12324.append aligned12324_12328

def missing12328_12329 : List (BitVec (edgeCount 12)) :=
  [missing12328]
abbrev records12328_12329 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12328]
theorem aligned12328_12329 :
    AlignedValid 12 4 missing12328_12329 records12328_12329 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12328
    maskCheck12328 AlignedValid.nil

def missing12329_12330 : List (BitVec (edgeCount 12)) :=
  [missing12329]
abbrev records12329_12330 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12329]
theorem aligned12329_12330 :
    AlignedValid 12 4 missing12329_12330 records12329_12330 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12329
    maskCheck12329 AlignedValid.nil

def missing12328_12330 : List (BitVec (edgeCount 12)) :=
  missing12328_12329 ++ missing12329_12330
abbrev records12328_12330 : List Blob :=
  records12328_12329 ++ records12329_12330
theorem aligned12328_12330 :
    AlignedValid 12 4 missing12328_12330 records12328_12330 :=
  aligned12328_12329.append aligned12329_12330

def missing12330_12331 : List (BitVec (edgeCount 12)) :=
  [missing12330]
abbrev records12330_12331 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12330]
theorem aligned12330_12331 :
    AlignedValid 12 4 missing12330_12331 records12330_12331 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12330
    maskCheck12330 AlignedValid.nil

def missing12331_12332 : List (BitVec (edgeCount 12)) :=
  [missing12331]
abbrev records12331_12332 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12331]
theorem aligned12331_12332 :
    AlignedValid 12 4 missing12331_12332 records12331_12332 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12331
    maskCheck12331 AlignedValid.nil

def missing12330_12332 : List (BitVec (edgeCount 12)) :=
  missing12330_12331 ++ missing12331_12332
abbrev records12330_12332 : List Blob :=
  records12330_12331 ++ records12331_12332
theorem aligned12330_12332 :
    AlignedValid 12 4 missing12330_12332 records12330_12332 :=
  aligned12330_12331.append aligned12331_12332

def missing12328_12332 : List (BitVec (edgeCount 12)) :=
  missing12328_12330 ++ missing12330_12332
abbrev records12328_12332 : List Blob :=
  records12328_12330 ++ records12330_12332
theorem aligned12328_12332 :
    AlignedValid 12 4 missing12328_12332 records12328_12332 :=
  aligned12328_12330.append aligned12330_12332

def missing12332_12333 : List (BitVec (edgeCount 12)) :=
  [missing12332]
abbrev records12332_12333 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12332]
theorem aligned12332_12333 :
    AlignedValid 12 4 missing12332_12333 records12332_12333 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12332
    maskCheck12332 AlignedValid.nil

def missing12333_12334 : List (BitVec (edgeCount 12)) :=
  [missing12333]
abbrev records12333_12334 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12333]
theorem aligned12333_12334 :
    AlignedValid 12 4 missing12333_12334 records12333_12334 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12333
    maskCheck12333 AlignedValid.nil

def missing12332_12334 : List (BitVec (edgeCount 12)) :=
  missing12332_12333 ++ missing12333_12334
abbrev records12332_12334 : List Blob :=
  records12332_12333 ++ records12333_12334
theorem aligned12332_12334 :
    AlignedValid 12 4 missing12332_12334 records12332_12334 :=
  aligned12332_12333.append aligned12333_12334

def missing12334_12335 : List (BitVec (edgeCount 12)) :=
  [missing12334]
abbrev records12334_12335 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12334]
theorem aligned12334_12335 :
    AlignedValid 12 4 missing12334_12335 records12334_12335 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12334
    maskCheck12334 AlignedValid.nil

def missing12335_12336 : List (BitVec (edgeCount 12)) :=
  [missing12335]
abbrev records12335_12336 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12335]
theorem aligned12335_12336 :
    AlignedValid 12 4 missing12335_12336 records12335_12336 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12335
    maskCheck12335 AlignedValid.nil

def missing12334_12336 : List (BitVec (edgeCount 12)) :=
  missing12334_12335 ++ missing12335_12336
abbrev records12334_12336 : List Blob :=
  records12334_12335 ++ records12335_12336
theorem aligned12334_12336 :
    AlignedValid 12 4 missing12334_12336 records12334_12336 :=
  aligned12334_12335.append aligned12335_12336

def missing12332_12336 : List (BitVec (edgeCount 12)) :=
  missing12332_12334 ++ missing12334_12336
abbrev records12332_12336 : List Blob :=
  records12332_12334 ++ records12334_12336
theorem aligned12332_12336 :
    AlignedValid 12 4 missing12332_12336 records12332_12336 :=
  aligned12332_12334.append aligned12334_12336

def missing12328_12336 : List (BitVec (edgeCount 12)) :=
  missing12328_12332 ++ missing12332_12336
abbrev records12328_12336 : List Blob :=
  records12328_12332 ++ records12332_12336
theorem aligned12328_12336 :
    AlignedValid 12 4 missing12328_12336 records12328_12336 :=
  aligned12328_12332.append aligned12332_12336

def missing12320_12336 : List (BitVec (edgeCount 12)) :=
  missing12320_12328 ++ missing12328_12336
abbrev records12320_12336 : List Blob :=
  records12320_12328 ++ records12328_12336
theorem aligned12320_12336 :
    AlignedValid 12 4 missing12320_12336 records12320_12336 :=
  aligned12320_12328.append aligned12328_12336

def missing12336_12337 : List (BitVec (edgeCount 12)) :=
  [missing12336]
abbrev records12336_12337 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12336]
theorem aligned12336_12337 :
    AlignedValid 12 4 missing12336_12337 records12336_12337 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12336
    maskCheck12336 AlignedValid.nil

def missing12337_12338 : List (BitVec (edgeCount 12)) :=
  [missing12337]
abbrev records12337_12338 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12337]
theorem aligned12337_12338 :
    AlignedValid 12 4 missing12337_12338 records12337_12338 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12337
    maskCheck12337 AlignedValid.nil

def missing12336_12338 : List (BitVec (edgeCount 12)) :=
  missing12336_12337 ++ missing12337_12338
abbrev records12336_12338 : List Blob :=
  records12336_12337 ++ records12337_12338
theorem aligned12336_12338 :
    AlignedValid 12 4 missing12336_12338 records12336_12338 :=
  aligned12336_12337.append aligned12337_12338

def missing12338_12339 : List (BitVec (edgeCount 12)) :=
  [missing12338]
abbrev records12338_12339 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12338]
theorem aligned12338_12339 :
    AlignedValid 12 4 missing12338_12339 records12338_12339 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12338
    maskCheck12338 AlignedValid.nil

def missing12339_12340 : List (BitVec (edgeCount 12)) :=
  [missing12339]
abbrev records12339_12340 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12339]
theorem aligned12339_12340 :
    AlignedValid 12 4 missing12339_12340 records12339_12340 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12339
    maskCheck12339 AlignedValid.nil

def missing12338_12340 : List (BitVec (edgeCount 12)) :=
  missing12338_12339 ++ missing12339_12340
abbrev records12338_12340 : List Blob :=
  records12338_12339 ++ records12339_12340
theorem aligned12338_12340 :
    AlignedValid 12 4 missing12338_12340 records12338_12340 :=
  aligned12338_12339.append aligned12339_12340

def missing12336_12340 : List (BitVec (edgeCount 12)) :=
  missing12336_12338 ++ missing12338_12340
abbrev records12336_12340 : List Blob :=
  records12336_12338 ++ records12338_12340
theorem aligned12336_12340 :
    AlignedValid 12 4 missing12336_12340 records12336_12340 :=
  aligned12336_12338.append aligned12338_12340

def missing12340_12341 : List (BitVec (edgeCount 12)) :=
  [missing12340]
abbrev records12340_12341 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12340]
theorem aligned12340_12341 :
    AlignedValid 12 4 missing12340_12341 records12340_12341 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12340
    maskCheck12340 AlignedValid.nil

def missing12341_12342 : List (BitVec (edgeCount 12)) :=
  [missing12341]
abbrev records12341_12342 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12341]
theorem aligned12341_12342 :
    AlignedValid 12 4 missing12341_12342 records12341_12342 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12341
    maskCheck12341 AlignedValid.nil

def missing12340_12342 : List (BitVec (edgeCount 12)) :=
  missing12340_12341 ++ missing12341_12342
abbrev records12340_12342 : List Blob :=
  records12340_12341 ++ records12341_12342
theorem aligned12340_12342 :
    AlignedValid 12 4 missing12340_12342 records12340_12342 :=
  aligned12340_12341.append aligned12341_12342

def missing12342_12343 : List (BitVec (edgeCount 12)) :=
  [missing12342]
abbrev records12342_12343 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12342]
theorem aligned12342_12343 :
    AlignedValid 12 4 missing12342_12343 records12342_12343 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12342
    maskCheck12342 AlignedValid.nil

def missing12343_12344 : List (BitVec (edgeCount 12)) :=
  [missing12343]
abbrev records12343_12344 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12343]
theorem aligned12343_12344 :
    AlignedValid 12 4 missing12343_12344 records12343_12344 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12343
    maskCheck12343 AlignedValid.nil

def missing12342_12344 : List (BitVec (edgeCount 12)) :=
  missing12342_12343 ++ missing12343_12344
abbrev records12342_12344 : List Blob :=
  records12342_12343 ++ records12343_12344
theorem aligned12342_12344 :
    AlignedValid 12 4 missing12342_12344 records12342_12344 :=
  aligned12342_12343.append aligned12343_12344

def missing12340_12344 : List (BitVec (edgeCount 12)) :=
  missing12340_12342 ++ missing12342_12344
abbrev records12340_12344 : List Blob :=
  records12340_12342 ++ records12342_12344
theorem aligned12340_12344 :
    AlignedValid 12 4 missing12340_12344 records12340_12344 :=
  aligned12340_12342.append aligned12342_12344

def missing12336_12344 : List (BitVec (edgeCount 12)) :=
  missing12336_12340 ++ missing12340_12344
abbrev records12336_12344 : List Blob :=
  records12336_12340 ++ records12340_12344
theorem aligned12336_12344 :
    AlignedValid 12 4 missing12336_12344 records12336_12344 :=
  aligned12336_12340.append aligned12340_12344

def missing12344_12345 : List (BitVec (edgeCount 12)) :=
  [missing12344]
abbrev records12344_12345 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12344]
theorem aligned12344_12345 :
    AlignedValid 12 4 missing12344_12345 records12344_12345 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12344
    maskCheck12344 AlignedValid.nil

def missing12345_12346 : List (BitVec (edgeCount 12)) :=
  [missing12345]
abbrev records12345_12346 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12345]
theorem aligned12345_12346 :
    AlignedValid 12 4 missing12345_12346 records12345_12346 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12345
    maskCheck12345 AlignedValid.nil

def missing12344_12346 : List (BitVec (edgeCount 12)) :=
  missing12344_12345 ++ missing12345_12346
abbrev records12344_12346 : List Blob :=
  records12344_12345 ++ records12345_12346
theorem aligned12344_12346 :
    AlignedValid 12 4 missing12344_12346 records12344_12346 :=
  aligned12344_12345.append aligned12345_12346

def missing12346_12347 : List (BitVec (edgeCount 12)) :=
  [missing12346]
abbrev records12346_12347 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12346]
theorem aligned12346_12347 :
    AlignedValid 12 4 missing12346_12347 records12346_12347 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12346
    maskCheck12346 AlignedValid.nil

def missing12347_12348 : List (BitVec (edgeCount 12)) :=
  [missing12347]
abbrev records12347_12348 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12347]
theorem aligned12347_12348 :
    AlignedValid 12 4 missing12347_12348 records12347_12348 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12347
    maskCheck12347 AlignedValid.nil

def missing12346_12348 : List (BitVec (edgeCount 12)) :=
  missing12346_12347 ++ missing12347_12348
abbrev records12346_12348 : List Blob :=
  records12346_12347 ++ records12347_12348
theorem aligned12346_12348 :
    AlignedValid 12 4 missing12346_12348 records12346_12348 :=
  aligned12346_12347.append aligned12347_12348

def missing12344_12348 : List (BitVec (edgeCount 12)) :=
  missing12344_12346 ++ missing12346_12348
abbrev records12344_12348 : List Blob :=
  records12344_12346 ++ records12346_12348
theorem aligned12344_12348 :
    AlignedValid 12 4 missing12344_12348 records12344_12348 :=
  aligned12344_12346.append aligned12346_12348

def missing12348_12349 : List (BitVec (edgeCount 12)) :=
  [missing12348]
abbrev records12348_12349 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12348]
theorem aligned12348_12349 :
    AlignedValid 12 4 missing12348_12349 records12348_12349 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12348
    maskCheck12348 AlignedValid.nil

def missing12349_12350 : List (BitVec (edgeCount 12)) :=
  [missing12349]
abbrev records12349_12350 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12349]
theorem aligned12349_12350 :
    AlignedValid 12 4 missing12349_12350 records12349_12350 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12349
    maskCheck12349 AlignedValid.nil

def missing12348_12350 : List (BitVec (edgeCount 12)) :=
  missing12348_12349 ++ missing12349_12350
abbrev records12348_12350 : List Blob :=
  records12348_12349 ++ records12349_12350
theorem aligned12348_12350 :
    AlignedValid 12 4 missing12348_12350 records12348_12350 :=
  aligned12348_12349.append aligned12349_12350

def missing12350_12351 : List (BitVec (edgeCount 12)) :=
  [missing12350]
abbrev records12350_12351 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12350]
theorem aligned12350_12351 :
    AlignedValid 12 4 missing12350_12351 records12350_12351 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12350
    maskCheck12350 AlignedValid.nil

def missing12351_12352 : List (BitVec (edgeCount 12)) :=
  [missing12351]
abbrev records12351_12352 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12351]
theorem aligned12351_12352 :
    AlignedValid 12 4 missing12351_12352 records12351_12352 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12351
    maskCheck12351 AlignedValid.nil

def missing12350_12352 : List (BitVec (edgeCount 12)) :=
  missing12350_12351 ++ missing12351_12352
abbrev records12350_12352 : List Blob :=
  records12350_12351 ++ records12351_12352
theorem aligned12350_12352 :
    AlignedValid 12 4 missing12350_12352 records12350_12352 :=
  aligned12350_12351.append aligned12351_12352

def missing12348_12352 : List (BitVec (edgeCount 12)) :=
  missing12348_12350 ++ missing12350_12352
abbrev records12348_12352 : List Blob :=
  records12348_12350 ++ records12350_12352
theorem aligned12348_12352 :
    AlignedValid 12 4 missing12348_12352 records12348_12352 :=
  aligned12348_12350.append aligned12350_12352

def missing12344_12352 : List (BitVec (edgeCount 12)) :=
  missing12344_12348 ++ missing12348_12352
abbrev records12344_12352 : List Blob :=
  records12344_12348 ++ records12348_12352
theorem aligned12344_12352 :
    AlignedValid 12 4 missing12344_12352 records12344_12352 :=
  aligned12344_12348.append aligned12348_12352

def missing12336_12352 : List (BitVec (edgeCount 12)) :=
  missing12336_12344 ++ missing12344_12352
abbrev records12336_12352 : List Blob :=
  records12336_12344 ++ records12344_12352
theorem aligned12336_12352 :
    AlignedValid 12 4 missing12336_12352 records12336_12352 :=
  aligned12336_12344.append aligned12344_12352

def missing12320_12352 : List (BitVec (edgeCount 12)) :=
  missing12320_12336 ++ missing12336_12352
abbrev records12320_12352 : List Blob :=
  records12320_12336 ++ records12336_12352
theorem aligned12320_12352 :
    AlignedValid 12 4 missing12320_12352 records12320_12352 :=
  aligned12320_12336.append aligned12336_12352

def missing12288_12352 : List (BitVec (edgeCount 12)) :=
  missing12288_12320 ++ missing12320_12352
abbrev records12288_12352 : List Blob :=
  records12288_12320 ++ records12320_12352
theorem aligned12288_12352 :
    AlignedValid 12 4 missing12288_12352 records12288_12352 :=
  aligned12288_12320.append aligned12320_12352

def missing12352_12353 : List (BitVec (edgeCount 12)) :=
  [missing12352]
abbrev records12352_12353 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12352]
theorem aligned12352_12353 :
    AlignedValid 12 4 missing12352_12353 records12352_12353 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12352
    maskCheck12352 AlignedValid.nil

def missing12353_12354 : List (BitVec (edgeCount 12)) :=
  [missing12353]
abbrev records12353_12354 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12353]
theorem aligned12353_12354 :
    AlignedValid 12 4 missing12353_12354 records12353_12354 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12353
    maskCheck12353 AlignedValid.nil

def missing12352_12354 : List (BitVec (edgeCount 12)) :=
  missing12352_12353 ++ missing12353_12354
abbrev records12352_12354 : List Blob :=
  records12352_12353 ++ records12353_12354
theorem aligned12352_12354 :
    AlignedValid 12 4 missing12352_12354 records12352_12354 :=
  aligned12352_12353.append aligned12353_12354

def missing12354_12355 : List (BitVec (edgeCount 12)) :=
  [missing12354]
abbrev records12354_12355 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12354]
theorem aligned12354_12355 :
    AlignedValid 12 4 missing12354_12355 records12354_12355 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12354
    maskCheck12354 AlignedValid.nil

def missing12355_12356 : List (BitVec (edgeCount 12)) :=
  [missing12355]
abbrev records12355_12356 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12355]
theorem aligned12355_12356 :
    AlignedValid 12 4 missing12355_12356 records12355_12356 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12355
    maskCheck12355 AlignedValid.nil

def missing12354_12356 : List (BitVec (edgeCount 12)) :=
  missing12354_12355 ++ missing12355_12356
abbrev records12354_12356 : List Blob :=
  records12354_12355 ++ records12355_12356
theorem aligned12354_12356 :
    AlignedValid 12 4 missing12354_12356 records12354_12356 :=
  aligned12354_12355.append aligned12355_12356

def missing12352_12356 : List (BitVec (edgeCount 12)) :=
  missing12352_12354 ++ missing12354_12356
abbrev records12352_12356 : List Blob :=
  records12352_12354 ++ records12354_12356
theorem aligned12352_12356 :
    AlignedValid 12 4 missing12352_12356 records12352_12356 :=
  aligned12352_12354.append aligned12354_12356

def missing12356_12357 : List (BitVec (edgeCount 12)) :=
  [missing12356]
abbrev records12356_12357 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12356]
theorem aligned12356_12357 :
    AlignedValid 12 4 missing12356_12357 records12356_12357 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12356
    maskCheck12356 AlignedValid.nil

def missing12357_12358 : List (BitVec (edgeCount 12)) :=
  [missing12357]
abbrev records12357_12358 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12357]
theorem aligned12357_12358 :
    AlignedValid 12 4 missing12357_12358 records12357_12358 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12357
    maskCheck12357 AlignedValid.nil

def missing12356_12358 : List (BitVec (edgeCount 12)) :=
  missing12356_12357 ++ missing12357_12358
abbrev records12356_12358 : List Blob :=
  records12356_12357 ++ records12357_12358
theorem aligned12356_12358 :
    AlignedValid 12 4 missing12356_12358 records12356_12358 :=
  aligned12356_12357.append aligned12357_12358

def missing12358_12359 : List (BitVec (edgeCount 12)) :=
  [missing12358]
abbrev records12358_12359 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12358]
theorem aligned12358_12359 :
    AlignedValid 12 4 missing12358_12359 records12358_12359 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12358
    maskCheck12358 AlignedValid.nil

def missing12359_12360 : List (BitVec (edgeCount 12)) :=
  [missing12359]
abbrev records12359_12360 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12359]
theorem aligned12359_12360 :
    AlignedValid 12 4 missing12359_12360 records12359_12360 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12359
    maskCheck12359 AlignedValid.nil

def missing12358_12360 : List (BitVec (edgeCount 12)) :=
  missing12358_12359 ++ missing12359_12360
abbrev records12358_12360 : List Blob :=
  records12358_12359 ++ records12359_12360
theorem aligned12358_12360 :
    AlignedValid 12 4 missing12358_12360 records12358_12360 :=
  aligned12358_12359.append aligned12359_12360

def missing12356_12360 : List (BitVec (edgeCount 12)) :=
  missing12356_12358 ++ missing12358_12360
abbrev records12356_12360 : List Blob :=
  records12356_12358 ++ records12358_12360
theorem aligned12356_12360 :
    AlignedValid 12 4 missing12356_12360 records12356_12360 :=
  aligned12356_12358.append aligned12358_12360

def missing12352_12360 : List (BitVec (edgeCount 12)) :=
  missing12352_12356 ++ missing12356_12360
abbrev records12352_12360 : List Blob :=
  records12352_12356 ++ records12356_12360
theorem aligned12352_12360 :
    AlignedValid 12 4 missing12352_12360 records12352_12360 :=
  aligned12352_12356.append aligned12356_12360

def missing12360_12361 : List (BitVec (edgeCount 12)) :=
  [missing12360]
abbrev records12360_12361 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12360]
theorem aligned12360_12361 :
    AlignedValid 12 4 missing12360_12361 records12360_12361 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12360
    maskCheck12360 AlignedValid.nil

def missing12361_12362 : List (BitVec (edgeCount 12)) :=
  [missing12361]
abbrev records12361_12362 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12361]
theorem aligned12361_12362 :
    AlignedValid 12 4 missing12361_12362 records12361_12362 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12361
    maskCheck12361 AlignedValid.nil

def missing12360_12362 : List (BitVec (edgeCount 12)) :=
  missing12360_12361 ++ missing12361_12362
abbrev records12360_12362 : List Blob :=
  records12360_12361 ++ records12361_12362
theorem aligned12360_12362 :
    AlignedValid 12 4 missing12360_12362 records12360_12362 :=
  aligned12360_12361.append aligned12361_12362

def missing12362_12363 : List (BitVec (edgeCount 12)) :=
  [missing12362]
abbrev records12362_12363 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12362]
theorem aligned12362_12363 :
    AlignedValid 12 4 missing12362_12363 records12362_12363 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12362
    maskCheck12362 AlignedValid.nil

def missing12363_12364 : List (BitVec (edgeCount 12)) :=
  [missing12363]
abbrev records12363_12364 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12363]
theorem aligned12363_12364 :
    AlignedValid 12 4 missing12363_12364 records12363_12364 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12363
    maskCheck12363 AlignedValid.nil

def missing12362_12364 : List (BitVec (edgeCount 12)) :=
  missing12362_12363 ++ missing12363_12364
abbrev records12362_12364 : List Blob :=
  records12362_12363 ++ records12363_12364
theorem aligned12362_12364 :
    AlignedValid 12 4 missing12362_12364 records12362_12364 :=
  aligned12362_12363.append aligned12363_12364

def missing12360_12364 : List (BitVec (edgeCount 12)) :=
  missing12360_12362 ++ missing12362_12364
abbrev records12360_12364 : List Blob :=
  records12360_12362 ++ records12362_12364
theorem aligned12360_12364 :
    AlignedValid 12 4 missing12360_12364 records12360_12364 :=
  aligned12360_12362.append aligned12362_12364

def missing12364_12365 : List (BitVec (edgeCount 12)) :=
  [missing12364]
abbrev records12364_12365 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12364]
theorem aligned12364_12365 :
    AlignedValid 12 4 missing12364_12365 records12364_12365 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12364
    maskCheck12364 AlignedValid.nil

def missing12365_12366 : List (BitVec (edgeCount 12)) :=
  [missing12365]
abbrev records12365_12366 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12365]
theorem aligned12365_12366 :
    AlignedValid 12 4 missing12365_12366 records12365_12366 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12365
    maskCheck12365 AlignedValid.nil

def missing12364_12366 : List (BitVec (edgeCount 12)) :=
  missing12364_12365 ++ missing12365_12366
abbrev records12364_12366 : List Blob :=
  records12364_12365 ++ records12365_12366
theorem aligned12364_12366 :
    AlignedValid 12 4 missing12364_12366 records12364_12366 :=
  aligned12364_12365.append aligned12365_12366

def missing12366_12367 : List (BitVec (edgeCount 12)) :=
  [missing12366]
abbrev records12366_12367 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12366]
theorem aligned12366_12367 :
    AlignedValid 12 4 missing12366_12367 records12366_12367 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12366
    maskCheck12366 AlignedValid.nil

def missing12367_12368 : List (BitVec (edgeCount 12)) :=
  [missing12367]
abbrev records12367_12368 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12367]
theorem aligned12367_12368 :
    AlignedValid 12 4 missing12367_12368 records12367_12368 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12367
    maskCheck12367 AlignedValid.nil

def missing12366_12368 : List (BitVec (edgeCount 12)) :=
  missing12366_12367 ++ missing12367_12368
abbrev records12366_12368 : List Blob :=
  records12366_12367 ++ records12367_12368
theorem aligned12366_12368 :
    AlignedValid 12 4 missing12366_12368 records12366_12368 :=
  aligned12366_12367.append aligned12367_12368

def missing12364_12368 : List (BitVec (edgeCount 12)) :=
  missing12364_12366 ++ missing12366_12368
abbrev records12364_12368 : List Blob :=
  records12364_12366 ++ records12366_12368
theorem aligned12364_12368 :
    AlignedValid 12 4 missing12364_12368 records12364_12368 :=
  aligned12364_12366.append aligned12366_12368

def missing12360_12368 : List (BitVec (edgeCount 12)) :=
  missing12360_12364 ++ missing12364_12368
abbrev records12360_12368 : List Blob :=
  records12360_12364 ++ records12364_12368
theorem aligned12360_12368 :
    AlignedValid 12 4 missing12360_12368 records12360_12368 :=
  aligned12360_12364.append aligned12364_12368

def missing12352_12368 : List (BitVec (edgeCount 12)) :=
  missing12352_12360 ++ missing12360_12368
abbrev records12352_12368 : List Blob :=
  records12352_12360 ++ records12360_12368
theorem aligned12352_12368 :
    AlignedValid 12 4 missing12352_12368 records12352_12368 :=
  aligned12352_12360.append aligned12360_12368

def missing12368_12369 : List (BitVec (edgeCount 12)) :=
  [missing12368]
abbrev records12368_12369 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12368]
theorem aligned12368_12369 :
    AlignedValid 12 4 missing12368_12369 records12368_12369 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12368
    maskCheck12368 AlignedValid.nil

def missing12369_12370 : List (BitVec (edgeCount 12)) :=
  [missing12369]
abbrev records12369_12370 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12369]
theorem aligned12369_12370 :
    AlignedValid 12 4 missing12369_12370 records12369_12370 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12369
    maskCheck12369 AlignedValid.nil

def missing12368_12370 : List (BitVec (edgeCount 12)) :=
  missing12368_12369 ++ missing12369_12370
abbrev records12368_12370 : List Blob :=
  records12368_12369 ++ records12369_12370
theorem aligned12368_12370 :
    AlignedValid 12 4 missing12368_12370 records12368_12370 :=
  aligned12368_12369.append aligned12369_12370

def missing12370_12371 : List (BitVec (edgeCount 12)) :=
  [missing12370]
abbrev records12370_12371 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12370]
theorem aligned12370_12371 :
    AlignedValid 12 4 missing12370_12371 records12370_12371 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12370
    maskCheck12370 AlignedValid.nil

def missing12371_12372 : List (BitVec (edgeCount 12)) :=
  [missing12371]
abbrev records12371_12372 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12371]
theorem aligned12371_12372 :
    AlignedValid 12 4 missing12371_12372 records12371_12372 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12371
    maskCheck12371 AlignedValid.nil

def missing12370_12372 : List (BitVec (edgeCount 12)) :=
  missing12370_12371 ++ missing12371_12372
abbrev records12370_12372 : List Blob :=
  records12370_12371 ++ records12371_12372
theorem aligned12370_12372 :
    AlignedValid 12 4 missing12370_12372 records12370_12372 :=
  aligned12370_12371.append aligned12371_12372

def missing12368_12372 : List (BitVec (edgeCount 12)) :=
  missing12368_12370 ++ missing12370_12372
abbrev records12368_12372 : List Blob :=
  records12368_12370 ++ records12370_12372
theorem aligned12368_12372 :
    AlignedValid 12 4 missing12368_12372 records12368_12372 :=
  aligned12368_12370.append aligned12370_12372

def missing12372_12373 : List (BitVec (edgeCount 12)) :=
  [missing12372]
abbrev records12372_12373 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12372]
theorem aligned12372_12373 :
    AlignedValid 12 4 missing12372_12373 records12372_12373 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12372
    maskCheck12372 AlignedValid.nil

def missing12373_12374 : List (BitVec (edgeCount 12)) :=
  [missing12373]
abbrev records12373_12374 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12373]
theorem aligned12373_12374 :
    AlignedValid 12 4 missing12373_12374 records12373_12374 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12373
    maskCheck12373 AlignedValid.nil

def missing12372_12374 : List (BitVec (edgeCount 12)) :=
  missing12372_12373 ++ missing12373_12374
abbrev records12372_12374 : List Blob :=
  records12372_12373 ++ records12373_12374
theorem aligned12372_12374 :
    AlignedValid 12 4 missing12372_12374 records12372_12374 :=
  aligned12372_12373.append aligned12373_12374

def missing12374_12375 : List (BitVec (edgeCount 12)) :=
  [missing12374]
abbrev records12374_12375 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12374]
theorem aligned12374_12375 :
    AlignedValid 12 4 missing12374_12375 records12374_12375 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12374
    maskCheck12374 AlignedValid.nil

def missing12375_12376 : List (BitVec (edgeCount 12)) :=
  [missing12375]
abbrev records12375_12376 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12375]
theorem aligned12375_12376 :
    AlignedValid 12 4 missing12375_12376 records12375_12376 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12375
    maskCheck12375 AlignedValid.nil

def missing12374_12376 : List (BitVec (edgeCount 12)) :=
  missing12374_12375 ++ missing12375_12376
abbrev records12374_12376 : List Blob :=
  records12374_12375 ++ records12375_12376
theorem aligned12374_12376 :
    AlignedValid 12 4 missing12374_12376 records12374_12376 :=
  aligned12374_12375.append aligned12375_12376

def missing12372_12376 : List (BitVec (edgeCount 12)) :=
  missing12372_12374 ++ missing12374_12376
abbrev records12372_12376 : List Blob :=
  records12372_12374 ++ records12374_12376
theorem aligned12372_12376 :
    AlignedValid 12 4 missing12372_12376 records12372_12376 :=
  aligned12372_12374.append aligned12374_12376

def missing12368_12376 : List (BitVec (edgeCount 12)) :=
  missing12368_12372 ++ missing12372_12376
abbrev records12368_12376 : List Blob :=
  records12368_12372 ++ records12372_12376
theorem aligned12368_12376 :
    AlignedValid 12 4 missing12368_12376 records12368_12376 :=
  aligned12368_12372.append aligned12372_12376

def missing12376_12377 : List (BitVec (edgeCount 12)) :=
  [missing12376]
abbrev records12376_12377 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12376]
theorem aligned12376_12377 :
    AlignedValid 12 4 missing12376_12377 records12376_12377 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12376
    maskCheck12376 AlignedValid.nil

def missing12377_12378 : List (BitVec (edgeCount 12)) :=
  [missing12377]
abbrev records12377_12378 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12377]
theorem aligned12377_12378 :
    AlignedValid 12 4 missing12377_12378 records12377_12378 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12377
    maskCheck12377 AlignedValid.nil

def missing12376_12378 : List (BitVec (edgeCount 12)) :=
  missing12376_12377 ++ missing12377_12378
abbrev records12376_12378 : List Blob :=
  records12376_12377 ++ records12377_12378
theorem aligned12376_12378 :
    AlignedValid 12 4 missing12376_12378 records12376_12378 :=
  aligned12376_12377.append aligned12377_12378

def missing12378_12379 : List (BitVec (edgeCount 12)) :=
  [missing12378]
abbrev records12378_12379 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12378]
theorem aligned12378_12379 :
    AlignedValid 12 4 missing12378_12379 records12378_12379 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12378
    maskCheck12378 AlignedValid.nil

def missing12379_12380 : List (BitVec (edgeCount 12)) :=
  [missing12379]
abbrev records12379_12380 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12379]
theorem aligned12379_12380 :
    AlignedValid 12 4 missing12379_12380 records12379_12380 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12379
    maskCheck12379 AlignedValid.nil

def missing12378_12380 : List (BitVec (edgeCount 12)) :=
  missing12378_12379 ++ missing12379_12380
abbrev records12378_12380 : List Blob :=
  records12378_12379 ++ records12379_12380
theorem aligned12378_12380 :
    AlignedValid 12 4 missing12378_12380 records12378_12380 :=
  aligned12378_12379.append aligned12379_12380

def missing12376_12380 : List (BitVec (edgeCount 12)) :=
  missing12376_12378 ++ missing12378_12380
abbrev records12376_12380 : List Blob :=
  records12376_12378 ++ records12378_12380
theorem aligned12376_12380 :
    AlignedValid 12 4 missing12376_12380 records12376_12380 :=
  aligned12376_12378.append aligned12378_12380

def missing12380_12381 : List (BitVec (edgeCount 12)) :=
  [missing12380]
abbrev records12380_12381 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12380]
theorem aligned12380_12381 :
    AlignedValid 12 4 missing12380_12381 records12380_12381 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12380
    maskCheck12380 AlignedValid.nil

def missing12381_12382 : List (BitVec (edgeCount 12)) :=
  [missing12381]
abbrev records12381_12382 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12381]
theorem aligned12381_12382 :
    AlignedValid 12 4 missing12381_12382 records12381_12382 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12381
    maskCheck12381 AlignedValid.nil

def missing12380_12382 : List (BitVec (edgeCount 12)) :=
  missing12380_12381 ++ missing12381_12382
abbrev records12380_12382 : List Blob :=
  records12380_12381 ++ records12381_12382
theorem aligned12380_12382 :
    AlignedValid 12 4 missing12380_12382 records12380_12382 :=
  aligned12380_12381.append aligned12381_12382

def missing12382_12383 : List (BitVec (edgeCount 12)) :=
  [missing12382]
abbrev records12382_12383 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12382]
theorem aligned12382_12383 :
    AlignedValid 12 4 missing12382_12383 records12382_12383 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12382
    maskCheck12382 AlignedValid.nil

def missing12383_12384 : List (BitVec (edgeCount 12)) :=
  [missing12383]
abbrev records12383_12384 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12383]
theorem aligned12383_12384 :
    AlignedValid 12 4 missing12383_12384 records12383_12384 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12383
    maskCheck12383 AlignedValid.nil

def missing12382_12384 : List (BitVec (edgeCount 12)) :=
  missing12382_12383 ++ missing12383_12384
abbrev records12382_12384 : List Blob :=
  records12382_12383 ++ records12383_12384
theorem aligned12382_12384 :
    AlignedValid 12 4 missing12382_12384 records12382_12384 :=
  aligned12382_12383.append aligned12383_12384

def missing12380_12384 : List (BitVec (edgeCount 12)) :=
  missing12380_12382 ++ missing12382_12384
abbrev records12380_12384 : List Blob :=
  records12380_12382 ++ records12382_12384
theorem aligned12380_12384 :
    AlignedValid 12 4 missing12380_12384 records12380_12384 :=
  aligned12380_12382.append aligned12382_12384

def missing12376_12384 : List (BitVec (edgeCount 12)) :=
  missing12376_12380 ++ missing12380_12384
abbrev records12376_12384 : List Blob :=
  records12376_12380 ++ records12380_12384
theorem aligned12376_12384 :
    AlignedValid 12 4 missing12376_12384 records12376_12384 :=
  aligned12376_12380.append aligned12380_12384

def missing12368_12384 : List (BitVec (edgeCount 12)) :=
  missing12368_12376 ++ missing12376_12384
abbrev records12368_12384 : List Blob :=
  records12368_12376 ++ records12376_12384
theorem aligned12368_12384 :
    AlignedValid 12 4 missing12368_12384 records12368_12384 :=
  aligned12368_12376.append aligned12376_12384

def missing12352_12384 : List (BitVec (edgeCount 12)) :=
  missing12352_12368 ++ missing12368_12384
abbrev records12352_12384 : List Blob :=
  records12352_12368 ++ records12368_12384
theorem aligned12352_12384 :
    AlignedValid 12 4 missing12352_12384 records12352_12384 :=
  aligned12352_12368.append aligned12368_12384

def missing12384_12385 : List (BitVec (edgeCount 12)) :=
  [missing12384]
abbrev records12384_12385 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12384]
theorem aligned12384_12385 :
    AlignedValid 12 4 missing12384_12385 records12384_12385 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12384
    maskCheck12384 AlignedValid.nil

def missing12385_12386 : List (BitVec (edgeCount 12)) :=
  [missing12385]
abbrev records12385_12386 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12385]
theorem aligned12385_12386 :
    AlignedValid 12 4 missing12385_12386 records12385_12386 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12385
    maskCheck12385 AlignedValid.nil

def missing12384_12386 : List (BitVec (edgeCount 12)) :=
  missing12384_12385 ++ missing12385_12386
abbrev records12384_12386 : List Blob :=
  records12384_12385 ++ records12385_12386
theorem aligned12384_12386 :
    AlignedValid 12 4 missing12384_12386 records12384_12386 :=
  aligned12384_12385.append aligned12385_12386

def missing12386_12387 : List (BitVec (edgeCount 12)) :=
  [missing12386]
abbrev records12386_12387 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12386]
theorem aligned12386_12387 :
    AlignedValid 12 4 missing12386_12387 records12386_12387 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12386
    maskCheck12386 AlignedValid.nil

def missing12387_12388 : List (BitVec (edgeCount 12)) :=
  [missing12387]
abbrev records12387_12388 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12387]
theorem aligned12387_12388 :
    AlignedValid 12 4 missing12387_12388 records12387_12388 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12387
    maskCheck12387 AlignedValid.nil

def missing12386_12388 : List (BitVec (edgeCount 12)) :=
  missing12386_12387 ++ missing12387_12388
abbrev records12386_12388 : List Blob :=
  records12386_12387 ++ records12387_12388
theorem aligned12386_12388 :
    AlignedValid 12 4 missing12386_12388 records12386_12388 :=
  aligned12386_12387.append aligned12387_12388

def missing12384_12388 : List (BitVec (edgeCount 12)) :=
  missing12384_12386 ++ missing12386_12388
abbrev records12384_12388 : List Blob :=
  records12384_12386 ++ records12386_12388
theorem aligned12384_12388 :
    AlignedValid 12 4 missing12384_12388 records12384_12388 :=
  aligned12384_12386.append aligned12386_12388

def missing12388_12389 : List (BitVec (edgeCount 12)) :=
  [missing12388]
abbrev records12388_12389 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12388]
theorem aligned12388_12389 :
    AlignedValid 12 4 missing12388_12389 records12388_12389 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12388
    maskCheck12388 AlignedValid.nil

def missing12389_12390 : List (BitVec (edgeCount 12)) :=
  [missing12389]
abbrev records12389_12390 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12389]
theorem aligned12389_12390 :
    AlignedValid 12 4 missing12389_12390 records12389_12390 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12389
    maskCheck12389 AlignedValid.nil

def missing12388_12390 : List (BitVec (edgeCount 12)) :=
  missing12388_12389 ++ missing12389_12390
abbrev records12388_12390 : List Blob :=
  records12388_12389 ++ records12389_12390
theorem aligned12388_12390 :
    AlignedValid 12 4 missing12388_12390 records12388_12390 :=
  aligned12388_12389.append aligned12389_12390

def missing12390_12391 : List (BitVec (edgeCount 12)) :=
  [missing12390]
abbrev records12390_12391 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12390]
theorem aligned12390_12391 :
    AlignedValid 12 4 missing12390_12391 records12390_12391 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12390
    maskCheck12390 AlignedValid.nil

def missing12391_12392 : List (BitVec (edgeCount 12)) :=
  [missing12391]
abbrev records12391_12392 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12391]
theorem aligned12391_12392 :
    AlignedValid 12 4 missing12391_12392 records12391_12392 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12391
    maskCheck12391 AlignedValid.nil

def missing12390_12392 : List (BitVec (edgeCount 12)) :=
  missing12390_12391 ++ missing12391_12392
abbrev records12390_12392 : List Blob :=
  records12390_12391 ++ records12391_12392
theorem aligned12390_12392 :
    AlignedValid 12 4 missing12390_12392 records12390_12392 :=
  aligned12390_12391.append aligned12391_12392

def missing12388_12392 : List (BitVec (edgeCount 12)) :=
  missing12388_12390 ++ missing12390_12392
abbrev records12388_12392 : List Blob :=
  records12388_12390 ++ records12390_12392
theorem aligned12388_12392 :
    AlignedValid 12 4 missing12388_12392 records12388_12392 :=
  aligned12388_12390.append aligned12390_12392

def missing12384_12392 : List (BitVec (edgeCount 12)) :=
  missing12384_12388 ++ missing12388_12392
abbrev records12384_12392 : List Blob :=
  records12384_12388 ++ records12388_12392
theorem aligned12384_12392 :
    AlignedValid 12 4 missing12384_12392 records12384_12392 :=
  aligned12384_12388.append aligned12388_12392

def missing12392_12393 : List (BitVec (edgeCount 12)) :=
  [missing12392]
abbrev records12392_12393 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12392]
theorem aligned12392_12393 :
    AlignedValid 12 4 missing12392_12393 records12392_12393 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12392
    maskCheck12392 AlignedValid.nil

def missing12393_12394 : List (BitVec (edgeCount 12)) :=
  [missing12393]
abbrev records12393_12394 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12393]
theorem aligned12393_12394 :
    AlignedValid 12 4 missing12393_12394 records12393_12394 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12393
    maskCheck12393 AlignedValid.nil

def missing12392_12394 : List (BitVec (edgeCount 12)) :=
  missing12392_12393 ++ missing12393_12394
abbrev records12392_12394 : List Blob :=
  records12392_12393 ++ records12393_12394
theorem aligned12392_12394 :
    AlignedValid 12 4 missing12392_12394 records12392_12394 :=
  aligned12392_12393.append aligned12393_12394

def missing12394_12395 : List (BitVec (edgeCount 12)) :=
  [missing12394]
abbrev records12394_12395 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12394]
theorem aligned12394_12395 :
    AlignedValid 12 4 missing12394_12395 records12394_12395 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12394
    maskCheck12394 AlignedValid.nil

def missing12395_12396 : List (BitVec (edgeCount 12)) :=
  [missing12395]
abbrev records12395_12396 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12395]
theorem aligned12395_12396 :
    AlignedValid 12 4 missing12395_12396 records12395_12396 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12395
    maskCheck12395 AlignedValid.nil

def missing12394_12396 : List (BitVec (edgeCount 12)) :=
  missing12394_12395 ++ missing12395_12396
abbrev records12394_12396 : List Blob :=
  records12394_12395 ++ records12395_12396
theorem aligned12394_12396 :
    AlignedValid 12 4 missing12394_12396 records12394_12396 :=
  aligned12394_12395.append aligned12395_12396

def missing12392_12396 : List (BitVec (edgeCount 12)) :=
  missing12392_12394 ++ missing12394_12396
abbrev records12392_12396 : List Blob :=
  records12392_12394 ++ records12394_12396
theorem aligned12392_12396 :
    AlignedValid 12 4 missing12392_12396 records12392_12396 :=
  aligned12392_12394.append aligned12394_12396

def missing12396_12397 : List (BitVec (edgeCount 12)) :=
  [missing12396]
abbrev records12396_12397 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12396]
theorem aligned12396_12397 :
    AlignedValid 12 4 missing12396_12397 records12396_12397 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12396
    maskCheck12396 AlignedValid.nil

def missing12397_12398 : List (BitVec (edgeCount 12)) :=
  [missing12397]
abbrev records12397_12398 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12397]
theorem aligned12397_12398 :
    AlignedValid 12 4 missing12397_12398 records12397_12398 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12397
    maskCheck12397 AlignedValid.nil

def missing12396_12398 : List (BitVec (edgeCount 12)) :=
  missing12396_12397 ++ missing12397_12398
abbrev records12396_12398 : List Blob :=
  records12396_12397 ++ records12397_12398
theorem aligned12396_12398 :
    AlignedValid 12 4 missing12396_12398 records12396_12398 :=
  aligned12396_12397.append aligned12397_12398

def missing12398_12399 : List (BitVec (edgeCount 12)) :=
  [missing12398]
abbrev records12398_12399 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12398]
theorem aligned12398_12399 :
    AlignedValid 12 4 missing12398_12399 records12398_12399 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12398
    maskCheck12398 AlignedValid.nil

def missing12399_12400 : List (BitVec (edgeCount 12)) :=
  [missing12399]
abbrev records12399_12400 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12399]
theorem aligned12399_12400 :
    AlignedValid 12 4 missing12399_12400 records12399_12400 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12399
    maskCheck12399 AlignedValid.nil

def missing12398_12400 : List (BitVec (edgeCount 12)) :=
  missing12398_12399 ++ missing12399_12400
abbrev records12398_12400 : List Blob :=
  records12398_12399 ++ records12399_12400
theorem aligned12398_12400 :
    AlignedValid 12 4 missing12398_12400 records12398_12400 :=
  aligned12398_12399.append aligned12399_12400

def missing12396_12400 : List (BitVec (edgeCount 12)) :=
  missing12396_12398 ++ missing12398_12400
abbrev records12396_12400 : List Blob :=
  records12396_12398 ++ records12398_12400
theorem aligned12396_12400 :
    AlignedValid 12 4 missing12396_12400 records12396_12400 :=
  aligned12396_12398.append aligned12398_12400

def missing12392_12400 : List (BitVec (edgeCount 12)) :=
  missing12392_12396 ++ missing12396_12400
abbrev records12392_12400 : List Blob :=
  records12392_12396 ++ records12396_12400
theorem aligned12392_12400 :
    AlignedValid 12 4 missing12392_12400 records12392_12400 :=
  aligned12392_12396.append aligned12396_12400

def missing12384_12400 : List (BitVec (edgeCount 12)) :=
  missing12384_12392 ++ missing12392_12400
abbrev records12384_12400 : List Blob :=
  records12384_12392 ++ records12392_12400
theorem aligned12384_12400 :
    AlignedValid 12 4 missing12384_12400 records12384_12400 :=
  aligned12384_12392.append aligned12392_12400

def missing12400_12401 : List (BitVec (edgeCount 12)) :=
  [missing12400]
abbrev records12400_12401 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12400]
theorem aligned12400_12401 :
    AlignedValid 12 4 missing12400_12401 records12400_12401 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12400
    maskCheck12400 AlignedValid.nil

def missing12401_12402 : List (BitVec (edgeCount 12)) :=
  [missing12401]
abbrev records12401_12402 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12401]
theorem aligned12401_12402 :
    AlignedValid 12 4 missing12401_12402 records12401_12402 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12401
    maskCheck12401 AlignedValid.nil

def missing12400_12402 : List (BitVec (edgeCount 12)) :=
  missing12400_12401 ++ missing12401_12402
abbrev records12400_12402 : List Blob :=
  records12400_12401 ++ records12401_12402
theorem aligned12400_12402 :
    AlignedValid 12 4 missing12400_12402 records12400_12402 :=
  aligned12400_12401.append aligned12401_12402

def missing12402_12403 : List (BitVec (edgeCount 12)) :=
  [missing12402]
abbrev records12402_12403 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12402]
theorem aligned12402_12403 :
    AlignedValid 12 4 missing12402_12403 records12402_12403 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12402
    maskCheck12402 AlignedValid.nil

def missing12403_12404 : List (BitVec (edgeCount 12)) :=
  [missing12403]
abbrev records12403_12404 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12403]
theorem aligned12403_12404 :
    AlignedValid 12 4 missing12403_12404 records12403_12404 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12403
    maskCheck12403 AlignedValid.nil

def missing12402_12404 : List (BitVec (edgeCount 12)) :=
  missing12402_12403 ++ missing12403_12404
abbrev records12402_12404 : List Blob :=
  records12402_12403 ++ records12403_12404
theorem aligned12402_12404 :
    AlignedValid 12 4 missing12402_12404 records12402_12404 :=
  aligned12402_12403.append aligned12403_12404

def missing12400_12404 : List (BitVec (edgeCount 12)) :=
  missing12400_12402 ++ missing12402_12404
abbrev records12400_12404 : List Blob :=
  records12400_12402 ++ records12402_12404
theorem aligned12400_12404 :
    AlignedValid 12 4 missing12400_12404 records12400_12404 :=
  aligned12400_12402.append aligned12402_12404

def missing12404_12405 : List (BitVec (edgeCount 12)) :=
  [missing12404]
abbrev records12404_12405 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12404]
theorem aligned12404_12405 :
    AlignedValid 12 4 missing12404_12405 records12404_12405 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12404
    maskCheck12404 AlignedValid.nil

def missing12405_12406 : List (BitVec (edgeCount 12)) :=
  [missing12405]
abbrev records12405_12406 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12405]
theorem aligned12405_12406 :
    AlignedValid 12 4 missing12405_12406 records12405_12406 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12405
    maskCheck12405 AlignedValid.nil

def missing12404_12406 : List (BitVec (edgeCount 12)) :=
  missing12404_12405 ++ missing12405_12406
abbrev records12404_12406 : List Blob :=
  records12404_12405 ++ records12405_12406
theorem aligned12404_12406 :
    AlignedValid 12 4 missing12404_12406 records12404_12406 :=
  aligned12404_12405.append aligned12405_12406

def missing12406_12407 : List (BitVec (edgeCount 12)) :=
  [missing12406]
abbrev records12406_12407 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12406]
theorem aligned12406_12407 :
    AlignedValid 12 4 missing12406_12407 records12406_12407 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12406
    maskCheck12406 AlignedValid.nil

def missing12407_12408 : List (BitVec (edgeCount 12)) :=
  [missing12407]
abbrev records12407_12408 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12407]
theorem aligned12407_12408 :
    AlignedValid 12 4 missing12407_12408 records12407_12408 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12407
    maskCheck12407 AlignedValid.nil

def missing12406_12408 : List (BitVec (edgeCount 12)) :=
  missing12406_12407 ++ missing12407_12408
abbrev records12406_12408 : List Blob :=
  records12406_12407 ++ records12407_12408
theorem aligned12406_12408 :
    AlignedValid 12 4 missing12406_12408 records12406_12408 :=
  aligned12406_12407.append aligned12407_12408

def missing12404_12408 : List (BitVec (edgeCount 12)) :=
  missing12404_12406 ++ missing12406_12408
abbrev records12404_12408 : List Blob :=
  records12404_12406 ++ records12406_12408
theorem aligned12404_12408 :
    AlignedValid 12 4 missing12404_12408 records12404_12408 :=
  aligned12404_12406.append aligned12406_12408

def missing12400_12408 : List (BitVec (edgeCount 12)) :=
  missing12400_12404 ++ missing12404_12408
abbrev records12400_12408 : List Blob :=
  records12400_12404 ++ records12404_12408
theorem aligned12400_12408 :
    AlignedValid 12 4 missing12400_12408 records12400_12408 :=
  aligned12400_12404.append aligned12404_12408

def missing12408_12409 : List (BitVec (edgeCount 12)) :=
  [missing12408]
abbrev records12408_12409 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12408]
theorem aligned12408_12409 :
    AlignedValid 12 4 missing12408_12409 records12408_12409 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12408
    maskCheck12408 AlignedValid.nil

def missing12409_12410 : List (BitVec (edgeCount 12)) :=
  [missing12409]
abbrev records12409_12410 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12409]
theorem aligned12409_12410 :
    AlignedValid 12 4 missing12409_12410 records12409_12410 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12409
    maskCheck12409 AlignedValid.nil

def missing12408_12410 : List (BitVec (edgeCount 12)) :=
  missing12408_12409 ++ missing12409_12410
abbrev records12408_12410 : List Blob :=
  records12408_12409 ++ records12409_12410
theorem aligned12408_12410 :
    AlignedValid 12 4 missing12408_12410 records12408_12410 :=
  aligned12408_12409.append aligned12409_12410

def missing12410_12411 : List (BitVec (edgeCount 12)) :=
  [missing12410]
abbrev records12410_12411 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12410]
theorem aligned12410_12411 :
    AlignedValid 12 4 missing12410_12411 records12410_12411 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12410
    maskCheck12410 AlignedValid.nil

def missing12411_12412 : List (BitVec (edgeCount 12)) :=
  [missing12411]
abbrev records12411_12412 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12411]
theorem aligned12411_12412 :
    AlignedValid 12 4 missing12411_12412 records12411_12412 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12411
    maskCheck12411 AlignedValid.nil

def missing12410_12412 : List (BitVec (edgeCount 12)) :=
  missing12410_12411 ++ missing12411_12412
abbrev records12410_12412 : List Blob :=
  records12410_12411 ++ records12411_12412
theorem aligned12410_12412 :
    AlignedValid 12 4 missing12410_12412 records12410_12412 :=
  aligned12410_12411.append aligned12411_12412

def missing12408_12412 : List (BitVec (edgeCount 12)) :=
  missing12408_12410 ++ missing12410_12412
abbrev records12408_12412 : List Blob :=
  records12408_12410 ++ records12410_12412
theorem aligned12408_12412 :
    AlignedValid 12 4 missing12408_12412 records12408_12412 :=
  aligned12408_12410.append aligned12410_12412

def missing12412_12413 : List (BitVec (edgeCount 12)) :=
  [missing12412]
abbrev records12412_12413 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12412]
theorem aligned12412_12413 :
    AlignedValid 12 4 missing12412_12413 records12412_12413 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12412
    maskCheck12412 AlignedValid.nil

def missing12413_12414 : List (BitVec (edgeCount 12)) :=
  [missing12413]
abbrev records12413_12414 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12413]
theorem aligned12413_12414 :
    AlignedValid 12 4 missing12413_12414 records12413_12414 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12413
    maskCheck12413 AlignedValid.nil

def missing12412_12414 : List (BitVec (edgeCount 12)) :=
  missing12412_12413 ++ missing12413_12414
abbrev records12412_12414 : List Blob :=
  records12412_12413 ++ records12413_12414
theorem aligned12412_12414 :
    AlignedValid 12 4 missing12412_12414 records12412_12414 :=
  aligned12412_12413.append aligned12413_12414

def missing12414_12415 : List (BitVec (edgeCount 12)) :=
  [missing12414]
abbrev records12414_12415 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12414]
theorem aligned12414_12415 :
    AlignedValid 12 4 missing12414_12415 records12414_12415 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12414
    maskCheck12414 AlignedValid.nil

def missing12415_12416 : List (BitVec (edgeCount 12)) :=
  [missing12415]
abbrev records12415_12416 : List Blob :=
  [StrongPackedBucketN12A4Shard096.record12415]
theorem aligned12415_12416 :
    AlignedValid 12 4 missing12415_12416 records12415_12416 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard096.check12415
    maskCheck12415 AlignedValid.nil

def missing12414_12416 : List (BitVec (edgeCount 12)) :=
  missing12414_12415 ++ missing12415_12416
abbrev records12414_12416 : List Blob :=
  records12414_12415 ++ records12415_12416
theorem aligned12414_12416 :
    AlignedValid 12 4 missing12414_12416 records12414_12416 :=
  aligned12414_12415.append aligned12415_12416

def missing12412_12416 : List (BitVec (edgeCount 12)) :=
  missing12412_12414 ++ missing12414_12416
abbrev records12412_12416 : List Blob :=
  records12412_12414 ++ records12414_12416
theorem aligned12412_12416 :
    AlignedValid 12 4 missing12412_12416 records12412_12416 :=
  aligned12412_12414.append aligned12414_12416

def missing12408_12416 : List (BitVec (edgeCount 12)) :=
  missing12408_12412 ++ missing12412_12416
abbrev records12408_12416 : List Blob :=
  records12408_12412 ++ records12412_12416
theorem aligned12408_12416 :
    AlignedValid 12 4 missing12408_12416 records12408_12416 :=
  aligned12408_12412.append aligned12412_12416

def missing12400_12416 : List (BitVec (edgeCount 12)) :=
  missing12400_12408 ++ missing12408_12416
abbrev records12400_12416 : List Blob :=
  records12400_12408 ++ records12408_12416
theorem aligned12400_12416 :
    AlignedValid 12 4 missing12400_12416 records12400_12416 :=
  aligned12400_12408.append aligned12408_12416

def missing12384_12416 : List (BitVec (edgeCount 12)) :=
  missing12384_12400 ++ missing12400_12416
abbrev records12384_12416 : List Blob :=
  records12384_12400 ++ records12400_12416
theorem aligned12384_12416 :
    AlignedValid 12 4 missing12384_12416 records12384_12416 :=
  aligned12384_12400.append aligned12400_12416

def missing12352_12416 : List (BitVec (edgeCount 12)) :=
  missing12352_12384 ++ missing12384_12416
abbrev records12352_12416 : List Blob :=
  records12352_12384 ++ records12384_12416
theorem aligned12352_12416 :
    AlignedValid 12 4 missing12352_12416 records12352_12416 :=
  aligned12352_12384.append aligned12384_12416

def missing12288_12416 : List (BitVec (edgeCount 12)) :=
  missing12288_12352 ++ missing12352_12416
abbrev records12288_12416 : List Blob :=
  records12288_12352 ++ records12352_12416
theorem aligned12288_12416 :
    AlignedValid 12 4 missing12288_12416 records12288_12416 :=
  aligned12288_12352.append aligned12352_12416

abbrev missing : List (BitVec (edgeCount 12)) := missing12288_12416
abbrev records : List Blob := records12288_12416
theorem aligned : AlignedValid 12 4 missing records := aligned12288_12416

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard096
