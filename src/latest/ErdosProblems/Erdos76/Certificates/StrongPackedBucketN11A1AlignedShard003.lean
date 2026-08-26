/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11A1Shard003

/-! Decode-only alignment checks for a=1, records 384--466. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A1AlignedShard003

open PackedBucketCertificate

def missing384 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 423037910384640
theorem maskCheck384 :
    checkMaskFor missing384 StrongPackedBucketN11A1Shard003.record384 = true := by
  decide

def missing385 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 422901008302080
theorem maskCheck385 :
    checkMaskFor missing385 StrongPackedBucketN11A1Shard003.record385 = true := by
  decide

def missing386 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 212756848443392
theorem maskCheck386 :
    checkMaskFor missing386 StrongPackedBucketN11A1Shard003.record386 = true := by
  decide

def missing387 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 108854878666752
theorem maskCheck387 :
    checkMaskFor missing387 StrongPackedBucketN11A1Shard003.record387 = true := by
  decide

def missing388 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 528316415115264
theorem maskCheck388 :
    checkMaskFor missing388 StrongPackedBucketN11A1Shard003.record388 = true := by
  decide

def missing389 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 809791391825920
theorem maskCheck389 :
    checkMaskFor missing389 StrongPackedBucketN11A1Shard003.record389 = true := by
  decide

def missing390 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1794953810313216
theorem maskCheck390 :
    checkMaskFor missing390 StrongPackedBucketN11A1Shard003.record390 = true := by
  decide

def missing391 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2498641252089856
theorem maskCheck391 :
    checkMaskFor missing391 StrongPackedBucketN11A1Shard003.record391 = true := by
  decide

def missing392 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2920853717155840
theorem maskCheck392 :
    checkMaskFor missing392 StrongPackedBucketN11A1Shard003.record392 = true := by
  decide

def missing393 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 3976384879820800
theorem maskCheck393 :
    checkMaskFor missing393 StrongPackedBucketN11A1Shard003.record393 = true := by
  decide

def missing394 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 6861503391105024
theorem maskCheck394 :
    checkMaskFor missing394 StrongPackedBucketN11A1Shard003.record394 = true := by
  decide

def missing395 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 246910157881344
theorem maskCheck395 :
    checkMaskFor missing395 StrongPackedBucketN11A1Shard003.record395 = true := by
  decide

def missing396 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 387647646236672
theorem maskCheck396 :
    checkMaskFor missing396 StrongPackedBucketN11A1Shard003.record396 = true := by
  decide

def missing397 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 493200762503168
theorem maskCheck397 :
    checkMaskFor missing397 StrongPackedBucketN11A1Shard003.record397 = true := by
  decide

def missing398 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 669122622947328
theorem maskCheck398 :
    checkMaskFor missing398 StrongPackedBucketN11A1Shard003.record398 = true := by
  decide

def missing399 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 774675739213824
theorem maskCheck399 :
    checkMaskFor missing399 StrongPackedBucketN11A1Shard003.record399 = true := by
  decide

def missing400 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 880228855480320
theorem maskCheck400 :
    checkMaskFor missing400 StrongPackedBucketN11A1Shard003.record400 = true := by
  decide

def missing401 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 915413227569152
theorem maskCheck401 :
    checkMaskFor missing401 StrongPackedBucketN11A1Shard003.record401 = true := by
  decide

def missing402 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1759838157701120
theorem maskCheck402 :
    checkMaskFor missing402 StrongPackedBucketN11A1Shard003.record402 = true := by
  decide

def missing403 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1970944390234112
theorem maskCheck403 :
    checkMaskFor missing403 StrongPackedBucketN11A1Shard003.record403 = true := by
  decide

def missing404 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2357972483211264
theorem maskCheck404 :
    checkMaskFor missing404 StrongPackedBucketN11A1Shard003.record404 = true := by
  decide

def missing405 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2569078715744256
theorem maskCheck405 :
    checkMaskFor missing405 StrongPackedBucketN11A1Shard003.record405 = true := by
  decide

def missing406 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2604263087833088
theorem maskCheck406 :
    checkMaskFor missing406 StrongPackedBucketN11A1Shard003.record406 = true := by
  decide

def missing407 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 3096844297076736
theorem maskCheck407 :
    checkMaskFor missing407 StrongPackedBucketN11A1Shard003.record407 = true := by
  decide

def missing408 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4609772296896512
theorem maskCheck408 :
    checkMaskFor missing408 StrongPackedBucketN11A1Shard003.record408 = true := by
  decide

def missing409 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4715325413163008
theorem maskCheck409 :
    checkMaskFor missing409 StrongPackedBucketN11A1Shard003.record409 = true := by
  decide

def missing410 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4856062901518336
theorem maskCheck410 :
    checkMaskFor missing410 StrongPackedBucketN11A1Shard003.record410 = true := by
  decide

def missing411 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 5137537878228992
theorem maskCheck411 :
    checkMaskFor missing411 StrongPackedBucketN11A1Shard003.record411 = true := by
  decide

def missing412 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18120571179008000
theorem maskCheck412 :
    checkMaskFor missing412 StrongPackedBucketN11A1Shard003.record412 = true := by
  decide

def missing413 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18331677411540992
theorem maskCheck413 :
    checkMaskFor missing413 StrongPackedBucketN11A1Shard003.record413 = true := by
  decide

def missing414 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18613152388251648
theorem maskCheck414 :
    checkMaskFor missing414 StrongPackedBucketN11A1Shard003.record414 = true := by
  decide

def missing415 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 247940950032384
theorem maskCheck415 :
    checkMaskFor missing415 StrongPackedBucketN11A1Shard003.record415 = true := by
  decide

def missing416 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 388678438387712
theorem maskCheck416 :
    checkMaskFor missing416 StrongPackedBucketN11A1Shard003.record416 = true := by
  decide

def missing417 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 881259647631360
theorem maskCheck417 :
    checkMaskFor missing417 StrongPackedBucketN11A1Shard003.record417 = true := by
  decide

def missing418 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1233103368519680
theorem maskCheck418 :
    checkMaskFor missing418 StrongPackedBucketN11A1Shard003.record418 = true := by
  decide

def missing419 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1444209601052672
theorem maskCheck419 :
    checkMaskFor missing419 StrongPackedBucketN11A1Shard003.record419 = true := by
  decide

def missing420 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1971975182385152
theorem maskCheck420 :
    checkMaskFor missing420 StrongPackedBucketN11A1Shard003.record420 = true := by
  decide

def missing421 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2359003275362304
theorem maskCheck421 :
    checkMaskFor missing421 StrongPackedBucketN11A1Shard003.record421 = true := by
  decide

def missing422 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2570109507895296
theorem maskCheck422 :
    checkMaskFor missing422 StrongPackedBucketN11A1Shard003.record422 = true := by
  decide

def missing423 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 3414534438027264
theorem maskCheck423 :
    checkMaskFor missing423 StrongPackedBucketN11A1Shard003.record423 = true := by
  decide

def missing424 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18121601971159040
theorem maskCheck424 :
    checkMaskFor missing424 StrongPackedBucketN11A1Shard003.record424 = true := by
  decide

def missing425 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18332708203692032
theorem maskCheck425 :
    checkMaskFor missing425 StrongPackedBucketN11A1Shard003.record425 = true := by
  decide

def missing426 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18860473785024512
theorem maskCheck426 :
    checkMaskFor missing426 StrongPackedBucketN11A1Shard003.record426 = true := by
  decide

def missing427 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19177133133824000
theorem maskCheck427 :
    checkMaskFor missing427 StrongPackedBucketN11A1Shard003.record427 = true := by
  decide

def missing428 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19423423738445824
theorem maskCheck428 :
    checkMaskFor missing428 StrongPackedBucketN11A1Shard003.record428 = true := by
  decide

def missing429 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 20303033040666624
theorem maskCheck429 :
    checkMaskFor missing429 StrongPackedBucketN11A1Shard003.record429 = true := by
  decide

def missing430 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 497049053200384
theorem maskCheck430 :
    checkMaskFor missing430 StrongPackedBucketN11A1Shard003.record430 = true := by
  decide

def missing431 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 919261518266368
theorem maskCheck431 :
    checkMaskFor missing431 StrongPackedBucketN11A1Shard003.record431 = true := by
  decide

def missing432 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1974792680931328
theorem maskCheck432 :
    checkMaskFor missing432 StrongPackedBucketN11A1Shard003.record432 = true := by
  decide

def missing433 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2361820773908480
theorem maskCheck433 :
    checkMaskFor missing433 StrongPackedBucketN11A1Shard003.record433 = true := by
  decide

def missing434 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4613620587593728
theorem maskCheck434 :
    checkMaskFor missing434 StrongPackedBucketN11A1Shard003.record434 = true := by
  decide

def missing435 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4719173703860224
theorem maskCheck435 :
    checkMaskFor missing435 StrongPackedBucketN11A1Shard003.record435 = true := by
  decide

def missing436 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4859911192215552
theorem maskCheck436 :
    checkMaskFor missing436 StrongPackedBucketN11A1Shard003.record436 = true := by
  decide

def missing437 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 20305850539212800
theorem maskCheck437 :
    checkMaskFor missing437 StrongPackedBucketN11A1Shard003.record437 = true := by
  decide

def missing438 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2393225843212288
theorem maskCheck438 :
    checkMaskFor missing438 StrongPackedBucketN11A1Shard003.record438 = true := by
  decide

def missing439 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 352669701013504
theorem maskCheck439 :
    checkMaskFor missing439 StrongPackedBucketN11A1Shard003.record439 = true := by
  decide

def missing440 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2534100770521088
theorem maskCheck440 :
    checkMaskFor missing440 StrongPackedBucketN11A1Shard003.record440 = true := by
  decide

def missing441 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 212756846379008
theorem maskCheck441 :
    checkMaskFor missing441 StrongPackedBucketN11A1Shard003.record441 = true := by
  decide

def missing442 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 353494334734336
theorem maskCheck442 :
    checkMaskFor missing442 StrongPackedBucketN11A1Shard003.record442 = true := by
  decide

def missing443 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 846075543977984
theorem maskCheck443 :
    checkMaskFor missing443 StrongPackedBucketN11A1Shard003.record443 = true := by
  decide

def missing444 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1197919264866304
theorem maskCheck444 :
    checkMaskFor missing444 StrongPackedBucketN11A1Shard003.record444 = true := by
  decide

def missing445 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2394187915886592
theorem maskCheck445 :
    checkMaskFor missing445 StrongPackedBucketN11A1Shard003.record445 = true := by
  decide

def missing446 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4575618985394176
theorem maskCheck446 :
    checkMaskFor missing446 StrongPackedBucketN11A1Shard003.record446 = true := by
  decide

def missing447 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 106380975439872
theorem maskCheck447 :
    checkMaskFor missing447 StrongPackedBucketN11A1Shard003.record447 = true := by
  decide

def missing448 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 106930731253760
theorem maskCheck448 :
    checkMaskFor missing448 StrongPackedBucketN11A1Shard003.record448 = true := by
  decide

def missing449 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 318036963786752
theorem maskCheck449 :
    checkMaskFor missing449 StrongPackedBucketN11A1Shard003.record449 = true := by
  decide

def missing450 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 845802545119232
theorem maskCheck450 :
    checkMaskFor missing450 StrongPackedBucketN11A1Shard003.record450 = true := by
  decide

def missing451 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 108854876602368
theorem maskCheck451 :
    checkMaskFor missing451 StrongPackedBucketN11A1Shard003.record451 = true := by
  decide

def missing452 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 179223620780032
theorem maskCheck452 :
    checkMaskFor missing452 StrongPackedBucketN11A1Shard003.record452 = true := by
  decide

def missing453 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 425514225401856
theorem maskCheck453 :
    checkMaskFor missing453 StrongPackedBucketN11A1Shard003.record453 = true := by
  decide

def missing454 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2290285946109952
theorem maskCheck454 :
    checkMaskFor missing454 StrongPackedBucketN11A1Shard003.record454 = true := by
  decide

def missing455 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4644766885117952
theorem maskCheck455 :
    checkMaskFor missing455 StrongPackedBucketN11A1Shard003.record455 = true := by
  decide

def missing456 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 211948318785536
theorem maskCheck456 :
    checkMaskFor missing456 StrongPackedBucketN11A1Shard003.record456 = true := by
  decide

def missing457 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 423054551318528
theorem maskCheck457 :
    checkMaskFor missing457 StrongPackedBucketN11A1Shard003.record457 = true := by
  decide

def missing458 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4574810457800704
theorem maskCheck458 :
    checkMaskFor missing458 StrongPackedBucketN11A1Shard003.record458 = true := by
  decide

def missing459 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 247392272188416
theorem maskCheck459 :
    checkMaskFor missing459 StrongPackedBucketN11A1Shard003.record459 = true := by
  decide

def missing460 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1232554690675712
theorem maskCheck460 :
    checkMaskFor missing460 StrongPackedBucketN11A1Shard003.record460 = true := by
  decide

def missing461 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 212276619576320
theorem maskCheck461 :
    checkMaskFor missing461 StrongPackedBucketN11A1Shard003.record461 = true := by
  decide

def missing462 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 634489084642304
theorem maskCheck462 :
    checkMaskFor missing462 StrongPackedBucketN11A1Shard003.record462 = true := by
  decide

def missing463 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1690020247307264
theorem maskCheck463 :
    checkMaskFor missing463 StrongPackedBucketN11A1Shard003.record463 = true := by
  decide

def missing464 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2323338944906240
theorem maskCheck464 :
    checkMaskFor missing464 StrongPackedBucketN11A1Shard003.record464 = true := by
  decide

def missing465 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 213376131204096
theorem maskCheck465 :
    checkMaskFor missing465 StrongPackedBucketN11A1Shard003.record465 = true := by
  decide

def missing466 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2324438456534016
theorem maskCheck466 :
    checkMaskFor missing466 StrongPackedBucketN11A1Shard003.record466 = true := by
  decide

def missing384_385 : List (BitVec (edgeCount 11)) :=
  [missing384]
abbrev records384_385 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record384]
theorem aligned384_385 :
    AlignedValid 11 1 missing384_385 records384_385 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check384
    maskCheck384 AlignedValid.nil

def missing385_386 : List (BitVec (edgeCount 11)) :=
  [missing385]
abbrev records385_386 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record385]
theorem aligned385_386 :
    AlignedValid 11 1 missing385_386 records385_386 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check385
    maskCheck385 AlignedValid.nil

def missing384_386 : List (BitVec (edgeCount 11)) :=
  missing384_385 ++ missing385_386
abbrev records384_386 : List Blob :=
  records384_385 ++ records385_386
theorem aligned384_386 :
    AlignedValid 11 1 missing384_386 records384_386 :=
  aligned384_385.append aligned385_386

def missing386_387 : List (BitVec (edgeCount 11)) :=
  [missing386]
abbrev records386_387 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record386]
theorem aligned386_387 :
    AlignedValid 11 1 missing386_387 records386_387 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check386
    maskCheck386 AlignedValid.nil

def missing387_388 : List (BitVec (edgeCount 11)) :=
  [missing387]
abbrev records387_388 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record387]
theorem aligned387_388 :
    AlignedValid 11 1 missing387_388 records387_388 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check387
    maskCheck387 AlignedValid.nil

def missing388_389 : List (BitVec (edgeCount 11)) :=
  [missing388]
abbrev records388_389 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record388]
theorem aligned388_389 :
    AlignedValid 11 1 missing388_389 records388_389 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check388
    maskCheck388 AlignedValid.nil

def missing387_389 : List (BitVec (edgeCount 11)) :=
  missing387_388 ++ missing388_389
abbrev records387_389 : List Blob :=
  records387_388 ++ records388_389
theorem aligned387_389 :
    AlignedValid 11 1 missing387_389 records387_389 :=
  aligned387_388.append aligned388_389

def missing386_389 : List (BitVec (edgeCount 11)) :=
  missing386_387 ++ missing387_389
abbrev records386_389 : List Blob :=
  records386_387 ++ records387_389
theorem aligned386_389 :
    AlignedValid 11 1 missing386_389 records386_389 :=
  aligned386_387.append aligned387_389

def missing384_389 : List (BitVec (edgeCount 11)) :=
  missing384_386 ++ missing386_389
abbrev records384_389 : List Blob :=
  records384_386 ++ records386_389
theorem aligned384_389 :
    AlignedValid 11 1 missing384_389 records384_389 :=
  aligned384_386.append aligned386_389

def missing389_390 : List (BitVec (edgeCount 11)) :=
  [missing389]
abbrev records389_390 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record389]
theorem aligned389_390 :
    AlignedValid 11 1 missing389_390 records389_390 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check389
    maskCheck389 AlignedValid.nil

def missing390_391 : List (BitVec (edgeCount 11)) :=
  [missing390]
abbrev records390_391 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record390]
theorem aligned390_391 :
    AlignedValid 11 1 missing390_391 records390_391 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check390
    maskCheck390 AlignedValid.nil

def missing389_391 : List (BitVec (edgeCount 11)) :=
  missing389_390 ++ missing390_391
abbrev records389_391 : List Blob :=
  records389_390 ++ records390_391
theorem aligned389_391 :
    AlignedValid 11 1 missing389_391 records389_391 :=
  aligned389_390.append aligned390_391

def missing391_392 : List (BitVec (edgeCount 11)) :=
  [missing391]
abbrev records391_392 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record391]
theorem aligned391_392 :
    AlignedValid 11 1 missing391_392 records391_392 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check391
    maskCheck391 AlignedValid.nil

def missing392_393 : List (BitVec (edgeCount 11)) :=
  [missing392]
abbrev records392_393 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record392]
theorem aligned392_393 :
    AlignedValid 11 1 missing392_393 records392_393 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check392
    maskCheck392 AlignedValid.nil

def missing393_394 : List (BitVec (edgeCount 11)) :=
  [missing393]
abbrev records393_394 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record393]
theorem aligned393_394 :
    AlignedValid 11 1 missing393_394 records393_394 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check393
    maskCheck393 AlignedValid.nil

def missing392_394 : List (BitVec (edgeCount 11)) :=
  missing392_393 ++ missing393_394
abbrev records392_394 : List Blob :=
  records392_393 ++ records393_394
theorem aligned392_394 :
    AlignedValid 11 1 missing392_394 records392_394 :=
  aligned392_393.append aligned393_394

def missing391_394 : List (BitVec (edgeCount 11)) :=
  missing391_392 ++ missing392_394
abbrev records391_394 : List Blob :=
  records391_392 ++ records392_394
theorem aligned391_394 :
    AlignedValid 11 1 missing391_394 records391_394 :=
  aligned391_392.append aligned392_394

def missing389_394 : List (BitVec (edgeCount 11)) :=
  missing389_391 ++ missing391_394
abbrev records389_394 : List Blob :=
  records389_391 ++ records391_394
theorem aligned389_394 :
    AlignedValid 11 1 missing389_394 records389_394 :=
  aligned389_391.append aligned391_394

def missing384_394 : List (BitVec (edgeCount 11)) :=
  missing384_389 ++ missing389_394
abbrev records384_394 : List Blob :=
  records384_389 ++ records389_394
theorem aligned384_394 :
    AlignedValid 11 1 missing384_394 records384_394 :=
  aligned384_389.append aligned389_394

def missing394_395 : List (BitVec (edgeCount 11)) :=
  [missing394]
abbrev records394_395 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record394]
theorem aligned394_395 :
    AlignedValid 11 1 missing394_395 records394_395 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check394
    maskCheck394 AlignedValid.nil

def missing395_396 : List (BitVec (edgeCount 11)) :=
  [missing395]
abbrev records395_396 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record395]
theorem aligned395_396 :
    AlignedValid 11 1 missing395_396 records395_396 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check395
    maskCheck395 AlignedValid.nil

def missing394_396 : List (BitVec (edgeCount 11)) :=
  missing394_395 ++ missing395_396
abbrev records394_396 : List Blob :=
  records394_395 ++ records395_396
theorem aligned394_396 :
    AlignedValid 11 1 missing394_396 records394_396 :=
  aligned394_395.append aligned395_396

def missing396_397 : List (BitVec (edgeCount 11)) :=
  [missing396]
abbrev records396_397 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record396]
theorem aligned396_397 :
    AlignedValid 11 1 missing396_397 records396_397 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check396
    maskCheck396 AlignedValid.nil

def missing397_398 : List (BitVec (edgeCount 11)) :=
  [missing397]
abbrev records397_398 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record397]
theorem aligned397_398 :
    AlignedValid 11 1 missing397_398 records397_398 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check397
    maskCheck397 AlignedValid.nil

def missing398_399 : List (BitVec (edgeCount 11)) :=
  [missing398]
abbrev records398_399 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record398]
theorem aligned398_399 :
    AlignedValid 11 1 missing398_399 records398_399 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check398
    maskCheck398 AlignedValid.nil

def missing397_399 : List (BitVec (edgeCount 11)) :=
  missing397_398 ++ missing398_399
abbrev records397_399 : List Blob :=
  records397_398 ++ records398_399
theorem aligned397_399 :
    AlignedValid 11 1 missing397_399 records397_399 :=
  aligned397_398.append aligned398_399

def missing396_399 : List (BitVec (edgeCount 11)) :=
  missing396_397 ++ missing397_399
abbrev records396_399 : List Blob :=
  records396_397 ++ records397_399
theorem aligned396_399 :
    AlignedValid 11 1 missing396_399 records396_399 :=
  aligned396_397.append aligned397_399

def missing394_399 : List (BitVec (edgeCount 11)) :=
  missing394_396 ++ missing396_399
abbrev records394_399 : List Blob :=
  records394_396 ++ records396_399
theorem aligned394_399 :
    AlignedValid 11 1 missing394_399 records394_399 :=
  aligned394_396.append aligned396_399

def missing399_400 : List (BitVec (edgeCount 11)) :=
  [missing399]
abbrev records399_400 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record399]
theorem aligned399_400 :
    AlignedValid 11 1 missing399_400 records399_400 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check399
    maskCheck399 AlignedValid.nil

def missing400_401 : List (BitVec (edgeCount 11)) :=
  [missing400]
abbrev records400_401 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record400]
theorem aligned400_401 :
    AlignedValid 11 1 missing400_401 records400_401 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check400
    maskCheck400 AlignedValid.nil

def missing399_401 : List (BitVec (edgeCount 11)) :=
  missing399_400 ++ missing400_401
abbrev records399_401 : List Blob :=
  records399_400 ++ records400_401
theorem aligned399_401 :
    AlignedValid 11 1 missing399_401 records399_401 :=
  aligned399_400.append aligned400_401

def missing401_402 : List (BitVec (edgeCount 11)) :=
  [missing401]
abbrev records401_402 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record401]
theorem aligned401_402 :
    AlignedValid 11 1 missing401_402 records401_402 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check401
    maskCheck401 AlignedValid.nil

def missing402_403 : List (BitVec (edgeCount 11)) :=
  [missing402]
abbrev records402_403 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record402]
theorem aligned402_403 :
    AlignedValid 11 1 missing402_403 records402_403 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check402
    maskCheck402 AlignedValid.nil

def missing403_404 : List (BitVec (edgeCount 11)) :=
  [missing403]
abbrev records403_404 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record403]
theorem aligned403_404 :
    AlignedValid 11 1 missing403_404 records403_404 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check403
    maskCheck403 AlignedValid.nil

def missing402_404 : List (BitVec (edgeCount 11)) :=
  missing402_403 ++ missing403_404
abbrev records402_404 : List Blob :=
  records402_403 ++ records403_404
theorem aligned402_404 :
    AlignedValid 11 1 missing402_404 records402_404 :=
  aligned402_403.append aligned403_404

def missing401_404 : List (BitVec (edgeCount 11)) :=
  missing401_402 ++ missing402_404
abbrev records401_404 : List Blob :=
  records401_402 ++ records402_404
theorem aligned401_404 :
    AlignedValid 11 1 missing401_404 records401_404 :=
  aligned401_402.append aligned402_404

def missing399_404 : List (BitVec (edgeCount 11)) :=
  missing399_401 ++ missing401_404
abbrev records399_404 : List Blob :=
  records399_401 ++ records401_404
theorem aligned399_404 :
    AlignedValid 11 1 missing399_404 records399_404 :=
  aligned399_401.append aligned401_404

def missing394_404 : List (BitVec (edgeCount 11)) :=
  missing394_399 ++ missing399_404
abbrev records394_404 : List Blob :=
  records394_399 ++ records399_404
theorem aligned394_404 :
    AlignedValid 11 1 missing394_404 records394_404 :=
  aligned394_399.append aligned399_404

def missing384_404 : List (BitVec (edgeCount 11)) :=
  missing384_394 ++ missing394_404
abbrev records384_404 : List Blob :=
  records384_394 ++ records394_404
theorem aligned384_404 :
    AlignedValid 11 1 missing384_404 records384_404 :=
  aligned384_394.append aligned394_404

def missing404_405 : List (BitVec (edgeCount 11)) :=
  [missing404]
abbrev records404_405 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record404]
theorem aligned404_405 :
    AlignedValid 11 1 missing404_405 records404_405 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check404
    maskCheck404 AlignedValid.nil

def missing405_406 : List (BitVec (edgeCount 11)) :=
  [missing405]
abbrev records405_406 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record405]
theorem aligned405_406 :
    AlignedValid 11 1 missing405_406 records405_406 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check405
    maskCheck405 AlignedValid.nil

def missing404_406 : List (BitVec (edgeCount 11)) :=
  missing404_405 ++ missing405_406
abbrev records404_406 : List Blob :=
  records404_405 ++ records405_406
theorem aligned404_406 :
    AlignedValid 11 1 missing404_406 records404_406 :=
  aligned404_405.append aligned405_406

def missing406_407 : List (BitVec (edgeCount 11)) :=
  [missing406]
abbrev records406_407 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record406]
theorem aligned406_407 :
    AlignedValid 11 1 missing406_407 records406_407 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check406
    maskCheck406 AlignedValid.nil

def missing407_408 : List (BitVec (edgeCount 11)) :=
  [missing407]
abbrev records407_408 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record407]
theorem aligned407_408 :
    AlignedValid 11 1 missing407_408 records407_408 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check407
    maskCheck407 AlignedValid.nil

def missing408_409 : List (BitVec (edgeCount 11)) :=
  [missing408]
abbrev records408_409 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record408]
theorem aligned408_409 :
    AlignedValid 11 1 missing408_409 records408_409 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check408
    maskCheck408 AlignedValid.nil

def missing407_409 : List (BitVec (edgeCount 11)) :=
  missing407_408 ++ missing408_409
abbrev records407_409 : List Blob :=
  records407_408 ++ records408_409
theorem aligned407_409 :
    AlignedValid 11 1 missing407_409 records407_409 :=
  aligned407_408.append aligned408_409

def missing406_409 : List (BitVec (edgeCount 11)) :=
  missing406_407 ++ missing407_409
abbrev records406_409 : List Blob :=
  records406_407 ++ records407_409
theorem aligned406_409 :
    AlignedValid 11 1 missing406_409 records406_409 :=
  aligned406_407.append aligned407_409

def missing404_409 : List (BitVec (edgeCount 11)) :=
  missing404_406 ++ missing406_409
abbrev records404_409 : List Blob :=
  records404_406 ++ records406_409
theorem aligned404_409 :
    AlignedValid 11 1 missing404_409 records404_409 :=
  aligned404_406.append aligned406_409

def missing409_410 : List (BitVec (edgeCount 11)) :=
  [missing409]
abbrev records409_410 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record409]
theorem aligned409_410 :
    AlignedValid 11 1 missing409_410 records409_410 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check409
    maskCheck409 AlignedValid.nil

def missing410_411 : List (BitVec (edgeCount 11)) :=
  [missing410]
abbrev records410_411 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record410]
theorem aligned410_411 :
    AlignedValid 11 1 missing410_411 records410_411 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check410
    maskCheck410 AlignedValid.nil

def missing409_411 : List (BitVec (edgeCount 11)) :=
  missing409_410 ++ missing410_411
abbrev records409_411 : List Blob :=
  records409_410 ++ records410_411
theorem aligned409_411 :
    AlignedValid 11 1 missing409_411 records409_411 :=
  aligned409_410.append aligned410_411

def missing411_412 : List (BitVec (edgeCount 11)) :=
  [missing411]
abbrev records411_412 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record411]
theorem aligned411_412 :
    AlignedValid 11 1 missing411_412 records411_412 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check411
    maskCheck411 AlignedValid.nil

def missing412_413 : List (BitVec (edgeCount 11)) :=
  [missing412]
abbrev records412_413 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record412]
theorem aligned412_413 :
    AlignedValid 11 1 missing412_413 records412_413 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check412
    maskCheck412 AlignedValid.nil

def missing413_414 : List (BitVec (edgeCount 11)) :=
  [missing413]
abbrev records413_414 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record413]
theorem aligned413_414 :
    AlignedValid 11 1 missing413_414 records413_414 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check413
    maskCheck413 AlignedValid.nil

def missing412_414 : List (BitVec (edgeCount 11)) :=
  missing412_413 ++ missing413_414
abbrev records412_414 : List Blob :=
  records412_413 ++ records413_414
theorem aligned412_414 :
    AlignedValid 11 1 missing412_414 records412_414 :=
  aligned412_413.append aligned413_414

def missing411_414 : List (BitVec (edgeCount 11)) :=
  missing411_412 ++ missing412_414
abbrev records411_414 : List Blob :=
  records411_412 ++ records412_414
theorem aligned411_414 :
    AlignedValid 11 1 missing411_414 records411_414 :=
  aligned411_412.append aligned412_414

def missing409_414 : List (BitVec (edgeCount 11)) :=
  missing409_411 ++ missing411_414
abbrev records409_414 : List Blob :=
  records409_411 ++ records411_414
theorem aligned409_414 :
    AlignedValid 11 1 missing409_414 records409_414 :=
  aligned409_411.append aligned411_414

def missing404_414 : List (BitVec (edgeCount 11)) :=
  missing404_409 ++ missing409_414
abbrev records404_414 : List Blob :=
  records404_409 ++ records409_414
theorem aligned404_414 :
    AlignedValid 11 1 missing404_414 records404_414 :=
  aligned404_409.append aligned409_414

def missing414_415 : List (BitVec (edgeCount 11)) :=
  [missing414]
abbrev records414_415 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record414]
theorem aligned414_415 :
    AlignedValid 11 1 missing414_415 records414_415 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check414
    maskCheck414 AlignedValid.nil

def missing415_416 : List (BitVec (edgeCount 11)) :=
  [missing415]
abbrev records415_416 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record415]
theorem aligned415_416 :
    AlignedValid 11 1 missing415_416 records415_416 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check415
    maskCheck415 AlignedValid.nil

def missing414_416 : List (BitVec (edgeCount 11)) :=
  missing414_415 ++ missing415_416
abbrev records414_416 : List Blob :=
  records414_415 ++ records415_416
theorem aligned414_416 :
    AlignedValid 11 1 missing414_416 records414_416 :=
  aligned414_415.append aligned415_416

def missing416_417 : List (BitVec (edgeCount 11)) :=
  [missing416]
abbrev records416_417 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record416]
theorem aligned416_417 :
    AlignedValid 11 1 missing416_417 records416_417 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check416
    maskCheck416 AlignedValid.nil

def missing417_418 : List (BitVec (edgeCount 11)) :=
  [missing417]
abbrev records417_418 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record417]
theorem aligned417_418 :
    AlignedValid 11 1 missing417_418 records417_418 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check417
    maskCheck417 AlignedValid.nil

def missing418_419 : List (BitVec (edgeCount 11)) :=
  [missing418]
abbrev records418_419 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record418]
theorem aligned418_419 :
    AlignedValid 11 1 missing418_419 records418_419 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check418
    maskCheck418 AlignedValid.nil

def missing417_419 : List (BitVec (edgeCount 11)) :=
  missing417_418 ++ missing418_419
abbrev records417_419 : List Blob :=
  records417_418 ++ records418_419
theorem aligned417_419 :
    AlignedValid 11 1 missing417_419 records417_419 :=
  aligned417_418.append aligned418_419

def missing416_419 : List (BitVec (edgeCount 11)) :=
  missing416_417 ++ missing417_419
abbrev records416_419 : List Blob :=
  records416_417 ++ records417_419
theorem aligned416_419 :
    AlignedValid 11 1 missing416_419 records416_419 :=
  aligned416_417.append aligned417_419

def missing414_419 : List (BitVec (edgeCount 11)) :=
  missing414_416 ++ missing416_419
abbrev records414_419 : List Blob :=
  records414_416 ++ records416_419
theorem aligned414_419 :
    AlignedValid 11 1 missing414_419 records414_419 :=
  aligned414_416.append aligned416_419

def missing419_420 : List (BitVec (edgeCount 11)) :=
  [missing419]
abbrev records419_420 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record419]
theorem aligned419_420 :
    AlignedValid 11 1 missing419_420 records419_420 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check419
    maskCheck419 AlignedValid.nil

def missing420_421 : List (BitVec (edgeCount 11)) :=
  [missing420]
abbrev records420_421 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record420]
theorem aligned420_421 :
    AlignedValid 11 1 missing420_421 records420_421 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check420
    maskCheck420 AlignedValid.nil

def missing421_422 : List (BitVec (edgeCount 11)) :=
  [missing421]
abbrev records421_422 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record421]
theorem aligned421_422 :
    AlignedValid 11 1 missing421_422 records421_422 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check421
    maskCheck421 AlignedValid.nil

def missing420_422 : List (BitVec (edgeCount 11)) :=
  missing420_421 ++ missing421_422
abbrev records420_422 : List Blob :=
  records420_421 ++ records421_422
theorem aligned420_422 :
    AlignedValid 11 1 missing420_422 records420_422 :=
  aligned420_421.append aligned421_422

def missing419_422 : List (BitVec (edgeCount 11)) :=
  missing419_420 ++ missing420_422
abbrev records419_422 : List Blob :=
  records419_420 ++ records420_422
theorem aligned419_422 :
    AlignedValid 11 1 missing419_422 records419_422 :=
  aligned419_420.append aligned420_422

def missing422_423 : List (BitVec (edgeCount 11)) :=
  [missing422]
abbrev records422_423 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record422]
theorem aligned422_423 :
    AlignedValid 11 1 missing422_423 records422_423 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check422
    maskCheck422 AlignedValid.nil

def missing423_424 : List (BitVec (edgeCount 11)) :=
  [missing423]
abbrev records423_424 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record423]
theorem aligned423_424 :
    AlignedValid 11 1 missing423_424 records423_424 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check423
    maskCheck423 AlignedValid.nil

def missing424_425 : List (BitVec (edgeCount 11)) :=
  [missing424]
abbrev records424_425 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record424]
theorem aligned424_425 :
    AlignedValid 11 1 missing424_425 records424_425 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check424
    maskCheck424 AlignedValid.nil

def missing423_425 : List (BitVec (edgeCount 11)) :=
  missing423_424 ++ missing424_425
abbrev records423_425 : List Blob :=
  records423_424 ++ records424_425
theorem aligned423_425 :
    AlignedValid 11 1 missing423_425 records423_425 :=
  aligned423_424.append aligned424_425

def missing422_425 : List (BitVec (edgeCount 11)) :=
  missing422_423 ++ missing423_425
abbrev records422_425 : List Blob :=
  records422_423 ++ records423_425
theorem aligned422_425 :
    AlignedValid 11 1 missing422_425 records422_425 :=
  aligned422_423.append aligned423_425

def missing419_425 : List (BitVec (edgeCount 11)) :=
  missing419_422 ++ missing422_425
abbrev records419_425 : List Blob :=
  records419_422 ++ records422_425
theorem aligned419_425 :
    AlignedValid 11 1 missing419_425 records419_425 :=
  aligned419_422.append aligned422_425

def missing414_425 : List (BitVec (edgeCount 11)) :=
  missing414_419 ++ missing419_425
abbrev records414_425 : List Blob :=
  records414_419 ++ records419_425
theorem aligned414_425 :
    AlignedValid 11 1 missing414_425 records414_425 :=
  aligned414_419.append aligned419_425

def missing404_425 : List (BitVec (edgeCount 11)) :=
  missing404_414 ++ missing414_425
abbrev records404_425 : List Blob :=
  records404_414 ++ records414_425
theorem aligned404_425 :
    AlignedValid 11 1 missing404_425 records404_425 :=
  aligned404_414.append aligned414_425

def missing384_425 : List (BitVec (edgeCount 11)) :=
  missing384_404 ++ missing404_425
abbrev records384_425 : List Blob :=
  records384_404 ++ records404_425
theorem aligned384_425 :
    AlignedValid 11 1 missing384_425 records384_425 :=
  aligned384_404.append aligned404_425

def missing425_426 : List (BitVec (edgeCount 11)) :=
  [missing425]
abbrev records425_426 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record425]
theorem aligned425_426 :
    AlignedValid 11 1 missing425_426 records425_426 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check425
    maskCheck425 AlignedValid.nil

def missing426_427 : List (BitVec (edgeCount 11)) :=
  [missing426]
abbrev records426_427 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record426]
theorem aligned426_427 :
    AlignedValid 11 1 missing426_427 records426_427 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check426
    maskCheck426 AlignedValid.nil

def missing425_427 : List (BitVec (edgeCount 11)) :=
  missing425_426 ++ missing426_427
abbrev records425_427 : List Blob :=
  records425_426 ++ records426_427
theorem aligned425_427 :
    AlignedValid 11 1 missing425_427 records425_427 :=
  aligned425_426.append aligned426_427

def missing427_428 : List (BitVec (edgeCount 11)) :=
  [missing427]
abbrev records427_428 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record427]
theorem aligned427_428 :
    AlignedValid 11 1 missing427_428 records427_428 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check427
    maskCheck427 AlignedValid.nil

def missing428_429 : List (BitVec (edgeCount 11)) :=
  [missing428]
abbrev records428_429 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record428]
theorem aligned428_429 :
    AlignedValid 11 1 missing428_429 records428_429 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check428
    maskCheck428 AlignedValid.nil

def missing429_430 : List (BitVec (edgeCount 11)) :=
  [missing429]
abbrev records429_430 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record429]
theorem aligned429_430 :
    AlignedValid 11 1 missing429_430 records429_430 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check429
    maskCheck429 AlignedValid.nil

def missing428_430 : List (BitVec (edgeCount 11)) :=
  missing428_429 ++ missing429_430
abbrev records428_430 : List Blob :=
  records428_429 ++ records429_430
theorem aligned428_430 :
    AlignedValid 11 1 missing428_430 records428_430 :=
  aligned428_429.append aligned429_430

def missing427_430 : List (BitVec (edgeCount 11)) :=
  missing427_428 ++ missing428_430
abbrev records427_430 : List Blob :=
  records427_428 ++ records428_430
theorem aligned427_430 :
    AlignedValid 11 1 missing427_430 records427_430 :=
  aligned427_428.append aligned428_430

def missing425_430 : List (BitVec (edgeCount 11)) :=
  missing425_427 ++ missing427_430
abbrev records425_430 : List Blob :=
  records425_427 ++ records427_430
theorem aligned425_430 :
    AlignedValid 11 1 missing425_430 records425_430 :=
  aligned425_427.append aligned427_430

def missing430_431 : List (BitVec (edgeCount 11)) :=
  [missing430]
abbrev records430_431 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record430]
theorem aligned430_431 :
    AlignedValid 11 1 missing430_431 records430_431 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check430
    maskCheck430 AlignedValid.nil

def missing431_432 : List (BitVec (edgeCount 11)) :=
  [missing431]
abbrev records431_432 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record431]
theorem aligned431_432 :
    AlignedValid 11 1 missing431_432 records431_432 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check431
    maskCheck431 AlignedValid.nil

def missing430_432 : List (BitVec (edgeCount 11)) :=
  missing430_431 ++ missing431_432
abbrev records430_432 : List Blob :=
  records430_431 ++ records431_432
theorem aligned430_432 :
    AlignedValid 11 1 missing430_432 records430_432 :=
  aligned430_431.append aligned431_432

def missing432_433 : List (BitVec (edgeCount 11)) :=
  [missing432]
abbrev records432_433 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record432]
theorem aligned432_433 :
    AlignedValid 11 1 missing432_433 records432_433 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check432
    maskCheck432 AlignedValid.nil

def missing433_434 : List (BitVec (edgeCount 11)) :=
  [missing433]
abbrev records433_434 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record433]
theorem aligned433_434 :
    AlignedValid 11 1 missing433_434 records433_434 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check433
    maskCheck433 AlignedValid.nil

def missing434_435 : List (BitVec (edgeCount 11)) :=
  [missing434]
abbrev records434_435 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record434]
theorem aligned434_435 :
    AlignedValid 11 1 missing434_435 records434_435 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check434
    maskCheck434 AlignedValid.nil

def missing433_435 : List (BitVec (edgeCount 11)) :=
  missing433_434 ++ missing434_435
abbrev records433_435 : List Blob :=
  records433_434 ++ records434_435
theorem aligned433_435 :
    AlignedValid 11 1 missing433_435 records433_435 :=
  aligned433_434.append aligned434_435

def missing432_435 : List (BitVec (edgeCount 11)) :=
  missing432_433 ++ missing433_435
abbrev records432_435 : List Blob :=
  records432_433 ++ records433_435
theorem aligned432_435 :
    AlignedValid 11 1 missing432_435 records432_435 :=
  aligned432_433.append aligned433_435

def missing430_435 : List (BitVec (edgeCount 11)) :=
  missing430_432 ++ missing432_435
abbrev records430_435 : List Blob :=
  records430_432 ++ records432_435
theorem aligned430_435 :
    AlignedValid 11 1 missing430_435 records430_435 :=
  aligned430_432.append aligned432_435

def missing425_435 : List (BitVec (edgeCount 11)) :=
  missing425_430 ++ missing430_435
abbrev records425_435 : List Blob :=
  records425_430 ++ records430_435
theorem aligned425_435 :
    AlignedValid 11 1 missing425_435 records425_435 :=
  aligned425_430.append aligned430_435

def missing435_436 : List (BitVec (edgeCount 11)) :=
  [missing435]
abbrev records435_436 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record435]
theorem aligned435_436 :
    AlignedValid 11 1 missing435_436 records435_436 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check435
    maskCheck435 AlignedValid.nil

def missing436_437 : List (BitVec (edgeCount 11)) :=
  [missing436]
abbrev records436_437 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record436]
theorem aligned436_437 :
    AlignedValid 11 1 missing436_437 records436_437 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check436
    maskCheck436 AlignedValid.nil

def missing435_437 : List (BitVec (edgeCount 11)) :=
  missing435_436 ++ missing436_437
abbrev records435_437 : List Blob :=
  records435_436 ++ records436_437
theorem aligned435_437 :
    AlignedValid 11 1 missing435_437 records435_437 :=
  aligned435_436.append aligned436_437

def missing437_438 : List (BitVec (edgeCount 11)) :=
  [missing437]
abbrev records437_438 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record437]
theorem aligned437_438 :
    AlignedValid 11 1 missing437_438 records437_438 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check437
    maskCheck437 AlignedValid.nil

def missing438_439 : List (BitVec (edgeCount 11)) :=
  [missing438]
abbrev records438_439 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record438]
theorem aligned438_439 :
    AlignedValid 11 1 missing438_439 records438_439 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check438
    maskCheck438 AlignedValid.nil

def missing439_440 : List (BitVec (edgeCount 11)) :=
  [missing439]
abbrev records439_440 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record439]
theorem aligned439_440 :
    AlignedValid 11 1 missing439_440 records439_440 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check439
    maskCheck439 AlignedValid.nil

def missing438_440 : List (BitVec (edgeCount 11)) :=
  missing438_439 ++ missing439_440
abbrev records438_440 : List Blob :=
  records438_439 ++ records439_440
theorem aligned438_440 :
    AlignedValid 11 1 missing438_440 records438_440 :=
  aligned438_439.append aligned439_440

def missing437_440 : List (BitVec (edgeCount 11)) :=
  missing437_438 ++ missing438_440
abbrev records437_440 : List Blob :=
  records437_438 ++ records438_440
theorem aligned437_440 :
    AlignedValid 11 1 missing437_440 records437_440 :=
  aligned437_438.append aligned438_440

def missing435_440 : List (BitVec (edgeCount 11)) :=
  missing435_437 ++ missing437_440
abbrev records435_440 : List Blob :=
  records435_437 ++ records437_440
theorem aligned435_440 :
    AlignedValid 11 1 missing435_440 records435_440 :=
  aligned435_437.append aligned437_440

def missing440_441 : List (BitVec (edgeCount 11)) :=
  [missing440]
abbrev records440_441 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record440]
theorem aligned440_441 :
    AlignedValid 11 1 missing440_441 records440_441 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check440
    maskCheck440 AlignedValid.nil

def missing441_442 : List (BitVec (edgeCount 11)) :=
  [missing441]
abbrev records441_442 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record441]
theorem aligned441_442 :
    AlignedValid 11 1 missing441_442 records441_442 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check441
    maskCheck441 AlignedValid.nil

def missing442_443 : List (BitVec (edgeCount 11)) :=
  [missing442]
abbrev records442_443 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record442]
theorem aligned442_443 :
    AlignedValid 11 1 missing442_443 records442_443 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check442
    maskCheck442 AlignedValid.nil

def missing441_443 : List (BitVec (edgeCount 11)) :=
  missing441_442 ++ missing442_443
abbrev records441_443 : List Blob :=
  records441_442 ++ records442_443
theorem aligned441_443 :
    AlignedValid 11 1 missing441_443 records441_443 :=
  aligned441_442.append aligned442_443

def missing440_443 : List (BitVec (edgeCount 11)) :=
  missing440_441 ++ missing441_443
abbrev records440_443 : List Blob :=
  records440_441 ++ records441_443
theorem aligned440_443 :
    AlignedValid 11 1 missing440_443 records440_443 :=
  aligned440_441.append aligned441_443

def missing443_444 : List (BitVec (edgeCount 11)) :=
  [missing443]
abbrev records443_444 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record443]
theorem aligned443_444 :
    AlignedValid 11 1 missing443_444 records443_444 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check443
    maskCheck443 AlignedValid.nil

def missing444_445 : List (BitVec (edgeCount 11)) :=
  [missing444]
abbrev records444_445 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record444]
theorem aligned444_445 :
    AlignedValid 11 1 missing444_445 records444_445 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check444
    maskCheck444 AlignedValid.nil

def missing445_446 : List (BitVec (edgeCount 11)) :=
  [missing445]
abbrev records445_446 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record445]
theorem aligned445_446 :
    AlignedValid 11 1 missing445_446 records445_446 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check445
    maskCheck445 AlignedValid.nil

def missing444_446 : List (BitVec (edgeCount 11)) :=
  missing444_445 ++ missing445_446
abbrev records444_446 : List Blob :=
  records444_445 ++ records445_446
theorem aligned444_446 :
    AlignedValid 11 1 missing444_446 records444_446 :=
  aligned444_445.append aligned445_446

def missing443_446 : List (BitVec (edgeCount 11)) :=
  missing443_444 ++ missing444_446
abbrev records443_446 : List Blob :=
  records443_444 ++ records444_446
theorem aligned443_446 :
    AlignedValid 11 1 missing443_446 records443_446 :=
  aligned443_444.append aligned444_446

def missing440_446 : List (BitVec (edgeCount 11)) :=
  missing440_443 ++ missing443_446
abbrev records440_446 : List Blob :=
  records440_443 ++ records443_446
theorem aligned440_446 :
    AlignedValid 11 1 missing440_446 records440_446 :=
  aligned440_443.append aligned443_446

def missing435_446 : List (BitVec (edgeCount 11)) :=
  missing435_440 ++ missing440_446
abbrev records435_446 : List Blob :=
  records435_440 ++ records440_446
theorem aligned435_446 :
    AlignedValid 11 1 missing435_446 records435_446 :=
  aligned435_440.append aligned440_446

def missing425_446 : List (BitVec (edgeCount 11)) :=
  missing425_435 ++ missing435_446
abbrev records425_446 : List Blob :=
  records425_435 ++ records435_446
theorem aligned425_446 :
    AlignedValid 11 1 missing425_446 records425_446 :=
  aligned425_435.append aligned435_446

def missing446_447 : List (BitVec (edgeCount 11)) :=
  [missing446]
abbrev records446_447 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record446]
theorem aligned446_447 :
    AlignedValid 11 1 missing446_447 records446_447 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check446
    maskCheck446 AlignedValid.nil

def missing447_448 : List (BitVec (edgeCount 11)) :=
  [missing447]
abbrev records447_448 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record447]
theorem aligned447_448 :
    AlignedValid 11 1 missing447_448 records447_448 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check447
    maskCheck447 AlignedValid.nil

def missing446_448 : List (BitVec (edgeCount 11)) :=
  missing446_447 ++ missing447_448
abbrev records446_448 : List Blob :=
  records446_447 ++ records447_448
theorem aligned446_448 :
    AlignedValid 11 1 missing446_448 records446_448 :=
  aligned446_447.append aligned447_448

def missing448_449 : List (BitVec (edgeCount 11)) :=
  [missing448]
abbrev records448_449 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record448]
theorem aligned448_449 :
    AlignedValid 11 1 missing448_449 records448_449 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check448
    maskCheck448 AlignedValid.nil

def missing449_450 : List (BitVec (edgeCount 11)) :=
  [missing449]
abbrev records449_450 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record449]
theorem aligned449_450 :
    AlignedValid 11 1 missing449_450 records449_450 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check449
    maskCheck449 AlignedValid.nil

def missing450_451 : List (BitVec (edgeCount 11)) :=
  [missing450]
abbrev records450_451 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record450]
theorem aligned450_451 :
    AlignedValid 11 1 missing450_451 records450_451 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check450
    maskCheck450 AlignedValid.nil

def missing449_451 : List (BitVec (edgeCount 11)) :=
  missing449_450 ++ missing450_451
abbrev records449_451 : List Blob :=
  records449_450 ++ records450_451
theorem aligned449_451 :
    AlignedValid 11 1 missing449_451 records449_451 :=
  aligned449_450.append aligned450_451

def missing448_451 : List (BitVec (edgeCount 11)) :=
  missing448_449 ++ missing449_451
abbrev records448_451 : List Blob :=
  records448_449 ++ records449_451
theorem aligned448_451 :
    AlignedValid 11 1 missing448_451 records448_451 :=
  aligned448_449.append aligned449_451

def missing446_451 : List (BitVec (edgeCount 11)) :=
  missing446_448 ++ missing448_451
abbrev records446_451 : List Blob :=
  records446_448 ++ records448_451
theorem aligned446_451 :
    AlignedValid 11 1 missing446_451 records446_451 :=
  aligned446_448.append aligned448_451

def missing451_452 : List (BitVec (edgeCount 11)) :=
  [missing451]
abbrev records451_452 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record451]
theorem aligned451_452 :
    AlignedValid 11 1 missing451_452 records451_452 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check451
    maskCheck451 AlignedValid.nil

def missing452_453 : List (BitVec (edgeCount 11)) :=
  [missing452]
abbrev records452_453 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record452]
theorem aligned452_453 :
    AlignedValid 11 1 missing452_453 records452_453 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check452
    maskCheck452 AlignedValid.nil

def missing451_453 : List (BitVec (edgeCount 11)) :=
  missing451_452 ++ missing452_453
abbrev records451_453 : List Blob :=
  records451_452 ++ records452_453
theorem aligned451_453 :
    AlignedValid 11 1 missing451_453 records451_453 :=
  aligned451_452.append aligned452_453

def missing453_454 : List (BitVec (edgeCount 11)) :=
  [missing453]
abbrev records453_454 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record453]
theorem aligned453_454 :
    AlignedValid 11 1 missing453_454 records453_454 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check453
    maskCheck453 AlignedValid.nil

def missing454_455 : List (BitVec (edgeCount 11)) :=
  [missing454]
abbrev records454_455 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record454]
theorem aligned454_455 :
    AlignedValid 11 1 missing454_455 records454_455 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check454
    maskCheck454 AlignedValid.nil

def missing455_456 : List (BitVec (edgeCount 11)) :=
  [missing455]
abbrev records455_456 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record455]
theorem aligned455_456 :
    AlignedValid 11 1 missing455_456 records455_456 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check455
    maskCheck455 AlignedValid.nil

def missing454_456 : List (BitVec (edgeCount 11)) :=
  missing454_455 ++ missing455_456
abbrev records454_456 : List Blob :=
  records454_455 ++ records455_456
theorem aligned454_456 :
    AlignedValid 11 1 missing454_456 records454_456 :=
  aligned454_455.append aligned455_456

def missing453_456 : List (BitVec (edgeCount 11)) :=
  missing453_454 ++ missing454_456
abbrev records453_456 : List Blob :=
  records453_454 ++ records454_456
theorem aligned453_456 :
    AlignedValid 11 1 missing453_456 records453_456 :=
  aligned453_454.append aligned454_456

def missing451_456 : List (BitVec (edgeCount 11)) :=
  missing451_453 ++ missing453_456
abbrev records451_456 : List Blob :=
  records451_453 ++ records453_456
theorem aligned451_456 :
    AlignedValid 11 1 missing451_456 records451_456 :=
  aligned451_453.append aligned453_456

def missing446_456 : List (BitVec (edgeCount 11)) :=
  missing446_451 ++ missing451_456
abbrev records446_456 : List Blob :=
  records446_451 ++ records451_456
theorem aligned446_456 :
    AlignedValid 11 1 missing446_456 records446_456 :=
  aligned446_451.append aligned451_456

def missing456_457 : List (BitVec (edgeCount 11)) :=
  [missing456]
abbrev records456_457 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record456]
theorem aligned456_457 :
    AlignedValid 11 1 missing456_457 records456_457 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check456
    maskCheck456 AlignedValid.nil

def missing457_458 : List (BitVec (edgeCount 11)) :=
  [missing457]
abbrev records457_458 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record457]
theorem aligned457_458 :
    AlignedValid 11 1 missing457_458 records457_458 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check457
    maskCheck457 AlignedValid.nil

def missing456_458 : List (BitVec (edgeCount 11)) :=
  missing456_457 ++ missing457_458
abbrev records456_458 : List Blob :=
  records456_457 ++ records457_458
theorem aligned456_458 :
    AlignedValid 11 1 missing456_458 records456_458 :=
  aligned456_457.append aligned457_458

def missing458_459 : List (BitVec (edgeCount 11)) :=
  [missing458]
abbrev records458_459 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record458]
theorem aligned458_459 :
    AlignedValid 11 1 missing458_459 records458_459 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check458
    maskCheck458 AlignedValid.nil

def missing459_460 : List (BitVec (edgeCount 11)) :=
  [missing459]
abbrev records459_460 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record459]
theorem aligned459_460 :
    AlignedValid 11 1 missing459_460 records459_460 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check459
    maskCheck459 AlignedValid.nil

def missing460_461 : List (BitVec (edgeCount 11)) :=
  [missing460]
abbrev records460_461 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record460]
theorem aligned460_461 :
    AlignedValid 11 1 missing460_461 records460_461 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check460
    maskCheck460 AlignedValid.nil

def missing459_461 : List (BitVec (edgeCount 11)) :=
  missing459_460 ++ missing460_461
abbrev records459_461 : List Blob :=
  records459_460 ++ records460_461
theorem aligned459_461 :
    AlignedValid 11 1 missing459_461 records459_461 :=
  aligned459_460.append aligned460_461

def missing458_461 : List (BitVec (edgeCount 11)) :=
  missing458_459 ++ missing459_461
abbrev records458_461 : List Blob :=
  records458_459 ++ records459_461
theorem aligned458_461 :
    AlignedValid 11 1 missing458_461 records458_461 :=
  aligned458_459.append aligned459_461

def missing456_461 : List (BitVec (edgeCount 11)) :=
  missing456_458 ++ missing458_461
abbrev records456_461 : List Blob :=
  records456_458 ++ records458_461
theorem aligned456_461 :
    AlignedValid 11 1 missing456_461 records456_461 :=
  aligned456_458.append aligned458_461

def missing461_462 : List (BitVec (edgeCount 11)) :=
  [missing461]
abbrev records461_462 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record461]
theorem aligned461_462 :
    AlignedValid 11 1 missing461_462 records461_462 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check461
    maskCheck461 AlignedValid.nil

def missing462_463 : List (BitVec (edgeCount 11)) :=
  [missing462]
abbrev records462_463 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record462]
theorem aligned462_463 :
    AlignedValid 11 1 missing462_463 records462_463 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check462
    maskCheck462 AlignedValid.nil

def missing463_464 : List (BitVec (edgeCount 11)) :=
  [missing463]
abbrev records463_464 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record463]
theorem aligned463_464 :
    AlignedValid 11 1 missing463_464 records463_464 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check463
    maskCheck463 AlignedValid.nil

def missing462_464 : List (BitVec (edgeCount 11)) :=
  missing462_463 ++ missing463_464
abbrev records462_464 : List Blob :=
  records462_463 ++ records463_464
theorem aligned462_464 :
    AlignedValid 11 1 missing462_464 records462_464 :=
  aligned462_463.append aligned463_464

def missing461_464 : List (BitVec (edgeCount 11)) :=
  missing461_462 ++ missing462_464
abbrev records461_464 : List Blob :=
  records461_462 ++ records462_464
theorem aligned461_464 :
    AlignedValid 11 1 missing461_464 records461_464 :=
  aligned461_462.append aligned462_464

def missing464_465 : List (BitVec (edgeCount 11)) :=
  [missing464]
abbrev records464_465 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record464]
theorem aligned464_465 :
    AlignedValid 11 1 missing464_465 records464_465 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check464
    maskCheck464 AlignedValid.nil

def missing465_466 : List (BitVec (edgeCount 11)) :=
  [missing465]
abbrev records465_466 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record465]
theorem aligned465_466 :
    AlignedValid 11 1 missing465_466 records465_466 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check465
    maskCheck465 AlignedValid.nil

def missing466_467 : List (BitVec (edgeCount 11)) :=
  [missing466]
abbrev records466_467 : List Blob :=
  [StrongPackedBucketN11A1Shard003.record466]
theorem aligned466_467 :
    AlignedValid 11 1 missing466_467 records466_467 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11A1Shard003.check466
    maskCheck466 AlignedValid.nil

def missing465_467 : List (BitVec (edgeCount 11)) :=
  missing465_466 ++ missing466_467
abbrev records465_467 : List Blob :=
  records465_466 ++ records466_467
theorem aligned465_467 :
    AlignedValid 11 1 missing465_467 records465_467 :=
  aligned465_466.append aligned466_467

def missing464_467 : List (BitVec (edgeCount 11)) :=
  missing464_465 ++ missing465_467
abbrev records464_467 : List Blob :=
  records464_465 ++ records465_467
theorem aligned464_467 :
    AlignedValid 11 1 missing464_467 records464_467 :=
  aligned464_465.append aligned465_467

def missing461_467 : List (BitVec (edgeCount 11)) :=
  missing461_464 ++ missing464_467
abbrev records461_467 : List Blob :=
  records461_464 ++ records464_467
theorem aligned461_467 :
    AlignedValid 11 1 missing461_467 records461_467 :=
  aligned461_464.append aligned464_467

def missing456_467 : List (BitVec (edgeCount 11)) :=
  missing456_461 ++ missing461_467
abbrev records456_467 : List Blob :=
  records456_461 ++ records461_467
theorem aligned456_467 :
    AlignedValid 11 1 missing456_467 records456_467 :=
  aligned456_461.append aligned461_467

def missing446_467 : List (BitVec (edgeCount 11)) :=
  missing446_456 ++ missing456_467
abbrev records446_467 : List Blob :=
  records446_456 ++ records456_467
theorem aligned446_467 :
    AlignedValid 11 1 missing446_467 records446_467 :=
  aligned446_456.append aligned456_467

def missing425_467 : List (BitVec (edgeCount 11)) :=
  missing425_446 ++ missing446_467
abbrev records425_467 : List Blob :=
  records425_446 ++ records446_467
theorem aligned425_467 :
    AlignedValid 11 1 missing425_467 records425_467 :=
  aligned425_446.append aligned446_467

def missing384_467 : List (BitVec (edgeCount 11)) :=
  missing384_425 ++ missing425_467
abbrev records384_467 : List Blob :=
  records384_425 ++ records425_467
theorem aligned384_467 :
    AlignedValid 11 1 missing384_467 records384_467 :=
  aligned384_425.append aligned425_467

abbrev missing : List (BitVec (edgeCount 11)) :=
  missing384_467
abbrev records : List Blob := records384_467
theorem aligned : AlignedValid 11 1 missing records :=
  aligned384_467

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A1AlignedShard003

