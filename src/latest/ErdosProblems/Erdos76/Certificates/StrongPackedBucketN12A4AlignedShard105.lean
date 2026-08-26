/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard105

/-! Decode-only alignment checks for n=12, a=4, records 13440--13567. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard105

open PackedBucketCertificate

def missing13440 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1121572573212049408
theorem maskCheck13440 :
    checkMaskFor missing13440 StrongPackedBucketN12A4Shard105.record13440 = true := by
  decide

def missing13441 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2130378889743040512
theorem maskCheck13441 :
    checkMaskFor missing13441 StrongPackedBucketN12A4Shard105.record13441 = true := by
  decide

def missing13442 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2202436483780968448
theorem maskCheck13442 :
    checkMaskFor missing13442 StrongPackedBucketN12A4Shard105.record13442 = true := by
  decide

def missing13443 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2238465280799932416
theorem maskCheck13443 :
    checkMaskFor missing13443 StrongPackedBucketN12A4Shard105.record13443 = true := by
  decide

def missing13444 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4364164304918806528
theorem maskCheck13444 :
    checkMaskFor missing13444 StrongPackedBucketN12A4Shard105.record13444 = true := by
  decide

def missing13445 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4400193101937770496
theorem maskCheck13445 :
    checkMaskFor missing13445 StrongPackedBucketN12A4Shard105.record13445 = true := by
  decide

def missing13446 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4472250695975698432
theorem maskCheck13446 :
    checkMaskFor missing13446 StrongPackedBucketN12A4Shard105.record13446 = true := by
  decide

def missing13447 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5156797839336013824
theorem maskCheck13447 :
    checkMaskFor missing13447 StrongPackedBucketN12A4Shard105.record13447 = true := by
  decide

def missing13448 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5589143403563581440
theorem maskCheck13448 :
    checkMaskFor missing13448 StrongPackedBucketN12A4Shard105.record13448 = true := by
  decide

def missing13449 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5661200997601509376
theorem maskCheck13449 :
    checkMaskFor missing13449 StrongPackedBucketN12A4Shard105.record13449 = true := by
  decide

def missing13450 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5697229794620473344
theorem maskCheck13450 :
    checkMaskFor missing13450 StrongPackedBucketN12A4Shard105.record13450 = true := by
  decide

def missing13451 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6670007314132500480
theorem maskCheck13451 :
    checkMaskFor missing13451 StrongPackedBucketN12A4Shard105.record13451 = true := by
  decide

def missing13452 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6706036111151464448
theorem maskCheck13452 :
    checkMaskFor missing13452 StrongPackedBucketN12A4Shard105.record13452 = true := by
  decide

def missing13453 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6778093705189392384
theorem maskCheck13453 :
    checkMaskFor missing13453 StrongPackedBucketN12A4Shard105.record13453 = true := by
  decide

def missing13454 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8939821526327230464
theorem maskCheck13454 :
    checkMaskFor missing13454 StrongPackedBucketN12A4Shard105.record13454 = true := by
  decide

def missing13455 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9768483857763401728
theorem maskCheck13455 :
    checkMaskFor missing13455 StrongPackedBucketN12A4Shard105.record13455 = true := by
  decide

def missing13456 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10200829421990969344
theorem maskCheck13456 :
    checkMaskFor missing13456 StrongPackedBucketN12A4Shard105.record13456 = true := by
  decide

def missing13457 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10308915813047861248
theorem maskCheck13457 :
    checkMaskFor missing13457 StrongPackedBucketN12A4Shard105.record13457 = true := by
  decide

def missing13458 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11317722129578852352
theorem maskCheck13458 :
    checkMaskFor missing13458 StrongPackedBucketN12A4Shard105.record13458 = true := by
  decide

def missing13459 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14091939500039077888
theorem maskCheck13459 :
    checkMaskFor missing13459 StrongPackedBucketN12A4Shard105.record13459 = true := by
  decide

def missing13460 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14236054688114933760
theorem maskCheck13460 :
    checkMaskFor missing13460 StrongPackedBucketN12A4Shard105.record13460 = true := by
  decide

def missing13461 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14344141079171825664
theorem maskCheck13461 :
    checkMaskFor missing13461 StrongPackedBucketN12A4Shard105.record13461 = true := by
  decide

def missing13462 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14776486643399393280
theorem maskCheck13462 :
    checkMaskFor missing13462 StrongPackedBucketN12A4Shard105.record13462 = true := by
  decide

def missing13463 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18991855894618177536
theorem maskCheck13463 :
    checkMaskFor missing13463 StrongPackedBucketN12A4Shard105.record13463 = true := by
  decide

def missing13464 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19424201458845745152
theorem maskCheck13464 :
    checkMaskFor missing13464 StrongPackedBucketN12A4Shard105.record13464 = true := by
  decide

def missing13465 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19496259052883673088
theorem maskCheck13465 :
    checkMaskFor missing13465 StrongPackedBucketN12A4Shard105.record13465 = true := by
  decide

def missing13466 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19532287849902637056
theorem maskCheck13466 :
    checkMaskFor missing13466 StrongPackedBucketN12A4Shard105.record13466 = true := by
  decide

def missing13467 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20505065369414664192
theorem maskCheck13467 :
    checkMaskFor missing13467 StrongPackedBucketN12A4Shard105.record13467 = true := by
  decide

def missing13468 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20613151760471556096
theorem maskCheck13468 :
    checkMaskFor missing13468 StrongPackedBucketN12A4Shard105.record13468 = true := by
  decide

def missing13469 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23315311536893853696
theorem maskCheck13469 :
    checkMaskFor missing13469 StrongPackedBucketN12A4Shard105.record13469 = true := by
  decide

def missing13470 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23459426724969709568
theorem maskCheck13470 :
    checkMaskFor missing13470 StrongPackedBucketN12A4Shard105.record13470 = true := by
  decide

def missing13471 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23531484319007637504
theorem maskCheck13471 :
    checkMaskFor missing13471 StrongPackedBucketN12A4Shard105.record13471 = true := by
  decide

def missing13472 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23567513116026601472
theorem maskCheck13472 :
    checkMaskFor missing13472 StrongPackedBucketN12A4Shard105.record13472 = true := by
  decide

def missing13473 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23963829883235205120
theorem maskCheck13473 :
    checkMaskFor missing13473 StrongPackedBucketN12A4Shard105.record13473 = true := by
  decide

def missing13474 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24071916274292097024
theorem maskCheck13474 :
    checkMaskFor missing13474 StrongPackedBucketN12A4Shard105.record13474 = true := by
  decide

def missing13475 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27926997555321241600
theorem maskCheck13475 :
    checkMaskFor missing13475 StrongPackedBucketN12A4Shard105.record13475 = true := by
  decide

def missing13476 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28071112743397097472
theorem maskCheck13476 :
    checkMaskFor missing13476 StrongPackedBucketN12A4Shard105.record13476 = true := by
  decide

def missing13477 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28179199134453989376
theorem maskCheck13477 :
    checkMaskFor missing13477 StrongPackedBucketN12A4Shard105.record13477 = true := by
  decide

def missing13478 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32394568385672773632
theorem maskCheck13478 :
    checkMaskFor missing13478 StrongPackedBucketN12A4Shard105.record13478 = true := by
  decide

def missing13479 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32502654776729665536
theorem maskCheck13479 :
    checkMaskFor missing13479 StrongPackedBucketN12A4Shard105.record13479 = true := by
  decide

def missing13480 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37438599968327729152
theorem maskCheck13480 :
    checkMaskFor missing13480 StrongPackedBucketN12A4Shard105.record13480 = true := by
  decide

def missing13481 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37870945532555296768
theorem maskCheck13481 :
    checkMaskFor missing13481 StrongPackedBucketN12A4Shard105.record13481 = true := by
  decide

def missing13482 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37943003126593224704
theorem maskCheck13482 :
    checkMaskFor missing13482 StrongPackedBucketN12A4Shard105.record13482 = true := by
  decide

def missing13483 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38951809443124215808
theorem maskCheck13483 :
    checkMaskFor missing13483 StrongPackedBucketN12A4Shard105.record13483 = true := by
  decide

def missing13484 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41762055610603405312
theorem maskCheck13484 :
    checkMaskFor missing13484 StrongPackedBucketN12A4Shard105.record13484 = true := by
  decide

def missing13485 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41906170798679261184
theorem maskCheck13485 :
    checkMaskFor missing13485 StrongPackedBucketN12A4Shard105.record13485 = true := by
  decide

def missing13486 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41978228392717189120
theorem maskCheck13486 :
    checkMaskFor missing13486 StrongPackedBucketN12A4Shard105.record13486 = true := by
  decide

def missing13487 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42410573956944756736
theorem maskCheck13487 :
    checkMaskFor missing13487 StrongPackedBucketN12A4Shard105.record13487 = true := by
  decide

def missing13488 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46373741629030793216
theorem maskCheck13488 :
    checkMaskFor missing13488 StrongPackedBucketN12A4Shard105.record13488 = true := by
  decide

def missing13489 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46517856817106649088
theorem maskCheck13489 :
    checkMaskFor missing13489 StrongPackedBucketN12A4Shard105.record13489 = true := by
  decide

def missing13490 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50841312459382325248
theorem maskCheck13490 :
    checkMaskFor missing13490 StrongPackedBucketN12A4Shard105.record13490 = true := by
  decide

def missing13491 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55597113665885569024
theorem maskCheck13491 :
    checkMaskFor missing13491 StrongPackedBucketN12A4Shard105.record13491 = true := by
  decide

def missing13492 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55813286447999352832
theorem maskCheck13492 :
    checkMaskFor missing13492 StrongPackedBucketN12A4Shard105.record13492 = true := by
  decide

def missing13493 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60136742090275028992
theorem maskCheck13493 :
    checkMaskFor missing13493 StrongPackedBucketN12A4Shard105.record13493 = true := by
  decide

def missing13494 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1121607757584138240
theorem maskCheck13494 :
    checkMaskFor missing13494 StrongPackedBucketN12A4Shard105.record13494 = true := by
  decide

def missing13495 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2130414074115129344
theorem maskCheck13495 :
    checkMaskFor missing13495 StrongPackedBucketN12A4Shard105.record13495 = true := by
  decide

def missing13496 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2202471668153057280
theorem maskCheck13496 :
    checkMaskFor missing13496 StrongPackedBucketN12A4Shard105.record13496 = true := by
  decide

def missing13497 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2238500465172021248
theorem maskCheck13497 :
    checkMaskFor missing13497 StrongPackedBucketN12A4Shard105.record13497 = true := by
  decide

def missing13498 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4364199489290895360
theorem maskCheck13498 :
    checkMaskFor missing13498 StrongPackedBucketN12A4Shard105.record13498 = true := by
  decide

def missing13499 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4400228286309859328
theorem maskCheck13499 :
    checkMaskFor missing13499 StrongPackedBucketN12A4Shard105.record13499 = true := by
  decide

def missing13500 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4472285880347787264
theorem maskCheck13500 :
    checkMaskFor missing13500 StrongPackedBucketN12A4Shard105.record13500 = true := by
  decide

def missing13501 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5156833023708102656
theorem maskCheck13501 :
    checkMaskFor missing13501 StrongPackedBucketN12A4Shard105.record13501 = true := by
  decide

def missing13502 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5589178587935670272
theorem maskCheck13502 :
    checkMaskFor missing13502 StrongPackedBucketN12A4Shard105.record13502 = true := by
  decide

def missing13503 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5661236181973598208
theorem maskCheck13503 :
    checkMaskFor missing13503 StrongPackedBucketN12A4Shard105.record13503 = true := by
  decide

def missing13504 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5697264978992562176
theorem maskCheck13504 :
    checkMaskFor missing13504 StrongPackedBucketN12A4Shard105.record13504 = true := by
  decide

def missing13505 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6670042498504589312
theorem maskCheck13505 :
    checkMaskFor missing13505 StrongPackedBucketN12A4Shard105.record13505 = true := by
  decide

def missing13506 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6778128889561481216
theorem maskCheck13506 :
    checkMaskFor missing13506 StrongPackedBucketN12A4Shard105.record13506 = true := by
  decide

def missing13507 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9768519042135490560
theorem maskCheck13507 :
    checkMaskFor missing13507 StrongPackedBucketN12A4Shard105.record13507 = true := by
  decide

def missing13508 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10200864606363058176
theorem maskCheck13508 :
    checkMaskFor missing13508 StrongPackedBucketN12A4Shard105.record13508 = true := by
  decide

def missing13509 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10272922200400986112
theorem maskCheck13509 :
    checkMaskFor missing13509 StrongPackedBucketN12A4Shard105.record13509 = true := by
  decide

def missing13510 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10308950997419950080
theorem maskCheck13510 :
    checkMaskFor missing13510 StrongPackedBucketN12A4Shard105.record13510 = true := by
  decide

def missing13511 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11281728516931977216
theorem maskCheck13511 :
    checkMaskFor missing13511 StrongPackedBucketN12A4Shard105.record13511 = true := by
  decide

def missing13512 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11317757313950941184
theorem maskCheck13512 :
    checkMaskFor missing13512 StrongPackedBucketN12A4Shard105.record13512 = true := by
  decide

def missing13513 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11389814907988869120
theorem maskCheck13513 :
    checkMaskFor missing13513 StrongPackedBucketN12A4Shard105.record13513 = true := by
  decide

def missing13514 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13551542729126707200
theorem maskCheck13514 :
    checkMaskFor missing13514 StrongPackedBucketN12A4Shard105.record13514 = true := by
  decide

def missing13515 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14091974684411166720
theorem maskCheck13515 :
    checkMaskFor missing13515 StrongPackedBucketN12A4Shard105.record13515 = true := by
  decide

def missing13516 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14236089872487022592
theorem maskCheck13516 :
    checkMaskFor missing13516 StrongPackedBucketN12A4Shard105.record13516 = true := by
  decide

def missing13517 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14308147466524950528
theorem maskCheck13517 :
    checkMaskFor missing13517 StrongPackedBucketN12A4Shard105.record13517 = true := by
  decide

def missing13518 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14344176263543914496
theorem maskCheck13518 :
    checkMaskFor missing13518 StrongPackedBucketN12A4Shard105.record13518 = true := by
  decide

def missing13519 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14740493030752518144
theorem maskCheck13519 :
    checkMaskFor missing13519 StrongPackedBucketN12A4Shard105.record13519 = true := by
  decide

def missing13520 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14848579421809410048
theorem maskCheck13520 :
    checkMaskFor missing13520 StrongPackedBucketN12A4Shard105.record13520 = true := by
  decide

def missing13521 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18991891078990266368
theorem maskCheck13521 :
    checkMaskFor missing13521 StrongPackedBucketN12A4Shard105.record13521 = true := by
  decide

def missing13522 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19424236643217833984
theorem maskCheck13522 :
    checkMaskFor missing13522 StrongPackedBucketN12A4Shard105.record13522 = true := by
  decide

def missing13523 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19496294237255761920
theorem maskCheck13523 :
    checkMaskFor missing13523 StrongPackedBucketN12A4Shard105.record13523 = true := by
  decide

def missing13524 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20505100553786753024
theorem maskCheck13524 :
    checkMaskFor missing13524 StrongPackedBucketN12A4Shard105.record13524 = true := by
  decide

def missing13525 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23315346721265942528
theorem maskCheck13525 :
    checkMaskFor missing13525 StrongPackedBucketN12A4Shard105.record13525 = true := by
  decide

def missing13526 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23531519503379726336
theorem maskCheck13526 :
    checkMaskFor missing13526 StrongPackedBucketN12A4Shard105.record13526 = true := by
  decide

def missing13527 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27927032739693330432
theorem maskCheck13527 :
    checkMaskFor missing13527 StrongPackedBucketN12A4Shard105.record13527 = true := by
  decide

def missing13528 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28071147927769186304
theorem maskCheck13528 :
    checkMaskFor missing13528 StrongPackedBucketN12A4Shard105.record13528 = true := by
  decide

def missing13529 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28143205521807114240
theorem maskCheck13529 :
    checkMaskFor missing13529 StrongPackedBucketN12A4Shard105.record13529 = true := by
  decide

def missing13530 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28575551086034681856
theorem maskCheck13530 :
    checkMaskFor missing13530 StrongPackedBucketN12A4Shard105.record13530 = true := by
  decide

def missing13531 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32466661164082790400
theorem maskCheck13531 :
    checkMaskFor missing13531 StrongPackedBucketN12A4Shard105.record13531 = true := by
  decide

def missing13532 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37438635152699817984
theorem maskCheck13532 :
    checkMaskFor missing13532 StrongPackedBucketN12A4Shard105.record13532 = true := by
  decide

def missing13533 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37870980716927385600
theorem maskCheck13533 :
    checkMaskFor missing13533 StrongPackedBucketN12A4Shard105.record13533 = true := by
  decide

def missing13534 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37943038310965313536
theorem maskCheck13534 :
    checkMaskFor missing13534 StrongPackedBucketN12A4Shard105.record13534 = true := by
  decide

def missing13535 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37979067107984277504
theorem maskCheck13535 :
    checkMaskFor missing13535 StrongPackedBucketN12A4Shard105.record13535 = true := by
  decide

def missing13536 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38951844627496304640
theorem maskCheck13536 :
    checkMaskFor missing13536 StrongPackedBucketN12A4Shard105.record13536 = true := by
  decide

def missing13537 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38987873424515268608
theorem maskCheck13537 :
    checkMaskFor missing13537 StrongPackedBucketN12A4Shard105.record13537 = true := by
  decide

def missing13538 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39059931018553196544
theorem maskCheck13538 :
    checkMaskFor missing13538 StrongPackedBucketN12A4Shard105.record13538 = true := by
  decide

def missing13539 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41221658839691034624
theorem maskCheck13539 :
    checkMaskFor missing13539 StrongPackedBucketN12A4Shard105.record13539 = true := by
  decide

def missing13540 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41762090794975494144
theorem maskCheck13540 :
    checkMaskFor missing13540 StrongPackedBucketN12A4Shard105.record13540 = true := by
  decide

def missing13541 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41906205983051350016
theorem maskCheck13541 :
    checkMaskFor missing13541 StrongPackedBucketN12A4Shard105.record13541 = true := by
  decide

def missing13542 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41978263577089277952
theorem maskCheck13542 :
    checkMaskFor missing13542 StrongPackedBucketN12A4Shard105.record13542 = true := by
  decide

def missing13543 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42014292374108241920
theorem maskCheck13543 :
    checkMaskFor missing13543 StrongPackedBucketN12A4Shard105.record13543 = true := by
  decide

def missing13544 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42410609141316845568
theorem maskCheck13544 :
    checkMaskFor missing13544 StrongPackedBucketN12A4Shard105.record13544 = true := by
  decide

def missing13545 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42518695532373737472
theorem maskCheck13545 :
    checkMaskFor missing13545 StrongPackedBucketN12A4Shard105.record13545 = true := by
  decide

def missing13546 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46373776813402882048
theorem maskCheck13546 :
    checkMaskFor missing13546 StrongPackedBucketN12A4Shard105.record13546 = true := by
  decide

def missing13547 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46517892001478737920
theorem maskCheck13547 :
    checkMaskFor missing13547 StrongPackedBucketN12A4Shard105.record13547 = true := by
  decide

def missing13548 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46589949595516665856
theorem maskCheck13548 :
    checkMaskFor missing13548 StrongPackedBucketN12A4Shard105.record13548 = true := by
  decide

def missing13549 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46625978392535629824
theorem maskCheck13549 :
    checkMaskFor missing13549 StrongPackedBucketN12A4Shard105.record13549 = true := by
  decide

def missing13550 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47022295159744233472
theorem maskCheck13550 :
    checkMaskFor missing13550 StrongPackedBucketN12A4Shard105.record13550 = true := by
  decide

def missing13551 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47058323956763197440
theorem maskCheck13551 :
    checkMaskFor missing13551 StrongPackedBucketN12A4Shard105.record13551 = true := by
  decide

def missing13552 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47130381550801125376
theorem maskCheck13552 :
    checkMaskFor missing13552 StrongPackedBucketN12A4Shard105.record13552 = true := by
  decide

def missing13553 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48139187867332116480
theorem maskCheck13553 :
    checkMaskFor missing13553 StrongPackedBucketN12A4Shard105.record13553 = true := by
  decide

def missing13554 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50841347643754414080
theorem maskCheck13554 :
    checkMaskFor missing13554 StrongPackedBucketN12A4Shard105.record13554 = true := by
  decide

def missing13555 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50913405237792342016
theorem maskCheck13555 :
    checkMaskFor missing13555 StrongPackedBucketN12A4Shard105.record13555 = true := by
  decide

def missing13556 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50949434034811305984
theorem maskCheck13556 :
    checkMaskFor missing13556 StrongPackedBucketN12A4Shard105.record13556 = true := by
  decide

def missing13557 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51057520425868197888
theorem maskCheck13557 :
    checkMaskFor missing13557 StrongPackedBucketN12A4Shard105.record13557 = true := by
  decide

def missing13558 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51165606816925089792
theorem maskCheck13558 :
    checkMaskFor missing13558 StrongPackedBucketN12A4Shard105.record13558 = true := by
  decide

def missing13559 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55597148850257657856
theorem maskCheck13559 :
    checkMaskFor missing13559 StrongPackedBucketN12A4Shard105.record13559 = true := by
  decide

def missing13560 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55741264038333513728
theorem maskCheck13560 :
    checkMaskFor missing13560 StrongPackedBucketN12A4Shard105.record13560 = true := by
  decide

def missing13561 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55813321632371441664
theorem maskCheck13561 :
    checkMaskFor missing13561 StrongPackedBucketN12A4Shard105.record13561 = true := by
  decide

def missing13562 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56245667196599009280
theorem maskCheck13562 :
    checkMaskFor missing13562 StrongPackedBucketN12A4Shard105.record13562 = true := by
  decide

def missing13563 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60136777274647117824
theorem maskCheck13563 :
    checkMaskFor missing13563 StrongPackedBucketN12A4Shard105.record13563 = true := by
  decide

def missing13564 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64676405699036577792
theorem maskCheck13564 :
    checkMaskFor missing13564 StrongPackedBucketN12A4Shard105.record13564 = true := by
  decide

def missing13565 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64748463293074505728
theorem maskCheck13565 :
    checkMaskFor missing13565 StrongPackedBucketN12A4Shard105.record13565 = true := by
  decide

def missing13566 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64892578481150361600
theorem maskCheck13566 :
    checkMaskFor missing13566 StrongPackedBucketN12A4Shard105.record13566 = true := by
  decide

def missing13567 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1121818863816671232
theorem maskCheck13567 :
    checkMaskFor missing13567 StrongPackedBucketN12A4Shard105.record13567 = true := by
  decide

def missing13440_13441 : List (BitVec (edgeCount 12)) :=
  [missing13440]
abbrev records13440_13441 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13440]
theorem aligned13440_13441 :
    AlignedValid 12 4 missing13440_13441 records13440_13441 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13440
    maskCheck13440 AlignedValid.nil

def missing13441_13442 : List (BitVec (edgeCount 12)) :=
  [missing13441]
abbrev records13441_13442 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13441]
theorem aligned13441_13442 :
    AlignedValid 12 4 missing13441_13442 records13441_13442 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13441
    maskCheck13441 AlignedValid.nil

def missing13440_13442 : List (BitVec (edgeCount 12)) :=
  missing13440_13441 ++ missing13441_13442
abbrev records13440_13442 : List Blob :=
  records13440_13441 ++ records13441_13442
theorem aligned13440_13442 :
    AlignedValid 12 4 missing13440_13442 records13440_13442 :=
  aligned13440_13441.append aligned13441_13442

def missing13442_13443 : List (BitVec (edgeCount 12)) :=
  [missing13442]
abbrev records13442_13443 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13442]
theorem aligned13442_13443 :
    AlignedValid 12 4 missing13442_13443 records13442_13443 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13442
    maskCheck13442 AlignedValid.nil

def missing13443_13444 : List (BitVec (edgeCount 12)) :=
  [missing13443]
abbrev records13443_13444 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13443]
theorem aligned13443_13444 :
    AlignedValid 12 4 missing13443_13444 records13443_13444 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13443
    maskCheck13443 AlignedValid.nil

def missing13442_13444 : List (BitVec (edgeCount 12)) :=
  missing13442_13443 ++ missing13443_13444
abbrev records13442_13444 : List Blob :=
  records13442_13443 ++ records13443_13444
theorem aligned13442_13444 :
    AlignedValid 12 4 missing13442_13444 records13442_13444 :=
  aligned13442_13443.append aligned13443_13444

def missing13440_13444 : List (BitVec (edgeCount 12)) :=
  missing13440_13442 ++ missing13442_13444
abbrev records13440_13444 : List Blob :=
  records13440_13442 ++ records13442_13444
theorem aligned13440_13444 :
    AlignedValid 12 4 missing13440_13444 records13440_13444 :=
  aligned13440_13442.append aligned13442_13444

def missing13444_13445 : List (BitVec (edgeCount 12)) :=
  [missing13444]
abbrev records13444_13445 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13444]
theorem aligned13444_13445 :
    AlignedValid 12 4 missing13444_13445 records13444_13445 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13444
    maskCheck13444 AlignedValid.nil

def missing13445_13446 : List (BitVec (edgeCount 12)) :=
  [missing13445]
abbrev records13445_13446 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13445]
theorem aligned13445_13446 :
    AlignedValid 12 4 missing13445_13446 records13445_13446 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13445
    maskCheck13445 AlignedValid.nil

def missing13444_13446 : List (BitVec (edgeCount 12)) :=
  missing13444_13445 ++ missing13445_13446
abbrev records13444_13446 : List Blob :=
  records13444_13445 ++ records13445_13446
theorem aligned13444_13446 :
    AlignedValid 12 4 missing13444_13446 records13444_13446 :=
  aligned13444_13445.append aligned13445_13446

def missing13446_13447 : List (BitVec (edgeCount 12)) :=
  [missing13446]
abbrev records13446_13447 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13446]
theorem aligned13446_13447 :
    AlignedValid 12 4 missing13446_13447 records13446_13447 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13446
    maskCheck13446 AlignedValid.nil

def missing13447_13448 : List (BitVec (edgeCount 12)) :=
  [missing13447]
abbrev records13447_13448 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13447]
theorem aligned13447_13448 :
    AlignedValid 12 4 missing13447_13448 records13447_13448 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13447
    maskCheck13447 AlignedValid.nil

def missing13446_13448 : List (BitVec (edgeCount 12)) :=
  missing13446_13447 ++ missing13447_13448
abbrev records13446_13448 : List Blob :=
  records13446_13447 ++ records13447_13448
theorem aligned13446_13448 :
    AlignedValid 12 4 missing13446_13448 records13446_13448 :=
  aligned13446_13447.append aligned13447_13448

def missing13444_13448 : List (BitVec (edgeCount 12)) :=
  missing13444_13446 ++ missing13446_13448
abbrev records13444_13448 : List Blob :=
  records13444_13446 ++ records13446_13448
theorem aligned13444_13448 :
    AlignedValid 12 4 missing13444_13448 records13444_13448 :=
  aligned13444_13446.append aligned13446_13448

def missing13440_13448 : List (BitVec (edgeCount 12)) :=
  missing13440_13444 ++ missing13444_13448
abbrev records13440_13448 : List Blob :=
  records13440_13444 ++ records13444_13448
theorem aligned13440_13448 :
    AlignedValid 12 4 missing13440_13448 records13440_13448 :=
  aligned13440_13444.append aligned13444_13448

def missing13448_13449 : List (BitVec (edgeCount 12)) :=
  [missing13448]
abbrev records13448_13449 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13448]
theorem aligned13448_13449 :
    AlignedValid 12 4 missing13448_13449 records13448_13449 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13448
    maskCheck13448 AlignedValid.nil

def missing13449_13450 : List (BitVec (edgeCount 12)) :=
  [missing13449]
abbrev records13449_13450 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13449]
theorem aligned13449_13450 :
    AlignedValid 12 4 missing13449_13450 records13449_13450 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13449
    maskCheck13449 AlignedValid.nil

def missing13448_13450 : List (BitVec (edgeCount 12)) :=
  missing13448_13449 ++ missing13449_13450
abbrev records13448_13450 : List Blob :=
  records13448_13449 ++ records13449_13450
theorem aligned13448_13450 :
    AlignedValid 12 4 missing13448_13450 records13448_13450 :=
  aligned13448_13449.append aligned13449_13450

def missing13450_13451 : List (BitVec (edgeCount 12)) :=
  [missing13450]
abbrev records13450_13451 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13450]
theorem aligned13450_13451 :
    AlignedValid 12 4 missing13450_13451 records13450_13451 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13450
    maskCheck13450 AlignedValid.nil

def missing13451_13452 : List (BitVec (edgeCount 12)) :=
  [missing13451]
abbrev records13451_13452 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13451]
theorem aligned13451_13452 :
    AlignedValid 12 4 missing13451_13452 records13451_13452 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13451
    maskCheck13451 AlignedValid.nil

def missing13450_13452 : List (BitVec (edgeCount 12)) :=
  missing13450_13451 ++ missing13451_13452
abbrev records13450_13452 : List Blob :=
  records13450_13451 ++ records13451_13452
theorem aligned13450_13452 :
    AlignedValid 12 4 missing13450_13452 records13450_13452 :=
  aligned13450_13451.append aligned13451_13452

def missing13448_13452 : List (BitVec (edgeCount 12)) :=
  missing13448_13450 ++ missing13450_13452
abbrev records13448_13452 : List Blob :=
  records13448_13450 ++ records13450_13452
theorem aligned13448_13452 :
    AlignedValid 12 4 missing13448_13452 records13448_13452 :=
  aligned13448_13450.append aligned13450_13452

def missing13452_13453 : List (BitVec (edgeCount 12)) :=
  [missing13452]
abbrev records13452_13453 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13452]
theorem aligned13452_13453 :
    AlignedValid 12 4 missing13452_13453 records13452_13453 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13452
    maskCheck13452 AlignedValid.nil

def missing13453_13454 : List (BitVec (edgeCount 12)) :=
  [missing13453]
abbrev records13453_13454 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13453]
theorem aligned13453_13454 :
    AlignedValid 12 4 missing13453_13454 records13453_13454 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13453
    maskCheck13453 AlignedValid.nil

def missing13452_13454 : List (BitVec (edgeCount 12)) :=
  missing13452_13453 ++ missing13453_13454
abbrev records13452_13454 : List Blob :=
  records13452_13453 ++ records13453_13454
theorem aligned13452_13454 :
    AlignedValid 12 4 missing13452_13454 records13452_13454 :=
  aligned13452_13453.append aligned13453_13454

def missing13454_13455 : List (BitVec (edgeCount 12)) :=
  [missing13454]
abbrev records13454_13455 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13454]
theorem aligned13454_13455 :
    AlignedValid 12 4 missing13454_13455 records13454_13455 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13454
    maskCheck13454 AlignedValid.nil

def missing13455_13456 : List (BitVec (edgeCount 12)) :=
  [missing13455]
abbrev records13455_13456 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13455]
theorem aligned13455_13456 :
    AlignedValid 12 4 missing13455_13456 records13455_13456 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13455
    maskCheck13455 AlignedValid.nil

def missing13454_13456 : List (BitVec (edgeCount 12)) :=
  missing13454_13455 ++ missing13455_13456
abbrev records13454_13456 : List Blob :=
  records13454_13455 ++ records13455_13456
theorem aligned13454_13456 :
    AlignedValid 12 4 missing13454_13456 records13454_13456 :=
  aligned13454_13455.append aligned13455_13456

def missing13452_13456 : List (BitVec (edgeCount 12)) :=
  missing13452_13454 ++ missing13454_13456
abbrev records13452_13456 : List Blob :=
  records13452_13454 ++ records13454_13456
theorem aligned13452_13456 :
    AlignedValid 12 4 missing13452_13456 records13452_13456 :=
  aligned13452_13454.append aligned13454_13456

def missing13448_13456 : List (BitVec (edgeCount 12)) :=
  missing13448_13452 ++ missing13452_13456
abbrev records13448_13456 : List Blob :=
  records13448_13452 ++ records13452_13456
theorem aligned13448_13456 :
    AlignedValid 12 4 missing13448_13456 records13448_13456 :=
  aligned13448_13452.append aligned13452_13456

def missing13440_13456 : List (BitVec (edgeCount 12)) :=
  missing13440_13448 ++ missing13448_13456
abbrev records13440_13456 : List Blob :=
  records13440_13448 ++ records13448_13456
theorem aligned13440_13456 :
    AlignedValid 12 4 missing13440_13456 records13440_13456 :=
  aligned13440_13448.append aligned13448_13456

def missing13456_13457 : List (BitVec (edgeCount 12)) :=
  [missing13456]
abbrev records13456_13457 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13456]
theorem aligned13456_13457 :
    AlignedValid 12 4 missing13456_13457 records13456_13457 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13456
    maskCheck13456 AlignedValid.nil

def missing13457_13458 : List (BitVec (edgeCount 12)) :=
  [missing13457]
abbrev records13457_13458 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13457]
theorem aligned13457_13458 :
    AlignedValid 12 4 missing13457_13458 records13457_13458 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13457
    maskCheck13457 AlignedValid.nil

def missing13456_13458 : List (BitVec (edgeCount 12)) :=
  missing13456_13457 ++ missing13457_13458
abbrev records13456_13458 : List Blob :=
  records13456_13457 ++ records13457_13458
theorem aligned13456_13458 :
    AlignedValid 12 4 missing13456_13458 records13456_13458 :=
  aligned13456_13457.append aligned13457_13458

def missing13458_13459 : List (BitVec (edgeCount 12)) :=
  [missing13458]
abbrev records13458_13459 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13458]
theorem aligned13458_13459 :
    AlignedValid 12 4 missing13458_13459 records13458_13459 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13458
    maskCheck13458 AlignedValid.nil

def missing13459_13460 : List (BitVec (edgeCount 12)) :=
  [missing13459]
abbrev records13459_13460 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13459]
theorem aligned13459_13460 :
    AlignedValid 12 4 missing13459_13460 records13459_13460 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13459
    maskCheck13459 AlignedValid.nil

def missing13458_13460 : List (BitVec (edgeCount 12)) :=
  missing13458_13459 ++ missing13459_13460
abbrev records13458_13460 : List Blob :=
  records13458_13459 ++ records13459_13460
theorem aligned13458_13460 :
    AlignedValid 12 4 missing13458_13460 records13458_13460 :=
  aligned13458_13459.append aligned13459_13460

def missing13456_13460 : List (BitVec (edgeCount 12)) :=
  missing13456_13458 ++ missing13458_13460
abbrev records13456_13460 : List Blob :=
  records13456_13458 ++ records13458_13460
theorem aligned13456_13460 :
    AlignedValid 12 4 missing13456_13460 records13456_13460 :=
  aligned13456_13458.append aligned13458_13460

def missing13460_13461 : List (BitVec (edgeCount 12)) :=
  [missing13460]
abbrev records13460_13461 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13460]
theorem aligned13460_13461 :
    AlignedValid 12 4 missing13460_13461 records13460_13461 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13460
    maskCheck13460 AlignedValid.nil

def missing13461_13462 : List (BitVec (edgeCount 12)) :=
  [missing13461]
abbrev records13461_13462 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13461]
theorem aligned13461_13462 :
    AlignedValid 12 4 missing13461_13462 records13461_13462 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13461
    maskCheck13461 AlignedValid.nil

def missing13460_13462 : List (BitVec (edgeCount 12)) :=
  missing13460_13461 ++ missing13461_13462
abbrev records13460_13462 : List Blob :=
  records13460_13461 ++ records13461_13462
theorem aligned13460_13462 :
    AlignedValid 12 4 missing13460_13462 records13460_13462 :=
  aligned13460_13461.append aligned13461_13462

def missing13462_13463 : List (BitVec (edgeCount 12)) :=
  [missing13462]
abbrev records13462_13463 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13462]
theorem aligned13462_13463 :
    AlignedValid 12 4 missing13462_13463 records13462_13463 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13462
    maskCheck13462 AlignedValid.nil

def missing13463_13464 : List (BitVec (edgeCount 12)) :=
  [missing13463]
abbrev records13463_13464 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13463]
theorem aligned13463_13464 :
    AlignedValid 12 4 missing13463_13464 records13463_13464 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13463
    maskCheck13463 AlignedValid.nil

def missing13462_13464 : List (BitVec (edgeCount 12)) :=
  missing13462_13463 ++ missing13463_13464
abbrev records13462_13464 : List Blob :=
  records13462_13463 ++ records13463_13464
theorem aligned13462_13464 :
    AlignedValid 12 4 missing13462_13464 records13462_13464 :=
  aligned13462_13463.append aligned13463_13464

def missing13460_13464 : List (BitVec (edgeCount 12)) :=
  missing13460_13462 ++ missing13462_13464
abbrev records13460_13464 : List Blob :=
  records13460_13462 ++ records13462_13464
theorem aligned13460_13464 :
    AlignedValid 12 4 missing13460_13464 records13460_13464 :=
  aligned13460_13462.append aligned13462_13464

def missing13456_13464 : List (BitVec (edgeCount 12)) :=
  missing13456_13460 ++ missing13460_13464
abbrev records13456_13464 : List Blob :=
  records13456_13460 ++ records13460_13464
theorem aligned13456_13464 :
    AlignedValid 12 4 missing13456_13464 records13456_13464 :=
  aligned13456_13460.append aligned13460_13464

def missing13464_13465 : List (BitVec (edgeCount 12)) :=
  [missing13464]
abbrev records13464_13465 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13464]
theorem aligned13464_13465 :
    AlignedValid 12 4 missing13464_13465 records13464_13465 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13464
    maskCheck13464 AlignedValid.nil

def missing13465_13466 : List (BitVec (edgeCount 12)) :=
  [missing13465]
abbrev records13465_13466 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13465]
theorem aligned13465_13466 :
    AlignedValid 12 4 missing13465_13466 records13465_13466 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13465
    maskCheck13465 AlignedValid.nil

def missing13464_13466 : List (BitVec (edgeCount 12)) :=
  missing13464_13465 ++ missing13465_13466
abbrev records13464_13466 : List Blob :=
  records13464_13465 ++ records13465_13466
theorem aligned13464_13466 :
    AlignedValid 12 4 missing13464_13466 records13464_13466 :=
  aligned13464_13465.append aligned13465_13466

def missing13466_13467 : List (BitVec (edgeCount 12)) :=
  [missing13466]
abbrev records13466_13467 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13466]
theorem aligned13466_13467 :
    AlignedValid 12 4 missing13466_13467 records13466_13467 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13466
    maskCheck13466 AlignedValid.nil

def missing13467_13468 : List (BitVec (edgeCount 12)) :=
  [missing13467]
abbrev records13467_13468 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13467]
theorem aligned13467_13468 :
    AlignedValid 12 4 missing13467_13468 records13467_13468 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13467
    maskCheck13467 AlignedValid.nil

def missing13466_13468 : List (BitVec (edgeCount 12)) :=
  missing13466_13467 ++ missing13467_13468
abbrev records13466_13468 : List Blob :=
  records13466_13467 ++ records13467_13468
theorem aligned13466_13468 :
    AlignedValid 12 4 missing13466_13468 records13466_13468 :=
  aligned13466_13467.append aligned13467_13468

def missing13464_13468 : List (BitVec (edgeCount 12)) :=
  missing13464_13466 ++ missing13466_13468
abbrev records13464_13468 : List Blob :=
  records13464_13466 ++ records13466_13468
theorem aligned13464_13468 :
    AlignedValid 12 4 missing13464_13468 records13464_13468 :=
  aligned13464_13466.append aligned13466_13468

def missing13468_13469 : List (BitVec (edgeCount 12)) :=
  [missing13468]
abbrev records13468_13469 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13468]
theorem aligned13468_13469 :
    AlignedValid 12 4 missing13468_13469 records13468_13469 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13468
    maskCheck13468 AlignedValid.nil

def missing13469_13470 : List (BitVec (edgeCount 12)) :=
  [missing13469]
abbrev records13469_13470 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13469]
theorem aligned13469_13470 :
    AlignedValid 12 4 missing13469_13470 records13469_13470 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13469
    maskCheck13469 AlignedValid.nil

def missing13468_13470 : List (BitVec (edgeCount 12)) :=
  missing13468_13469 ++ missing13469_13470
abbrev records13468_13470 : List Blob :=
  records13468_13469 ++ records13469_13470
theorem aligned13468_13470 :
    AlignedValid 12 4 missing13468_13470 records13468_13470 :=
  aligned13468_13469.append aligned13469_13470

def missing13470_13471 : List (BitVec (edgeCount 12)) :=
  [missing13470]
abbrev records13470_13471 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13470]
theorem aligned13470_13471 :
    AlignedValid 12 4 missing13470_13471 records13470_13471 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13470
    maskCheck13470 AlignedValid.nil

def missing13471_13472 : List (BitVec (edgeCount 12)) :=
  [missing13471]
abbrev records13471_13472 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13471]
theorem aligned13471_13472 :
    AlignedValid 12 4 missing13471_13472 records13471_13472 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13471
    maskCheck13471 AlignedValid.nil

def missing13470_13472 : List (BitVec (edgeCount 12)) :=
  missing13470_13471 ++ missing13471_13472
abbrev records13470_13472 : List Blob :=
  records13470_13471 ++ records13471_13472
theorem aligned13470_13472 :
    AlignedValid 12 4 missing13470_13472 records13470_13472 :=
  aligned13470_13471.append aligned13471_13472

def missing13468_13472 : List (BitVec (edgeCount 12)) :=
  missing13468_13470 ++ missing13470_13472
abbrev records13468_13472 : List Blob :=
  records13468_13470 ++ records13470_13472
theorem aligned13468_13472 :
    AlignedValid 12 4 missing13468_13472 records13468_13472 :=
  aligned13468_13470.append aligned13470_13472

def missing13464_13472 : List (BitVec (edgeCount 12)) :=
  missing13464_13468 ++ missing13468_13472
abbrev records13464_13472 : List Blob :=
  records13464_13468 ++ records13468_13472
theorem aligned13464_13472 :
    AlignedValid 12 4 missing13464_13472 records13464_13472 :=
  aligned13464_13468.append aligned13468_13472

def missing13456_13472 : List (BitVec (edgeCount 12)) :=
  missing13456_13464 ++ missing13464_13472
abbrev records13456_13472 : List Blob :=
  records13456_13464 ++ records13464_13472
theorem aligned13456_13472 :
    AlignedValid 12 4 missing13456_13472 records13456_13472 :=
  aligned13456_13464.append aligned13464_13472

def missing13440_13472 : List (BitVec (edgeCount 12)) :=
  missing13440_13456 ++ missing13456_13472
abbrev records13440_13472 : List Blob :=
  records13440_13456 ++ records13456_13472
theorem aligned13440_13472 :
    AlignedValid 12 4 missing13440_13472 records13440_13472 :=
  aligned13440_13456.append aligned13456_13472

def missing13472_13473 : List (BitVec (edgeCount 12)) :=
  [missing13472]
abbrev records13472_13473 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13472]
theorem aligned13472_13473 :
    AlignedValid 12 4 missing13472_13473 records13472_13473 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13472
    maskCheck13472 AlignedValid.nil

def missing13473_13474 : List (BitVec (edgeCount 12)) :=
  [missing13473]
abbrev records13473_13474 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13473]
theorem aligned13473_13474 :
    AlignedValid 12 4 missing13473_13474 records13473_13474 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13473
    maskCheck13473 AlignedValid.nil

def missing13472_13474 : List (BitVec (edgeCount 12)) :=
  missing13472_13473 ++ missing13473_13474
abbrev records13472_13474 : List Blob :=
  records13472_13473 ++ records13473_13474
theorem aligned13472_13474 :
    AlignedValid 12 4 missing13472_13474 records13472_13474 :=
  aligned13472_13473.append aligned13473_13474

def missing13474_13475 : List (BitVec (edgeCount 12)) :=
  [missing13474]
abbrev records13474_13475 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13474]
theorem aligned13474_13475 :
    AlignedValid 12 4 missing13474_13475 records13474_13475 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13474
    maskCheck13474 AlignedValid.nil

def missing13475_13476 : List (BitVec (edgeCount 12)) :=
  [missing13475]
abbrev records13475_13476 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13475]
theorem aligned13475_13476 :
    AlignedValid 12 4 missing13475_13476 records13475_13476 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13475
    maskCheck13475 AlignedValid.nil

def missing13474_13476 : List (BitVec (edgeCount 12)) :=
  missing13474_13475 ++ missing13475_13476
abbrev records13474_13476 : List Blob :=
  records13474_13475 ++ records13475_13476
theorem aligned13474_13476 :
    AlignedValid 12 4 missing13474_13476 records13474_13476 :=
  aligned13474_13475.append aligned13475_13476

def missing13472_13476 : List (BitVec (edgeCount 12)) :=
  missing13472_13474 ++ missing13474_13476
abbrev records13472_13476 : List Blob :=
  records13472_13474 ++ records13474_13476
theorem aligned13472_13476 :
    AlignedValid 12 4 missing13472_13476 records13472_13476 :=
  aligned13472_13474.append aligned13474_13476

def missing13476_13477 : List (BitVec (edgeCount 12)) :=
  [missing13476]
abbrev records13476_13477 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13476]
theorem aligned13476_13477 :
    AlignedValid 12 4 missing13476_13477 records13476_13477 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13476
    maskCheck13476 AlignedValid.nil

def missing13477_13478 : List (BitVec (edgeCount 12)) :=
  [missing13477]
abbrev records13477_13478 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13477]
theorem aligned13477_13478 :
    AlignedValid 12 4 missing13477_13478 records13477_13478 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13477
    maskCheck13477 AlignedValid.nil

def missing13476_13478 : List (BitVec (edgeCount 12)) :=
  missing13476_13477 ++ missing13477_13478
abbrev records13476_13478 : List Blob :=
  records13476_13477 ++ records13477_13478
theorem aligned13476_13478 :
    AlignedValid 12 4 missing13476_13478 records13476_13478 :=
  aligned13476_13477.append aligned13477_13478

def missing13478_13479 : List (BitVec (edgeCount 12)) :=
  [missing13478]
abbrev records13478_13479 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13478]
theorem aligned13478_13479 :
    AlignedValid 12 4 missing13478_13479 records13478_13479 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13478
    maskCheck13478 AlignedValid.nil

def missing13479_13480 : List (BitVec (edgeCount 12)) :=
  [missing13479]
abbrev records13479_13480 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13479]
theorem aligned13479_13480 :
    AlignedValid 12 4 missing13479_13480 records13479_13480 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13479
    maskCheck13479 AlignedValid.nil

def missing13478_13480 : List (BitVec (edgeCount 12)) :=
  missing13478_13479 ++ missing13479_13480
abbrev records13478_13480 : List Blob :=
  records13478_13479 ++ records13479_13480
theorem aligned13478_13480 :
    AlignedValid 12 4 missing13478_13480 records13478_13480 :=
  aligned13478_13479.append aligned13479_13480

def missing13476_13480 : List (BitVec (edgeCount 12)) :=
  missing13476_13478 ++ missing13478_13480
abbrev records13476_13480 : List Blob :=
  records13476_13478 ++ records13478_13480
theorem aligned13476_13480 :
    AlignedValid 12 4 missing13476_13480 records13476_13480 :=
  aligned13476_13478.append aligned13478_13480

def missing13472_13480 : List (BitVec (edgeCount 12)) :=
  missing13472_13476 ++ missing13476_13480
abbrev records13472_13480 : List Blob :=
  records13472_13476 ++ records13476_13480
theorem aligned13472_13480 :
    AlignedValid 12 4 missing13472_13480 records13472_13480 :=
  aligned13472_13476.append aligned13476_13480

def missing13480_13481 : List (BitVec (edgeCount 12)) :=
  [missing13480]
abbrev records13480_13481 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13480]
theorem aligned13480_13481 :
    AlignedValid 12 4 missing13480_13481 records13480_13481 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13480
    maskCheck13480 AlignedValid.nil

def missing13481_13482 : List (BitVec (edgeCount 12)) :=
  [missing13481]
abbrev records13481_13482 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13481]
theorem aligned13481_13482 :
    AlignedValid 12 4 missing13481_13482 records13481_13482 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13481
    maskCheck13481 AlignedValid.nil

def missing13480_13482 : List (BitVec (edgeCount 12)) :=
  missing13480_13481 ++ missing13481_13482
abbrev records13480_13482 : List Blob :=
  records13480_13481 ++ records13481_13482
theorem aligned13480_13482 :
    AlignedValid 12 4 missing13480_13482 records13480_13482 :=
  aligned13480_13481.append aligned13481_13482

def missing13482_13483 : List (BitVec (edgeCount 12)) :=
  [missing13482]
abbrev records13482_13483 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13482]
theorem aligned13482_13483 :
    AlignedValid 12 4 missing13482_13483 records13482_13483 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13482
    maskCheck13482 AlignedValid.nil

def missing13483_13484 : List (BitVec (edgeCount 12)) :=
  [missing13483]
abbrev records13483_13484 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13483]
theorem aligned13483_13484 :
    AlignedValid 12 4 missing13483_13484 records13483_13484 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13483
    maskCheck13483 AlignedValid.nil

def missing13482_13484 : List (BitVec (edgeCount 12)) :=
  missing13482_13483 ++ missing13483_13484
abbrev records13482_13484 : List Blob :=
  records13482_13483 ++ records13483_13484
theorem aligned13482_13484 :
    AlignedValid 12 4 missing13482_13484 records13482_13484 :=
  aligned13482_13483.append aligned13483_13484

def missing13480_13484 : List (BitVec (edgeCount 12)) :=
  missing13480_13482 ++ missing13482_13484
abbrev records13480_13484 : List Blob :=
  records13480_13482 ++ records13482_13484
theorem aligned13480_13484 :
    AlignedValid 12 4 missing13480_13484 records13480_13484 :=
  aligned13480_13482.append aligned13482_13484

def missing13484_13485 : List (BitVec (edgeCount 12)) :=
  [missing13484]
abbrev records13484_13485 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13484]
theorem aligned13484_13485 :
    AlignedValid 12 4 missing13484_13485 records13484_13485 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13484
    maskCheck13484 AlignedValid.nil

def missing13485_13486 : List (BitVec (edgeCount 12)) :=
  [missing13485]
abbrev records13485_13486 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13485]
theorem aligned13485_13486 :
    AlignedValid 12 4 missing13485_13486 records13485_13486 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13485
    maskCheck13485 AlignedValid.nil

def missing13484_13486 : List (BitVec (edgeCount 12)) :=
  missing13484_13485 ++ missing13485_13486
abbrev records13484_13486 : List Blob :=
  records13484_13485 ++ records13485_13486
theorem aligned13484_13486 :
    AlignedValid 12 4 missing13484_13486 records13484_13486 :=
  aligned13484_13485.append aligned13485_13486

def missing13486_13487 : List (BitVec (edgeCount 12)) :=
  [missing13486]
abbrev records13486_13487 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13486]
theorem aligned13486_13487 :
    AlignedValid 12 4 missing13486_13487 records13486_13487 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13486
    maskCheck13486 AlignedValid.nil

def missing13487_13488 : List (BitVec (edgeCount 12)) :=
  [missing13487]
abbrev records13487_13488 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13487]
theorem aligned13487_13488 :
    AlignedValid 12 4 missing13487_13488 records13487_13488 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13487
    maskCheck13487 AlignedValid.nil

def missing13486_13488 : List (BitVec (edgeCount 12)) :=
  missing13486_13487 ++ missing13487_13488
abbrev records13486_13488 : List Blob :=
  records13486_13487 ++ records13487_13488
theorem aligned13486_13488 :
    AlignedValid 12 4 missing13486_13488 records13486_13488 :=
  aligned13486_13487.append aligned13487_13488

def missing13484_13488 : List (BitVec (edgeCount 12)) :=
  missing13484_13486 ++ missing13486_13488
abbrev records13484_13488 : List Blob :=
  records13484_13486 ++ records13486_13488
theorem aligned13484_13488 :
    AlignedValid 12 4 missing13484_13488 records13484_13488 :=
  aligned13484_13486.append aligned13486_13488

def missing13480_13488 : List (BitVec (edgeCount 12)) :=
  missing13480_13484 ++ missing13484_13488
abbrev records13480_13488 : List Blob :=
  records13480_13484 ++ records13484_13488
theorem aligned13480_13488 :
    AlignedValid 12 4 missing13480_13488 records13480_13488 :=
  aligned13480_13484.append aligned13484_13488

def missing13472_13488 : List (BitVec (edgeCount 12)) :=
  missing13472_13480 ++ missing13480_13488
abbrev records13472_13488 : List Blob :=
  records13472_13480 ++ records13480_13488
theorem aligned13472_13488 :
    AlignedValid 12 4 missing13472_13488 records13472_13488 :=
  aligned13472_13480.append aligned13480_13488

def missing13488_13489 : List (BitVec (edgeCount 12)) :=
  [missing13488]
abbrev records13488_13489 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13488]
theorem aligned13488_13489 :
    AlignedValid 12 4 missing13488_13489 records13488_13489 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13488
    maskCheck13488 AlignedValid.nil

def missing13489_13490 : List (BitVec (edgeCount 12)) :=
  [missing13489]
abbrev records13489_13490 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13489]
theorem aligned13489_13490 :
    AlignedValid 12 4 missing13489_13490 records13489_13490 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13489
    maskCheck13489 AlignedValid.nil

def missing13488_13490 : List (BitVec (edgeCount 12)) :=
  missing13488_13489 ++ missing13489_13490
abbrev records13488_13490 : List Blob :=
  records13488_13489 ++ records13489_13490
theorem aligned13488_13490 :
    AlignedValid 12 4 missing13488_13490 records13488_13490 :=
  aligned13488_13489.append aligned13489_13490

def missing13490_13491 : List (BitVec (edgeCount 12)) :=
  [missing13490]
abbrev records13490_13491 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13490]
theorem aligned13490_13491 :
    AlignedValid 12 4 missing13490_13491 records13490_13491 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13490
    maskCheck13490 AlignedValid.nil

def missing13491_13492 : List (BitVec (edgeCount 12)) :=
  [missing13491]
abbrev records13491_13492 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13491]
theorem aligned13491_13492 :
    AlignedValid 12 4 missing13491_13492 records13491_13492 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13491
    maskCheck13491 AlignedValid.nil

def missing13490_13492 : List (BitVec (edgeCount 12)) :=
  missing13490_13491 ++ missing13491_13492
abbrev records13490_13492 : List Blob :=
  records13490_13491 ++ records13491_13492
theorem aligned13490_13492 :
    AlignedValid 12 4 missing13490_13492 records13490_13492 :=
  aligned13490_13491.append aligned13491_13492

def missing13488_13492 : List (BitVec (edgeCount 12)) :=
  missing13488_13490 ++ missing13490_13492
abbrev records13488_13492 : List Blob :=
  records13488_13490 ++ records13490_13492
theorem aligned13488_13492 :
    AlignedValid 12 4 missing13488_13492 records13488_13492 :=
  aligned13488_13490.append aligned13490_13492

def missing13492_13493 : List (BitVec (edgeCount 12)) :=
  [missing13492]
abbrev records13492_13493 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13492]
theorem aligned13492_13493 :
    AlignedValid 12 4 missing13492_13493 records13492_13493 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13492
    maskCheck13492 AlignedValid.nil

def missing13493_13494 : List (BitVec (edgeCount 12)) :=
  [missing13493]
abbrev records13493_13494 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13493]
theorem aligned13493_13494 :
    AlignedValid 12 4 missing13493_13494 records13493_13494 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13493
    maskCheck13493 AlignedValid.nil

def missing13492_13494 : List (BitVec (edgeCount 12)) :=
  missing13492_13493 ++ missing13493_13494
abbrev records13492_13494 : List Blob :=
  records13492_13493 ++ records13493_13494
theorem aligned13492_13494 :
    AlignedValid 12 4 missing13492_13494 records13492_13494 :=
  aligned13492_13493.append aligned13493_13494

def missing13494_13495 : List (BitVec (edgeCount 12)) :=
  [missing13494]
abbrev records13494_13495 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13494]
theorem aligned13494_13495 :
    AlignedValid 12 4 missing13494_13495 records13494_13495 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13494
    maskCheck13494 AlignedValid.nil

def missing13495_13496 : List (BitVec (edgeCount 12)) :=
  [missing13495]
abbrev records13495_13496 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13495]
theorem aligned13495_13496 :
    AlignedValid 12 4 missing13495_13496 records13495_13496 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13495
    maskCheck13495 AlignedValid.nil

def missing13494_13496 : List (BitVec (edgeCount 12)) :=
  missing13494_13495 ++ missing13495_13496
abbrev records13494_13496 : List Blob :=
  records13494_13495 ++ records13495_13496
theorem aligned13494_13496 :
    AlignedValid 12 4 missing13494_13496 records13494_13496 :=
  aligned13494_13495.append aligned13495_13496

def missing13492_13496 : List (BitVec (edgeCount 12)) :=
  missing13492_13494 ++ missing13494_13496
abbrev records13492_13496 : List Blob :=
  records13492_13494 ++ records13494_13496
theorem aligned13492_13496 :
    AlignedValid 12 4 missing13492_13496 records13492_13496 :=
  aligned13492_13494.append aligned13494_13496

def missing13488_13496 : List (BitVec (edgeCount 12)) :=
  missing13488_13492 ++ missing13492_13496
abbrev records13488_13496 : List Blob :=
  records13488_13492 ++ records13492_13496
theorem aligned13488_13496 :
    AlignedValid 12 4 missing13488_13496 records13488_13496 :=
  aligned13488_13492.append aligned13492_13496

def missing13496_13497 : List (BitVec (edgeCount 12)) :=
  [missing13496]
abbrev records13496_13497 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13496]
theorem aligned13496_13497 :
    AlignedValid 12 4 missing13496_13497 records13496_13497 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13496
    maskCheck13496 AlignedValid.nil

def missing13497_13498 : List (BitVec (edgeCount 12)) :=
  [missing13497]
abbrev records13497_13498 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13497]
theorem aligned13497_13498 :
    AlignedValid 12 4 missing13497_13498 records13497_13498 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13497
    maskCheck13497 AlignedValid.nil

def missing13496_13498 : List (BitVec (edgeCount 12)) :=
  missing13496_13497 ++ missing13497_13498
abbrev records13496_13498 : List Blob :=
  records13496_13497 ++ records13497_13498
theorem aligned13496_13498 :
    AlignedValid 12 4 missing13496_13498 records13496_13498 :=
  aligned13496_13497.append aligned13497_13498

def missing13498_13499 : List (BitVec (edgeCount 12)) :=
  [missing13498]
abbrev records13498_13499 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13498]
theorem aligned13498_13499 :
    AlignedValid 12 4 missing13498_13499 records13498_13499 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13498
    maskCheck13498 AlignedValid.nil

def missing13499_13500 : List (BitVec (edgeCount 12)) :=
  [missing13499]
abbrev records13499_13500 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13499]
theorem aligned13499_13500 :
    AlignedValid 12 4 missing13499_13500 records13499_13500 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13499
    maskCheck13499 AlignedValid.nil

def missing13498_13500 : List (BitVec (edgeCount 12)) :=
  missing13498_13499 ++ missing13499_13500
abbrev records13498_13500 : List Blob :=
  records13498_13499 ++ records13499_13500
theorem aligned13498_13500 :
    AlignedValid 12 4 missing13498_13500 records13498_13500 :=
  aligned13498_13499.append aligned13499_13500

def missing13496_13500 : List (BitVec (edgeCount 12)) :=
  missing13496_13498 ++ missing13498_13500
abbrev records13496_13500 : List Blob :=
  records13496_13498 ++ records13498_13500
theorem aligned13496_13500 :
    AlignedValid 12 4 missing13496_13500 records13496_13500 :=
  aligned13496_13498.append aligned13498_13500

def missing13500_13501 : List (BitVec (edgeCount 12)) :=
  [missing13500]
abbrev records13500_13501 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13500]
theorem aligned13500_13501 :
    AlignedValid 12 4 missing13500_13501 records13500_13501 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13500
    maskCheck13500 AlignedValid.nil

def missing13501_13502 : List (BitVec (edgeCount 12)) :=
  [missing13501]
abbrev records13501_13502 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13501]
theorem aligned13501_13502 :
    AlignedValid 12 4 missing13501_13502 records13501_13502 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13501
    maskCheck13501 AlignedValid.nil

def missing13500_13502 : List (BitVec (edgeCount 12)) :=
  missing13500_13501 ++ missing13501_13502
abbrev records13500_13502 : List Blob :=
  records13500_13501 ++ records13501_13502
theorem aligned13500_13502 :
    AlignedValid 12 4 missing13500_13502 records13500_13502 :=
  aligned13500_13501.append aligned13501_13502

def missing13502_13503 : List (BitVec (edgeCount 12)) :=
  [missing13502]
abbrev records13502_13503 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13502]
theorem aligned13502_13503 :
    AlignedValid 12 4 missing13502_13503 records13502_13503 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13502
    maskCheck13502 AlignedValid.nil

def missing13503_13504 : List (BitVec (edgeCount 12)) :=
  [missing13503]
abbrev records13503_13504 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13503]
theorem aligned13503_13504 :
    AlignedValid 12 4 missing13503_13504 records13503_13504 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13503
    maskCheck13503 AlignedValid.nil

def missing13502_13504 : List (BitVec (edgeCount 12)) :=
  missing13502_13503 ++ missing13503_13504
abbrev records13502_13504 : List Blob :=
  records13502_13503 ++ records13503_13504
theorem aligned13502_13504 :
    AlignedValid 12 4 missing13502_13504 records13502_13504 :=
  aligned13502_13503.append aligned13503_13504

def missing13500_13504 : List (BitVec (edgeCount 12)) :=
  missing13500_13502 ++ missing13502_13504
abbrev records13500_13504 : List Blob :=
  records13500_13502 ++ records13502_13504
theorem aligned13500_13504 :
    AlignedValid 12 4 missing13500_13504 records13500_13504 :=
  aligned13500_13502.append aligned13502_13504

def missing13496_13504 : List (BitVec (edgeCount 12)) :=
  missing13496_13500 ++ missing13500_13504
abbrev records13496_13504 : List Blob :=
  records13496_13500 ++ records13500_13504
theorem aligned13496_13504 :
    AlignedValid 12 4 missing13496_13504 records13496_13504 :=
  aligned13496_13500.append aligned13500_13504

def missing13488_13504 : List (BitVec (edgeCount 12)) :=
  missing13488_13496 ++ missing13496_13504
abbrev records13488_13504 : List Blob :=
  records13488_13496 ++ records13496_13504
theorem aligned13488_13504 :
    AlignedValid 12 4 missing13488_13504 records13488_13504 :=
  aligned13488_13496.append aligned13496_13504

def missing13472_13504 : List (BitVec (edgeCount 12)) :=
  missing13472_13488 ++ missing13488_13504
abbrev records13472_13504 : List Blob :=
  records13472_13488 ++ records13488_13504
theorem aligned13472_13504 :
    AlignedValid 12 4 missing13472_13504 records13472_13504 :=
  aligned13472_13488.append aligned13488_13504

def missing13440_13504 : List (BitVec (edgeCount 12)) :=
  missing13440_13472 ++ missing13472_13504
abbrev records13440_13504 : List Blob :=
  records13440_13472 ++ records13472_13504
theorem aligned13440_13504 :
    AlignedValid 12 4 missing13440_13504 records13440_13504 :=
  aligned13440_13472.append aligned13472_13504

def missing13504_13505 : List (BitVec (edgeCount 12)) :=
  [missing13504]
abbrev records13504_13505 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13504]
theorem aligned13504_13505 :
    AlignedValid 12 4 missing13504_13505 records13504_13505 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13504
    maskCheck13504 AlignedValid.nil

def missing13505_13506 : List (BitVec (edgeCount 12)) :=
  [missing13505]
abbrev records13505_13506 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13505]
theorem aligned13505_13506 :
    AlignedValid 12 4 missing13505_13506 records13505_13506 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13505
    maskCheck13505 AlignedValid.nil

def missing13504_13506 : List (BitVec (edgeCount 12)) :=
  missing13504_13505 ++ missing13505_13506
abbrev records13504_13506 : List Blob :=
  records13504_13505 ++ records13505_13506
theorem aligned13504_13506 :
    AlignedValid 12 4 missing13504_13506 records13504_13506 :=
  aligned13504_13505.append aligned13505_13506

def missing13506_13507 : List (BitVec (edgeCount 12)) :=
  [missing13506]
abbrev records13506_13507 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13506]
theorem aligned13506_13507 :
    AlignedValid 12 4 missing13506_13507 records13506_13507 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13506
    maskCheck13506 AlignedValid.nil

def missing13507_13508 : List (BitVec (edgeCount 12)) :=
  [missing13507]
abbrev records13507_13508 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13507]
theorem aligned13507_13508 :
    AlignedValid 12 4 missing13507_13508 records13507_13508 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13507
    maskCheck13507 AlignedValid.nil

def missing13506_13508 : List (BitVec (edgeCount 12)) :=
  missing13506_13507 ++ missing13507_13508
abbrev records13506_13508 : List Blob :=
  records13506_13507 ++ records13507_13508
theorem aligned13506_13508 :
    AlignedValid 12 4 missing13506_13508 records13506_13508 :=
  aligned13506_13507.append aligned13507_13508

def missing13504_13508 : List (BitVec (edgeCount 12)) :=
  missing13504_13506 ++ missing13506_13508
abbrev records13504_13508 : List Blob :=
  records13504_13506 ++ records13506_13508
theorem aligned13504_13508 :
    AlignedValid 12 4 missing13504_13508 records13504_13508 :=
  aligned13504_13506.append aligned13506_13508

def missing13508_13509 : List (BitVec (edgeCount 12)) :=
  [missing13508]
abbrev records13508_13509 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13508]
theorem aligned13508_13509 :
    AlignedValid 12 4 missing13508_13509 records13508_13509 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13508
    maskCheck13508 AlignedValid.nil

def missing13509_13510 : List (BitVec (edgeCount 12)) :=
  [missing13509]
abbrev records13509_13510 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13509]
theorem aligned13509_13510 :
    AlignedValid 12 4 missing13509_13510 records13509_13510 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13509
    maskCheck13509 AlignedValid.nil

def missing13508_13510 : List (BitVec (edgeCount 12)) :=
  missing13508_13509 ++ missing13509_13510
abbrev records13508_13510 : List Blob :=
  records13508_13509 ++ records13509_13510
theorem aligned13508_13510 :
    AlignedValid 12 4 missing13508_13510 records13508_13510 :=
  aligned13508_13509.append aligned13509_13510

def missing13510_13511 : List (BitVec (edgeCount 12)) :=
  [missing13510]
abbrev records13510_13511 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13510]
theorem aligned13510_13511 :
    AlignedValid 12 4 missing13510_13511 records13510_13511 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13510
    maskCheck13510 AlignedValid.nil

def missing13511_13512 : List (BitVec (edgeCount 12)) :=
  [missing13511]
abbrev records13511_13512 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13511]
theorem aligned13511_13512 :
    AlignedValid 12 4 missing13511_13512 records13511_13512 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13511
    maskCheck13511 AlignedValid.nil

def missing13510_13512 : List (BitVec (edgeCount 12)) :=
  missing13510_13511 ++ missing13511_13512
abbrev records13510_13512 : List Blob :=
  records13510_13511 ++ records13511_13512
theorem aligned13510_13512 :
    AlignedValid 12 4 missing13510_13512 records13510_13512 :=
  aligned13510_13511.append aligned13511_13512

def missing13508_13512 : List (BitVec (edgeCount 12)) :=
  missing13508_13510 ++ missing13510_13512
abbrev records13508_13512 : List Blob :=
  records13508_13510 ++ records13510_13512
theorem aligned13508_13512 :
    AlignedValid 12 4 missing13508_13512 records13508_13512 :=
  aligned13508_13510.append aligned13510_13512

def missing13504_13512 : List (BitVec (edgeCount 12)) :=
  missing13504_13508 ++ missing13508_13512
abbrev records13504_13512 : List Blob :=
  records13504_13508 ++ records13508_13512
theorem aligned13504_13512 :
    AlignedValid 12 4 missing13504_13512 records13504_13512 :=
  aligned13504_13508.append aligned13508_13512

def missing13512_13513 : List (BitVec (edgeCount 12)) :=
  [missing13512]
abbrev records13512_13513 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13512]
theorem aligned13512_13513 :
    AlignedValid 12 4 missing13512_13513 records13512_13513 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13512
    maskCheck13512 AlignedValid.nil

def missing13513_13514 : List (BitVec (edgeCount 12)) :=
  [missing13513]
abbrev records13513_13514 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13513]
theorem aligned13513_13514 :
    AlignedValid 12 4 missing13513_13514 records13513_13514 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13513
    maskCheck13513 AlignedValid.nil

def missing13512_13514 : List (BitVec (edgeCount 12)) :=
  missing13512_13513 ++ missing13513_13514
abbrev records13512_13514 : List Blob :=
  records13512_13513 ++ records13513_13514
theorem aligned13512_13514 :
    AlignedValid 12 4 missing13512_13514 records13512_13514 :=
  aligned13512_13513.append aligned13513_13514

def missing13514_13515 : List (BitVec (edgeCount 12)) :=
  [missing13514]
abbrev records13514_13515 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13514]
theorem aligned13514_13515 :
    AlignedValid 12 4 missing13514_13515 records13514_13515 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13514
    maskCheck13514 AlignedValid.nil

def missing13515_13516 : List (BitVec (edgeCount 12)) :=
  [missing13515]
abbrev records13515_13516 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13515]
theorem aligned13515_13516 :
    AlignedValid 12 4 missing13515_13516 records13515_13516 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13515
    maskCheck13515 AlignedValid.nil

def missing13514_13516 : List (BitVec (edgeCount 12)) :=
  missing13514_13515 ++ missing13515_13516
abbrev records13514_13516 : List Blob :=
  records13514_13515 ++ records13515_13516
theorem aligned13514_13516 :
    AlignedValid 12 4 missing13514_13516 records13514_13516 :=
  aligned13514_13515.append aligned13515_13516

def missing13512_13516 : List (BitVec (edgeCount 12)) :=
  missing13512_13514 ++ missing13514_13516
abbrev records13512_13516 : List Blob :=
  records13512_13514 ++ records13514_13516
theorem aligned13512_13516 :
    AlignedValid 12 4 missing13512_13516 records13512_13516 :=
  aligned13512_13514.append aligned13514_13516

def missing13516_13517 : List (BitVec (edgeCount 12)) :=
  [missing13516]
abbrev records13516_13517 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13516]
theorem aligned13516_13517 :
    AlignedValid 12 4 missing13516_13517 records13516_13517 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13516
    maskCheck13516 AlignedValid.nil

def missing13517_13518 : List (BitVec (edgeCount 12)) :=
  [missing13517]
abbrev records13517_13518 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13517]
theorem aligned13517_13518 :
    AlignedValid 12 4 missing13517_13518 records13517_13518 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13517
    maskCheck13517 AlignedValid.nil

def missing13516_13518 : List (BitVec (edgeCount 12)) :=
  missing13516_13517 ++ missing13517_13518
abbrev records13516_13518 : List Blob :=
  records13516_13517 ++ records13517_13518
theorem aligned13516_13518 :
    AlignedValid 12 4 missing13516_13518 records13516_13518 :=
  aligned13516_13517.append aligned13517_13518

def missing13518_13519 : List (BitVec (edgeCount 12)) :=
  [missing13518]
abbrev records13518_13519 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13518]
theorem aligned13518_13519 :
    AlignedValid 12 4 missing13518_13519 records13518_13519 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13518
    maskCheck13518 AlignedValid.nil

def missing13519_13520 : List (BitVec (edgeCount 12)) :=
  [missing13519]
abbrev records13519_13520 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13519]
theorem aligned13519_13520 :
    AlignedValid 12 4 missing13519_13520 records13519_13520 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13519
    maskCheck13519 AlignedValid.nil

def missing13518_13520 : List (BitVec (edgeCount 12)) :=
  missing13518_13519 ++ missing13519_13520
abbrev records13518_13520 : List Blob :=
  records13518_13519 ++ records13519_13520
theorem aligned13518_13520 :
    AlignedValid 12 4 missing13518_13520 records13518_13520 :=
  aligned13518_13519.append aligned13519_13520

def missing13516_13520 : List (BitVec (edgeCount 12)) :=
  missing13516_13518 ++ missing13518_13520
abbrev records13516_13520 : List Blob :=
  records13516_13518 ++ records13518_13520
theorem aligned13516_13520 :
    AlignedValid 12 4 missing13516_13520 records13516_13520 :=
  aligned13516_13518.append aligned13518_13520

def missing13512_13520 : List (BitVec (edgeCount 12)) :=
  missing13512_13516 ++ missing13516_13520
abbrev records13512_13520 : List Blob :=
  records13512_13516 ++ records13516_13520
theorem aligned13512_13520 :
    AlignedValid 12 4 missing13512_13520 records13512_13520 :=
  aligned13512_13516.append aligned13516_13520

def missing13504_13520 : List (BitVec (edgeCount 12)) :=
  missing13504_13512 ++ missing13512_13520
abbrev records13504_13520 : List Blob :=
  records13504_13512 ++ records13512_13520
theorem aligned13504_13520 :
    AlignedValid 12 4 missing13504_13520 records13504_13520 :=
  aligned13504_13512.append aligned13512_13520

def missing13520_13521 : List (BitVec (edgeCount 12)) :=
  [missing13520]
abbrev records13520_13521 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13520]
theorem aligned13520_13521 :
    AlignedValid 12 4 missing13520_13521 records13520_13521 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13520
    maskCheck13520 AlignedValid.nil

def missing13521_13522 : List (BitVec (edgeCount 12)) :=
  [missing13521]
abbrev records13521_13522 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13521]
theorem aligned13521_13522 :
    AlignedValid 12 4 missing13521_13522 records13521_13522 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13521
    maskCheck13521 AlignedValid.nil

def missing13520_13522 : List (BitVec (edgeCount 12)) :=
  missing13520_13521 ++ missing13521_13522
abbrev records13520_13522 : List Blob :=
  records13520_13521 ++ records13521_13522
theorem aligned13520_13522 :
    AlignedValid 12 4 missing13520_13522 records13520_13522 :=
  aligned13520_13521.append aligned13521_13522

def missing13522_13523 : List (BitVec (edgeCount 12)) :=
  [missing13522]
abbrev records13522_13523 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13522]
theorem aligned13522_13523 :
    AlignedValid 12 4 missing13522_13523 records13522_13523 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13522
    maskCheck13522 AlignedValid.nil

def missing13523_13524 : List (BitVec (edgeCount 12)) :=
  [missing13523]
abbrev records13523_13524 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13523]
theorem aligned13523_13524 :
    AlignedValid 12 4 missing13523_13524 records13523_13524 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13523
    maskCheck13523 AlignedValid.nil

def missing13522_13524 : List (BitVec (edgeCount 12)) :=
  missing13522_13523 ++ missing13523_13524
abbrev records13522_13524 : List Blob :=
  records13522_13523 ++ records13523_13524
theorem aligned13522_13524 :
    AlignedValid 12 4 missing13522_13524 records13522_13524 :=
  aligned13522_13523.append aligned13523_13524

def missing13520_13524 : List (BitVec (edgeCount 12)) :=
  missing13520_13522 ++ missing13522_13524
abbrev records13520_13524 : List Blob :=
  records13520_13522 ++ records13522_13524
theorem aligned13520_13524 :
    AlignedValid 12 4 missing13520_13524 records13520_13524 :=
  aligned13520_13522.append aligned13522_13524

def missing13524_13525 : List (BitVec (edgeCount 12)) :=
  [missing13524]
abbrev records13524_13525 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13524]
theorem aligned13524_13525 :
    AlignedValid 12 4 missing13524_13525 records13524_13525 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13524
    maskCheck13524 AlignedValid.nil

def missing13525_13526 : List (BitVec (edgeCount 12)) :=
  [missing13525]
abbrev records13525_13526 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13525]
theorem aligned13525_13526 :
    AlignedValid 12 4 missing13525_13526 records13525_13526 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13525
    maskCheck13525 AlignedValid.nil

def missing13524_13526 : List (BitVec (edgeCount 12)) :=
  missing13524_13525 ++ missing13525_13526
abbrev records13524_13526 : List Blob :=
  records13524_13525 ++ records13525_13526
theorem aligned13524_13526 :
    AlignedValid 12 4 missing13524_13526 records13524_13526 :=
  aligned13524_13525.append aligned13525_13526

def missing13526_13527 : List (BitVec (edgeCount 12)) :=
  [missing13526]
abbrev records13526_13527 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13526]
theorem aligned13526_13527 :
    AlignedValid 12 4 missing13526_13527 records13526_13527 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13526
    maskCheck13526 AlignedValid.nil

def missing13527_13528 : List (BitVec (edgeCount 12)) :=
  [missing13527]
abbrev records13527_13528 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13527]
theorem aligned13527_13528 :
    AlignedValid 12 4 missing13527_13528 records13527_13528 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13527
    maskCheck13527 AlignedValid.nil

def missing13526_13528 : List (BitVec (edgeCount 12)) :=
  missing13526_13527 ++ missing13527_13528
abbrev records13526_13528 : List Blob :=
  records13526_13527 ++ records13527_13528
theorem aligned13526_13528 :
    AlignedValid 12 4 missing13526_13528 records13526_13528 :=
  aligned13526_13527.append aligned13527_13528

def missing13524_13528 : List (BitVec (edgeCount 12)) :=
  missing13524_13526 ++ missing13526_13528
abbrev records13524_13528 : List Blob :=
  records13524_13526 ++ records13526_13528
theorem aligned13524_13528 :
    AlignedValid 12 4 missing13524_13528 records13524_13528 :=
  aligned13524_13526.append aligned13526_13528

def missing13520_13528 : List (BitVec (edgeCount 12)) :=
  missing13520_13524 ++ missing13524_13528
abbrev records13520_13528 : List Blob :=
  records13520_13524 ++ records13524_13528
theorem aligned13520_13528 :
    AlignedValid 12 4 missing13520_13528 records13520_13528 :=
  aligned13520_13524.append aligned13524_13528

def missing13528_13529 : List (BitVec (edgeCount 12)) :=
  [missing13528]
abbrev records13528_13529 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13528]
theorem aligned13528_13529 :
    AlignedValid 12 4 missing13528_13529 records13528_13529 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13528
    maskCheck13528 AlignedValid.nil

def missing13529_13530 : List (BitVec (edgeCount 12)) :=
  [missing13529]
abbrev records13529_13530 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13529]
theorem aligned13529_13530 :
    AlignedValid 12 4 missing13529_13530 records13529_13530 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13529
    maskCheck13529 AlignedValid.nil

def missing13528_13530 : List (BitVec (edgeCount 12)) :=
  missing13528_13529 ++ missing13529_13530
abbrev records13528_13530 : List Blob :=
  records13528_13529 ++ records13529_13530
theorem aligned13528_13530 :
    AlignedValid 12 4 missing13528_13530 records13528_13530 :=
  aligned13528_13529.append aligned13529_13530

def missing13530_13531 : List (BitVec (edgeCount 12)) :=
  [missing13530]
abbrev records13530_13531 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13530]
theorem aligned13530_13531 :
    AlignedValid 12 4 missing13530_13531 records13530_13531 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13530
    maskCheck13530 AlignedValid.nil

def missing13531_13532 : List (BitVec (edgeCount 12)) :=
  [missing13531]
abbrev records13531_13532 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13531]
theorem aligned13531_13532 :
    AlignedValid 12 4 missing13531_13532 records13531_13532 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13531
    maskCheck13531 AlignedValid.nil

def missing13530_13532 : List (BitVec (edgeCount 12)) :=
  missing13530_13531 ++ missing13531_13532
abbrev records13530_13532 : List Blob :=
  records13530_13531 ++ records13531_13532
theorem aligned13530_13532 :
    AlignedValid 12 4 missing13530_13532 records13530_13532 :=
  aligned13530_13531.append aligned13531_13532

def missing13528_13532 : List (BitVec (edgeCount 12)) :=
  missing13528_13530 ++ missing13530_13532
abbrev records13528_13532 : List Blob :=
  records13528_13530 ++ records13530_13532
theorem aligned13528_13532 :
    AlignedValid 12 4 missing13528_13532 records13528_13532 :=
  aligned13528_13530.append aligned13530_13532

def missing13532_13533 : List (BitVec (edgeCount 12)) :=
  [missing13532]
abbrev records13532_13533 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13532]
theorem aligned13532_13533 :
    AlignedValid 12 4 missing13532_13533 records13532_13533 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13532
    maskCheck13532 AlignedValid.nil

def missing13533_13534 : List (BitVec (edgeCount 12)) :=
  [missing13533]
abbrev records13533_13534 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13533]
theorem aligned13533_13534 :
    AlignedValid 12 4 missing13533_13534 records13533_13534 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13533
    maskCheck13533 AlignedValid.nil

def missing13532_13534 : List (BitVec (edgeCount 12)) :=
  missing13532_13533 ++ missing13533_13534
abbrev records13532_13534 : List Blob :=
  records13532_13533 ++ records13533_13534
theorem aligned13532_13534 :
    AlignedValid 12 4 missing13532_13534 records13532_13534 :=
  aligned13532_13533.append aligned13533_13534

def missing13534_13535 : List (BitVec (edgeCount 12)) :=
  [missing13534]
abbrev records13534_13535 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13534]
theorem aligned13534_13535 :
    AlignedValid 12 4 missing13534_13535 records13534_13535 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13534
    maskCheck13534 AlignedValid.nil

def missing13535_13536 : List (BitVec (edgeCount 12)) :=
  [missing13535]
abbrev records13535_13536 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13535]
theorem aligned13535_13536 :
    AlignedValid 12 4 missing13535_13536 records13535_13536 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13535
    maskCheck13535 AlignedValid.nil

def missing13534_13536 : List (BitVec (edgeCount 12)) :=
  missing13534_13535 ++ missing13535_13536
abbrev records13534_13536 : List Blob :=
  records13534_13535 ++ records13535_13536
theorem aligned13534_13536 :
    AlignedValid 12 4 missing13534_13536 records13534_13536 :=
  aligned13534_13535.append aligned13535_13536

def missing13532_13536 : List (BitVec (edgeCount 12)) :=
  missing13532_13534 ++ missing13534_13536
abbrev records13532_13536 : List Blob :=
  records13532_13534 ++ records13534_13536
theorem aligned13532_13536 :
    AlignedValid 12 4 missing13532_13536 records13532_13536 :=
  aligned13532_13534.append aligned13534_13536

def missing13528_13536 : List (BitVec (edgeCount 12)) :=
  missing13528_13532 ++ missing13532_13536
abbrev records13528_13536 : List Blob :=
  records13528_13532 ++ records13532_13536
theorem aligned13528_13536 :
    AlignedValid 12 4 missing13528_13536 records13528_13536 :=
  aligned13528_13532.append aligned13532_13536

def missing13520_13536 : List (BitVec (edgeCount 12)) :=
  missing13520_13528 ++ missing13528_13536
abbrev records13520_13536 : List Blob :=
  records13520_13528 ++ records13528_13536
theorem aligned13520_13536 :
    AlignedValid 12 4 missing13520_13536 records13520_13536 :=
  aligned13520_13528.append aligned13528_13536

def missing13504_13536 : List (BitVec (edgeCount 12)) :=
  missing13504_13520 ++ missing13520_13536
abbrev records13504_13536 : List Blob :=
  records13504_13520 ++ records13520_13536
theorem aligned13504_13536 :
    AlignedValid 12 4 missing13504_13536 records13504_13536 :=
  aligned13504_13520.append aligned13520_13536

def missing13536_13537 : List (BitVec (edgeCount 12)) :=
  [missing13536]
abbrev records13536_13537 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13536]
theorem aligned13536_13537 :
    AlignedValid 12 4 missing13536_13537 records13536_13537 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13536
    maskCheck13536 AlignedValid.nil

def missing13537_13538 : List (BitVec (edgeCount 12)) :=
  [missing13537]
abbrev records13537_13538 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13537]
theorem aligned13537_13538 :
    AlignedValid 12 4 missing13537_13538 records13537_13538 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13537
    maskCheck13537 AlignedValid.nil

def missing13536_13538 : List (BitVec (edgeCount 12)) :=
  missing13536_13537 ++ missing13537_13538
abbrev records13536_13538 : List Blob :=
  records13536_13537 ++ records13537_13538
theorem aligned13536_13538 :
    AlignedValid 12 4 missing13536_13538 records13536_13538 :=
  aligned13536_13537.append aligned13537_13538

def missing13538_13539 : List (BitVec (edgeCount 12)) :=
  [missing13538]
abbrev records13538_13539 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13538]
theorem aligned13538_13539 :
    AlignedValid 12 4 missing13538_13539 records13538_13539 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13538
    maskCheck13538 AlignedValid.nil

def missing13539_13540 : List (BitVec (edgeCount 12)) :=
  [missing13539]
abbrev records13539_13540 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13539]
theorem aligned13539_13540 :
    AlignedValid 12 4 missing13539_13540 records13539_13540 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13539
    maskCheck13539 AlignedValid.nil

def missing13538_13540 : List (BitVec (edgeCount 12)) :=
  missing13538_13539 ++ missing13539_13540
abbrev records13538_13540 : List Blob :=
  records13538_13539 ++ records13539_13540
theorem aligned13538_13540 :
    AlignedValid 12 4 missing13538_13540 records13538_13540 :=
  aligned13538_13539.append aligned13539_13540

def missing13536_13540 : List (BitVec (edgeCount 12)) :=
  missing13536_13538 ++ missing13538_13540
abbrev records13536_13540 : List Blob :=
  records13536_13538 ++ records13538_13540
theorem aligned13536_13540 :
    AlignedValid 12 4 missing13536_13540 records13536_13540 :=
  aligned13536_13538.append aligned13538_13540

def missing13540_13541 : List (BitVec (edgeCount 12)) :=
  [missing13540]
abbrev records13540_13541 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13540]
theorem aligned13540_13541 :
    AlignedValid 12 4 missing13540_13541 records13540_13541 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13540
    maskCheck13540 AlignedValid.nil

def missing13541_13542 : List (BitVec (edgeCount 12)) :=
  [missing13541]
abbrev records13541_13542 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13541]
theorem aligned13541_13542 :
    AlignedValid 12 4 missing13541_13542 records13541_13542 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13541
    maskCheck13541 AlignedValid.nil

def missing13540_13542 : List (BitVec (edgeCount 12)) :=
  missing13540_13541 ++ missing13541_13542
abbrev records13540_13542 : List Blob :=
  records13540_13541 ++ records13541_13542
theorem aligned13540_13542 :
    AlignedValid 12 4 missing13540_13542 records13540_13542 :=
  aligned13540_13541.append aligned13541_13542

def missing13542_13543 : List (BitVec (edgeCount 12)) :=
  [missing13542]
abbrev records13542_13543 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13542]
theorem aligned13542_13543 :
    AlignedValid 12 4 missing13542_13543 records13542_13543 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13542
    maskCheck13542 AlignedValid.nil

def missing13543_13544 : List (BitVec (edgeCount 12)) :=
  [missing13543]
abbrev records13543_13544 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13543]
theorem aligned13543_13544 :
    AlignedValid 12 4 missing13543_13544 records13543_13544 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13543
    maskCheck13543 AlignedValid.nil

def missing13542_13544 : List (BitVec (edgeCount 12)) :=
  missing13542_13543 ++ missing13543_13544
abbrev records13542_13544 : List Blob :=
  records13542_13543 ++ records13543_13544
theorem aligned13542_13544 :
    AlignedValid 12 4 missing13542_13544 records13542_13544 :=
  aligned13542_13543.append aligned13543_13544

def missing13540_13544 : List (BitVec (edgeCount 12)) :=
  missing13540_13542 ++ missing13542_13544
abbrev records13540_13544 : List Blob :=
  records13540_13542 ++ records13542_13544
theorem aligned13540_13544 :
    AlignedValid 12 4 missing13540_13544 records13540_13544 :=
  aligned13540_13542.append aligned13542_13544

def missing13536_13544 : List (BitVec (edgeCount 12)) :=
  missing13536_13540 ++ missing13540_13544
abbrev records13536_13544 : List Blob :=
  records13536_13540 ++ records13540_13544
theorem aligned13536_13544 :
    AlignedValid 12 4 missing13536_13544 records13536_13544 :=
  aligned13536_13540.append aligned13540_13544

def missing13544_13545 : List (BitVec (edgeCount 12)) :=
  [missing13544]
abbrev records13544_13545 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13544]
theorem aligned13544_13545 :
    AlignedValid 12 4 missing13544_13545 records13544_13545 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13544
    maskCheck13544 AlignedValid.nil

def missing13545_13546 : List (BitVec (edgeCount 12)) :=
  [missing13545]
abbrev records13545_13546 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13545]
theorem aligned13545_13546 :
    AlignedValid 12 4 missing13545_13546 records13545_13546 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13545
    maskCheck13545 AlignedValid.nil

def missing13544_13546 : List (BitVec (edgeCount 12)) :=
  missing13544_13545 ++ missing13545_13546
abbrev records13544_13546 : List Blob :=
  records13544_13545 ++ records13545_13546
theorem aligned13544_13546 :
    AlignedValid 12 4 missing13544_13546 records13544_13546 :=
  aligned13544_13545.append aligned13545_13546

def missing13546_13547 : List (BitVec (edgeCount 12)) :=
  [missing13546]
abbrev records13546_13547 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13546]
theorem aligned13546_13547 :
    AlignedValid 12 4 missing13546_13547 records13546_13547 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13546
    maskCheck13546 AlignedValid.nil

def missing13547_13548 : List (BitVec (edgeCount 12)) :=
  [missing13547]
abbrev records13547_13548 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13547]
theorem aligned13547_13548 :
    AlignedValid 12 4 missing13547_13548 records13547_13548 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13547
    maskCheck13547 AlignedValid.nil

def missing13546_13548 : List (BitVec (edgeCount 12)) :=
  missing13546_13547 ++ missing13547_13548
abbrev records13546_13548 : List Blob :=
  records13546_13547 ++ records13547_13548
theorem aligned13546_13548 :
    AlignedValid 12 4 missing13546_13548 records13546_13548 :=
  aligned13546_13547.append aligned13547_13548

def missing13544_13548 : List (BitVec (edgeCount 12)) :=
  missing13544_13546 ++ missing13546_13548
abbrev records13544_13548 : List Blob :=
  records13544_13546 ++ records13546_13548
theorem aligned13544_13548 :
    AlignedValid 12 4 missing13544_13548 records13544_13548 :=
  aligned13544_13546.append aligned13546_13548

def missing13548_13549 : List (BitVec (edgeCount 12)) :=
  [missing13548]
abbrev records13548_13549 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13548]
theorem aligned13548_13549 :
    AlignedValid 12 4 missing13548_13549 records13548_13549 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13548
    maskCheck13548 AlignedValid.nil

def missing13549_13550 : List (BitVec (edgeCount 12)) :=
  [missing13549]
abbrev records13549_13550 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13549]
theorem aligned13549_13550 :
    AlignedValid 12 4 missing13549_13550 records13549_13550 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13549
    maskCheck13549 AlignedValid.nil

def missing13548_13550 : List (BitVec (edgeCount 12)) :=
  missing13548_13549 ++ missing13549_13550
abbrev records13548_13550 : List Blob :=
  records13548_13549 ++ records13549_13550
theorem aligned13548_13550 :
    AlignedValid 12 4 missing13548_13550 records13548_13550 :=
  aligned13548_13549.append aligned13549_13550

def missing13550_13551 : List (BitVec (edgeCount 12)) :=
  [missing13550]
abbrev records13550_13551 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13550]
theorem aligned13550_13551 :
    AlignedValid 12 4 missing13550_13551 records13550_13551 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13550
    maskCheck13550 AlignedValid.nil

def missing13551_13552 : List (BitVec (edgeCount 12)) :=
  [missing13551]
abbrev records13551_13552 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13551]
theorem aligned13551_13552 :
    AlignedValid 12 4 missing13551_13552 records13551_13552 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13551
    maskCheck13551 AlignedValid.nil

def missing13550_13552 : List (BitVec (edgeCount 12)) :=
  missing13550_13551 ++ missing13551_13552
abbrev records13550_13552 : List Blob :=
  records13550_13551 ++ records13551_13552
theorem aligned13550_13552 :
    AlignedValid 12 4 missing13550_13552 records13550_13552 :=
  aligned13550_13551.append aligned13551_13552

def missing13548_13552 : List (BitVec (edgeCount 12)) :=
  missing13548_13550 ++ missing13550_13552
abbrev records13548_13552 : List Blob :=
  records13548_13550 ++ records13550_13552
theorem aligned13548_13552 :
    AlignedValid 12 4 missing13548_13552 records13548_13552 :=
  aligned13548_13550.append aligned13550_13552

def missing13544_13552 : List (BitVec (edgeCount 12)) :=
  missing13544_13548 ++ missing13548_13552
abbrev records13544_13552 : List Blob :=
  records13544_13548 ++ records13548_13552
theorem aligned13544_13552 :
    AlignedValid 12 4 missing13544_13552 records13544_13552 :=
  aligned13544_13548.append aligned13548_13552

def missing13536_13552 : List (BitVec (edgeCount 12)) :=
  missing13536_13544 ++ missing13544_13552
abbrev records13536_13552 : List Blob :=
  records13536_13544 ++ records13544_13552
theorem aligned13536_13552 :
    AlignedValid 12 4 missing13536_13552 records13536_13552 :=
  aligned13536_13544.append aligned13544_13552

def missing13552_13553 : List (BitVec (edgeCount 12)) :=
  [missing13552]
abbrev records13552_13553 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13552]
theorem aligned13552_13553 :
    AlignedValid 12 4 missing13552_13553 records13552_13553 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13552
    maskCheck13552 AlignedValid.nil

def missing13553_13554 : List (BitVec (edgeCount 12)) :=
  [missing13553]
abbrev records13553_13554 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13553]
theorem aligned13553_13554 :
    AlignedValid 12 4 missing13553_13554 records13553_13554 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13553
    maskCheck13553 AlignedValid.nil

def missing13552_13554 : List (BitVec (edgeCount 12)) :=
  missing13552_13553 ++ missing13553_13554
abbrev records13552_13554 : List Blob :=
  records13552_13553 ++ records13553_13554
theorem aligned13552_13554 :
    AlignedValid 12 4 missing13552_13554 records13552_13554 :=
  aligned13552_13553.append aligned13553_13554

def missing13554_13555 : List (BitVec (edgeCount 12)) :=
  [missing13554]
abbrev records13554_13555 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13554]
theorem aligned13554_13555 :
    AlignedValid 12 4 missing13554_13555 records13554_13555 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13554
    maskCheck13554 AlignedValid.nil

def missing13555_13556 : List (BitVec (edgeCount 12)) :=
  [missing13555]
abbrev records13555_13556 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13555]
theorem aligned13555_13556 :
    AlignedValid 12 4 missing13555_13556 records13555_13556 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13555
    maskCheck13555 AlignedValid.nil

def missing13554_13556 : List (BitVec (edgeCount 12)) :=
  missing13554_13555 ++ missing13555_13556
abbrev records13554_13556 : List Blob :=
  records13554_13555 ++ records13555_13556
theorem aligned13554_13556 :
    AlignedValid 12 4 missing13554_13556 records13554_13556 :=
  aligned13554_13555.append aligned13555_13556

def missing13552_13556 : List (BitVec (edgeCount 12)) :=
  missing13552_13554 ++ missing13554_13556
abbrev records13552_13556 : List Blob :=
  records13552_13554 ++ records13554_13556
theorem aligned13552_13556 :
    AlignedValid 12 4 missing13552_13556 records13552_13556 :=
  aligned13552_13554.append aligned13554_13556

def missing13556_13557 : List (BitVec (edgeCount 12)) :=
  [missing13556]
abbrev records13556_13557 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13556]
theorem aligned13556_13557 :
    AlignedValid 12 4 missing13556_13557 records13556_13557 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13556
    maskCheck13556 AlignedValid.nil

def missing13557_13558 : List (BitVec (edgeCount 12)) :=
  [missing13557]
abbrev records13557_13558 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13557]
theorem aligned13557_13558 :
    AlignedValid 12 4 missing13557_13558 records13557_13558 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13557
    maskCheck13557 AlignedValid.nil

def missing13556_13558 : List (BitVec (edgeCount 12)) :=
  missing13556_13557 ++ missing13557_13558
abbrev records13556_13558 : List Blob :=
  records13556_13557 ++ records13557_13558
theorem aligned13556_13558 :
    AlignedValid 12 4 missing13556_13558 records13556_13558 :=
  aligned13556_13557.append aligned13557_13558

def missing13558_13559 : List (BitVec (edgeCount 12)) :=
  [missing13558]
abbrev records13558_13559 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13558]
theorem aligned13558_13559 :
    AlignedValid 12 4 missing13558_13559 records13558_13559 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13558
    maskCheck13558 AlignedValid.nil

def missing13559_13560 : List (BitVec (edgeCount 12)) :=
  [missing13559]
abbrev records13559_13560 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13559]
theorem aligned13559_13560 :
    AlignedValid 12 4 missing13559_13560 records13559_13560 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13559
    maskCheck13559 AlignedValid.nil

def missing13558_13560 : List (BitVec (edgeCount 12)) :=
  missing13558_13559 ++ missing13559_13560
abbrev records13558_13560 : List Blob :=
  records13558_13559 ++ records13559_13560
theorem aligned13558_13560 :
    AlignedValid 12 4 missing13558_13560 records13558_13560 :=
  aligned13558_13559.append aligned13559_13560

def missing13556_13560 : List (BitVec (edgeCount 12)) :=
  missing13556_13558 ++ missing13558_13560
abbrev records13556_13560 : List Blob :=
  records13556_13558 ++ records13558_13560
theorem aligned13556_13560 :
    AlignedValid 12 4 missing13556_13560 records13556_13560 :=
  aligned13556_13558.append aligned13558_13560

def missing13552_13560 : List (BitVec (edgeCount 12)) :=
  missing13552_13556 ++ missing13556_13560
abbrev records13552_13560 : List Blob :=
  records13552_13556 ++ records13556_13560
theorem aligned13552_13560 :
    AlignedValid 12 4 missing13552_13560 records13552_13560 :=
  aligned13552_13556.append aligned13556_13560

def missing13560_13561 : List (BitVec (edgeCount 12)) :=
  [missing13560]
abbrev records13560_13561 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13560]
theorem aligned13560_13561 :
    AlignedValid 12 4 missing13560_13561 records13560_13561 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13560
    maskCheck13560 AlignedValid.nil

def missing13561_13562 : List (BitVec (edgeCount 12)) :=
  [missing13561]
abbrev records13561_13562 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13561]
theorem aligned13561_13562 :
    AlignedValid 12 4 missing13561_13562 records13561_13562 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13561
    maskCheck13561 AlignedValid.nil

def missing13560_13562 : List (BitVec (edgeCount 12)) :=
  missing13560_13561 ++ missing13561_13562
abbrev records13560_13562 : List Blob :=
  records13560_13561 ++ records13561_13562
theorem aligned13560_13562 :
    AlignedValid 12 4 missing13560_13562 records13560_13562 :=
  aligned13560_13561.append aligned13561_13562

def missing13562_13563 : List (BitVec (edgeCount 12)) :=
  [missing13562]
abbrev records13562_13563 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13562]
theorem aligned13562_13563 :
    AlignedValid 12 4 missing13562_13563 records13562_13563 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13562
    maskCheck13562 AlignedValid.nil

def missing13563_13564 : List (BitVec (edgeCount 12)) :=
  [missing13563]
abbrev records13563_13564 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13563]
theorem aligned13563_13564 :
    AlignedValid 12 4 missing13563_13564 records13563_13564 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13563
    maskCheck13563 AlignedValid.nil

def missing13562_13564 : List (BitVec (edgeCount 12)) :=
  missing13562_13563 ++ missing13563_13564
abbrev records13562_13564 : List Blob :=
  records13562_13563 ++ records13563_13564
theorem aligned13562_13564 :
    AlignedValid 12 4 missing13562_13564 records13562_13564 :=
  aligned13562_13563.append aligned13563_13564

def missing13560_13564 : List (BitVec (edgeCount 12)) :=
  missing13560_13562 ++ missing13562_13564
abbrev records13560_13564 : List Blob :=
  records13560_13562 ++ records13562_13564
theorem aligned13560_13564 :
    AlignedValid 12 4 missing13560_13564 records13560_13564 :=
  aligned13560_13562.append aligned13562_13564

def missing13564_13565 : List (BitVec (edgeCount 12)) :=
  [missing13564]
abbrev records13564_13565 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13564]
theorem aligned13564_13565 :
    AlignedValid 12 4 missing13564_13565 records13564_13565 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13564
    maskCheck13564 AlignedValid.nil

def missing13565_13566 : List (BitVec (edgeCount 12)) :=
  [missing13565]
abbrev records13565_13566 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13565]
theorem aligned13565_13566 :
    AlignedValid 12 4 missing13565_13566 records13565_13566 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13565
    maskCheck13565 AlignedValid.nil

def missing13564_13566 : List (BitVec (edgeCount 12)) :=
  missing13564_13565 ++ missing13565_13566
abbrev records13564_13566 : List Blob :=
  records13564_13565 ++ records13565_13566
theorem aligned13564_13566 :
    AlignedValid 12 4 missing13564_13566 records13564_13566 :=
  aligned13564_13565.append aligned13565_13566

def missing13566_13567 : List (BitVec (edgeCount 12)) :=
  [missing13566]
abbrev records13566_13567 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13566]
theorem aligned13566_13567 :
    AlignedValid 12 4 missing13566_13567 records13566_13567 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13566
    maskCheck13566 AlignedValid.nil

def missing13567_13568 : List (BitVec (edgeCount 12)) :=
  [missing13567]
abbrev records13567_13568 : List Blob :=
  [StrongPackedBucketN12A4Shard105.record13567]
theorem aligned13567_13568 :
    AlignedValid 12 4 missing13567_13568 records13567_13568 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard105.check13567
    maskCheck13567 AlignedValid.nil

def missing13566_13568 : List (BitVec (edgeCount 12)) :=
  missing13566_13567 ++ missing13567_13568
abbrev records13566_13568 : List Blob :=
  records13566_13567 ++ records13567_13568
theorem aligned13566_13568 :
    AlignedValid 12 4 missing13566_13568 records13566_13568 :=
  aligned13566_13567.append aligned13567_13568

def missing13564_13568 : List (BitVec (edgeCount 12)) :=
  missing13564_13566 ++ missing13566_13568
abbrev records13564_13568 : List Blob :=
  records13564_13566 ++ records13566_13568
theorem aligned13564_13568 :
    AlignedValid 12 4 missing13564_13568 records13564_13568 :=
  aligned13564_13566.append aligned13566_13568

def missing13560_13568 : List (BitVec (edgeCount 12)) :=
  missing13560_13564 ++ missing13564_13568
abbrev records13560_13568 : List Blob :=
  records13560_13564 ++ records13564_13568
theorem aligned13560_13568 :
    AlignedValid 12 4 missing13560_13568 records13560_13568 :=
  aligned13560_13564.append aligned13564_13568

def missing13552_13568 : List (BitVec (edgeCount 12)) :=
  missing13552_13560 ++ missing13560_13568
abbrev records13552_13568 : List Blob :=
  records13552_13560 ++ records13560_13568
theorem aligned13552_13568 :
    AlignedValid 12 4 missing13552_13568 records13552_13568 :=
  aligned13552_13560.append aligned13560_13568

def missing13536_13568 : List (BitVec (edgeCount 12)) :=
  missing13536_13552 ++ missing13552_13568
abbrev records13536_13568 : List Blob :=
  records13536_13552 ++ records13552_13568
theorem aligned13536_13568 :
    AlignedValid 12 4 missing13536_13568 records13536_13568 :=
  aligned13536_13552.append aligned13552_13568

def missing13504_13568 : List (BitVec (edgeCount 12)) :=
  missing13504_13536 ++ missing13536_13568
abbrev records13504_13568 : List Blob :=
  records13504_13536 ++ records13536_13568
theorem aligned13504_13568 :
    AlignedValid 12 4 missing13504_13568 records13504_13568 :=
  aligned13504_13536.append aligned13536_13568

def missing13440_13568 : List (BitVec (edgeCount 12)) :=
  missing13440_13504 ++ missing13504_13568
abbrev records13440_13568 : List Blob :=
  records13440_13504 ++ records13504_13568
theorem aligned13440_13568 :
    AlignedValid 12 4 missing13440_13568 records13440_13568 :=
  aligned13440_13504.append aligned13504_13568

abbrev missing : List (BitVec (edgeCount 12)) := missing13440_13568
abbrev records : List Blob := records13440_13568
theorem aligned : AlignedValid 12 4 missing records := aligned13440_13568

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard105
