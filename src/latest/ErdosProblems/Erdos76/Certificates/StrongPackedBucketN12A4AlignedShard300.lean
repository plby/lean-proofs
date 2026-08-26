/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard300

/-! Decode-only alignment checks for n=12, a=4, records 38400--38527. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard300

open PackedBucketCertificate

def missing38400 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1369940362541432832
theorem maskCheck38400 :
    checkMaskFor missing38400 StrongPackedBucketN12A4Shard300.record38400 = true := by
  decide

def missing38401 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1514055550617288704
theorem maskCheck38401 :
    checkMaskFor missing38401 StrongPackedBucketN12A4Shard300.record38401 = true := by
  decide

def missing38402 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2414775476091387904
theorem maskCheck38402 :
    checkMaskFor missing38402 StrongPackedBucketN12A4Shard300.record38402 = true := by
  decide

def missing38403 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3495639386660306944
theorem maskCheck38403 :
    checkMaskFor missing38403 StrongPackedBucketN12A4Shard300.record38403 = true := by
  decide

def missing38404 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4828704876361973760
theorem maskCheck38404 :
    checkMaskFor missing38404 StrongPackedBucketN12A4Shard300.record38404 = true := by
  decide

def missing38405 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4972820064437829632
theorem maskCheck38405 :
    checkMaskFor missing38405 StrongPackedBucketN12A4Shard300.record38405 = true := by
  decide

def missing38406 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 253610604906971136
theorem maskCheck38406 :
    checkMaskFor missing38406 StrongPackedBucketN12A4Shard300.record38406 = true := by
  decide

def missing38407 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 397725792982827008
theorem maskCheck38407 :
    checkMaskFor missing38407 StrongPackedBucketN12A4Shard300.record38407 = true := by
  decide

def missing38408 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 505812184039718912
theorem maskCheck38408 :
    checkMaskFor missing38408 StrongPackedBucketN12A4Shard300.record38408 = true := by
  decide

def missing38409 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 794042560191430656
theorem maskCheck38409 :
    checkMaskFor missing38409 StrongPackedBucketN12A4Shard300.record38409 = true := by
  decide

def missing38410 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 902128951248322560
theorem maskCheck38410 :
    checkMaskFor missing38410 StrongPackedBucketN12A4Shard300.record38410 = true := by
  decide

def missing38411 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 938157748267286528
theorem maskCheck38411 :
    checkMaskFor missing38411 StrongPackedBucketN12A4Shard300.record38411 = true := by
  decide

def missing38412 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1766820079703457792
theorem maskCheck38412 :
    checkMaskFor missing38412 StrongPackedBucketN12A4Shard300.record38412 = true := by
  decide

def missing38413 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1802848876722421760
theorem maskCheck38413 :
    checkMaskFor missing38413 StrongPackedBucketN12A4Shard300.record38413 = true := by
  decide

def missing38414 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2019021658836205568
theorem maskCheck38414 :
    checkMaskFor missing38414 StrongPackedBucketN12A4Shard300.record38414 = true := by
  decide

def missing38415 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2631511208158593024
theorem maskCheck38415 :
    checkMaskFor missing38415 StrongPackedBucketN12A4Shard300.record38415 = true := by
  decide

def missing38416 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2919741584310304768
theorem maskCheck38416 :
    checkMaskFor missing38416 StrongPackedBucketN12A4Shard300.record38416 = true := by
  decide

def missing38417 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4829267826315395072
theorem maskCheck38417 :
    checkMaskFor missing38417 StrongPackedBucketN12A4Shard300.record38417 = true := by
  decide

def missing38418 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4973383014391250944
theorem maskCheck38418 :
    checkMaskFor missing38418 StrongPackedBucketN12A4Shard300.record38418 = true := by
  decide

def missing38419 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5261613390542962688
theorem maskCheck38419 :
    checkMaskFor missing38419 StrongPackedBucketN12A4Shard300.record38419 = true := by
  decide

def missing38420 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18556239490540666880
theorem maskCheck38420 :
    checkMaskFor missing38420 StrongPackedBucketN12A4Shard300.record38420 = true := by
  decide

def missing38421 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18664325881597558784
theorem maskCheck38421 :
    checkMaskFor missing38421 StrongPackedBucketN12A4Shard300.record38421 = true := by
  decide

def missing38422 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18772412272654450688
theorem maskCheck38422 :
    checkMaskFor missing38422 StrongPackedBucketN12A4Shard300.record38422 = true := by
  decide

def missing38423 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18808441069673414656
theorem maskCheck38423 :
    checkMaskFor missing38423 StrongPackedBucketN12A4Shard300.record38423 = true := by
  decide

def missing38424 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19060642648806162432
theorem maskCheck38424 :
    checkMaskFor missing38424 StrongPackedBucketN12A4Shard300.record38424 = true := by
  decide

def missing38425 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19096671445825126400
theorem maskCheck38425 :
    checkMaskFor missing38425 StrongPackedBucketN12A4Shard300.record38425 = true := by
  decide

def missing38426 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19637103401109585920
theorem maskCheck38426 :
    checkMaskFor missing38426 StrongPackedBucketN12A4Shard300.record38426 = true := by
  decide

def missing38427 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19673132198128549888
theorem maskCheck38427 :
    checkMaskFor missing38427 StrongPackedBucketN12A4Shard300.record38427 = true := by
  decide

def missing38428 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19889304980242333696
theorem maskCheck38428 :
    checkMaskFor missing38428 StrongPackedBucketN12A4Shard300.record38428 = true := by
  decide

def missing38429 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20177535356394045440
theorem maskCheck38429 :
    checkMaskFor missing38429 StrongPackedBucketN12A4Shard300.record38429 = true := by
  decide

def missing38430 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20790024905716432896
theorem maskCheck38430 :
    checkMaskFor missing38430 StrongPackedBucketN12A4Shard300.record38430 = true := by
  decide

def missing38431 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23131896711949090816
theorem maskCheck38431 :
    checkMaskFor missing38431 StrongPackedBucketN12A4Shard300.record38431 = true := by
  decide

def missing38432 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55377670043921842176
theorem maskCheck38432 :
    checkMaskFor missing38432 StrongPackedBucketN12A4Shard300.record38432 = true := by
  decide

def missing38433 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55413698840940806144
theorem maskCheck38433 :
    checkMaskFor missing38433 StrongPackedBucketN12A4Shard300.record38433 = true := by
  decide

def missing38434 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55629871623054589952
theorem maskCheck38434 :
    checkMaskFor missing38434 StrongPackedBucketN12A4Shard300.record38434 = true := by
  decide

def missing38435 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55918101999206301696
theorem maskCheck38435 :
    checkMaskFor missing38435 StrongPackedBucketN12A4Shard300.record38435 = true := by
  decide

def missing38436 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 252800540788948992
theorem maskCheck38436 :
    checkMaskFor missing38436 StrongPackedBucketN12A4Shard300.record38436 = true := by
  decide

def missing38437 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 505002119921696768
theorem maskCheck38437 :
    checkMaskFor missing38437 StrongPackedBucketN12A4Shard300.record38437 = true := by
  decide

def missing38438 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 685146105016516608
theorem maskCheck38438 :
    checkMaskFor missing38438 StrongPackedBucketN12A4Shard300.record38438 = true := by
  decide

def missing38439 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 793232496073408512
theorem maskCheck38439 :
    checkMaskFor missing38439 StrongPackedBucketN12A4Shard300.record38439 = true := by
  decide

def missing38440 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1261606857319940096
theorem maskCheck38440 :
    checkMaskFor missing38440 StrongPackedBucketN12A4Shard300.record38440 = true := by
  decide

def missing38441 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1369693248376832000
theorem maskCheck38441 :
    checkMaskFor missing38441 StrongPackedBucketN12A4Shard300.record38441 = true := by
  decide

def missing38442 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1766010015585435648
theorem maskCheck38442 :
    checkMaskFor missing38442 StrongPackedBucketN12A4Shard300.record38442 = true := by
  decide

def missing38443 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2414528361926787072
theorem maskCheck38443 :
    checkMaskFor missing38443 StrongPackedBucketN12A4Shard300.record38443 = true := by
  decide

def missing38444 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2918931520192282624
theorem maskCheck38444 :
    checkMaskFor missing38444 StrongPackedBucketN12A4Shard300.record38444 = true := by
  decide

def missing38445 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4035824227780165632
theorem maskCheck38445 :
    checkMaskFor missing38445 StrongPackedBucketN12A4Shard300.record38445 = true := by
  decide

def missing38446 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4720371371140481024
theorem maskCheck38446 :
    checkMaskFor missing38446 StrongPackedBucketN12A4Shard300.record38446 = true := by
  decide

def missing38447 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4828457762197372928
theorem maskCheck38447 :
    checkMaskFor missing38447 StrongPackedBucketN12A4Shard300.record38447 = true := by
  decide

def missing38448 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4936544153254264832
theorem maskCheck38448 :
    checkMaskFor missing38448 StrongPackedBucketN12A4Shard300.record38448 = true := by
  decide

def missing38449 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4972572950273228800
theorem maskCheck38449 :
    checkMaskFor missing38449 StrongPackedBucketN12A4Shard300.record38449 = true := by
  decide

def missing38450 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5476976108538724352
theorem maskCheck38450 :
    checkMaskFor missing38450 StrongPackedBucketN12A4Shard300.record38450 = true := by
  decide

def missing38451 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6053436860842147840
theorem maskCheck38451 :
    checkMaskFor missing38451 StrongPackedBucketN12A4Shard300.record38451 = true := by
  decide

def missing38452 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37002173500132196352
theorem maskCheck38452 :
    checkMaskFor missing38452 StrongPackedBucketN12A4Shard300.record38452 = true := by
  decide

def missing38453 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37506576658397691904
theorem maskCheck38453 :
    checkMaskFor missing38453 StrongPackedBucketN12A4Shard300.record38453 = true := by
  decide

def missing38454 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38083037410701115392
theorem maskCheck38454 :
    checkMaskFor missing38454 StrongPackedBucketN12A4Shard300.record38454 = true := by
  decide

def missing38455 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 253891256323702784
theorem maskCheck38455 :
    checkMaskFor missing38455 StrongPackedBucketN12A4Shard300.record38455 = true := by
  decide

def missing38456 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 506092835456450560
theorem maskCheck38456 :
    checkMaskFor missing38456 StrongPackedBucketN12A4Shard300.record38456 = true := by
  decide

def missing38457 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 794323211608162304
theorem maskCheck38457 :
    checkMaskFor missing38457 StrongPackedBucketN12A4Shard300.record38457 = true := by
  decide

def missing38458 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1767100731120189440
theorem maskCheck38458 :
    checkMaskFor missing38458 StrongPackedBucketN12A4Shard300.record38458 = true := by
  decide

def missing38459 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2920022235727036416
theorem maskCheck38459 :
    checkMaskFor missing38459 StrongPackedBucketN12A4Shard300.record38459 = true := by
  decide

def missing38460 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4829548477732126720
theorem maskCheck38460 :
    checkMaskFor missing38460 StrongPackedBucketN12A4Shard300.record38460 = true := by
  decide

def missing38461 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4937634868789018624
theorem maskCheck38461 :
    checkMaskFor missing38461 StrongPackedBucketN12A4Shard300.record38461 = true := by
  decide

def missing38462 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4973663665807982592
theorem maskCheck38462 :
    checkMaskFor missing38462 StrongPackedBucketN12A4Shard300.record38462 = true := by
  decide

def missing38463 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5478066824073478144
theorem maskCheck38463 :
    checkMaskFor missing38463 StrongPackedBucketN12A4Shard300.record38463 = true := by
  decide

def missing38464 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37003264215666950144
theorem maskCheck38464 :
    checkMaskFor missing38464 StrongPackedBucketN12A4Shard300.record38464 = true := by
  decide

def missing38465 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37111350606723842048
theorem maskCheck38465 :
    checkMaskFor missing38465 StrongPackedBucketN12A4Shard300.record38465 = true := by
  decide

def missing38466 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37507667373932445696
theorem maskCheck38466 :
    checkMaskFor missing38466 StrongPackedBucketN12A4Shard300.record38466 = true := by
  decide

def missing38467 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37543696170951409664
theorem maskCheck38467 :
    checkMaskFor missing38467 StrongPackedBucketN12A4Shard300.record38467 = true := by
  decide

def missing38468 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38624560081520328704
theorem maskCheck38468 :
    checkMaskFor missing38468 StrongPackedBucketN12A4Shard300.record38468 = true := by
  decide

def missing38469 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39237049630842716160
theorem maskCheck38469 :
    checkMaskFor missing38469 StrongPackedBucketN12A4Shard300.record38469 = true := by
  decide

def missing38470 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41578921437075374080
theorem maskCheck38470 :
    checkMaskFor missing38470 StrongPackedBucketN12A4Shard300.record38470 = true := by
  decide

def missing38471 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41795094219189157888
theorem maskCheck38471 :
    checkMaskFor missing38471 StrongPackedBucketN12A4Shard300.record38471 = true := by
  decide

def missing38472 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 253469387456020480
theorem maskCheck38472 :
    checkMaskFor missing38472 StrongPackedBucketN12A4Shard300.record38472 = true := by
  decide

def missing38473 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 397584575531876352
theorem maskCheck38473 :
    checkMaskFor missing38473 StrongPackedBucketN12A4Shard300.record38473 = true := by
  decide

def missing38474 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 469642169569804288
theorem maskCheck38474 :
    checkMaskFor missing38474 StrongPackedBucketN12A4Shard300.record38474 = true := by
  decide

def missing38475 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 505670966588768256
theorem maskCheck38475 :
    checkMaskFor missing38475 StrongPackedBucketN12A4Shard300.record38475 = true := by
  decide

def missing38476 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 685814951683588096
theorem maskCheck38476 :
    checkMaskFor missing38476 StrongPackedBucketN12A4Shard300.record38476 = true := by
  decide

def missing38477 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 793901342740480000
theorem maskCheck38477 :
    checkMaskFor missing38477 StrongPackedBucketN12A4Shard300.record38477 = true := by
  decide

def missing38478 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 901987733797371904
theorem maskCheck38478 :
    checkMaskFor missing38478 StrongPackedBucketN12A4Shard300.record38478 = true := by
  decide

def missing38479 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 938016530816335872
theorem maskCheck38479 :
    checkMaskFor missing38479 StrongPackedBucketN12A4Shard300.record38479 = true := by
  decide

def missing38480 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1010074124854263808
theorem maskCheck38480 :
    checkMaskFor missing38480 StrongPackedBucketN12A4Shard300.record38480 = true := by
  decide

def missing38481 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1478448486100795392
theorem maskCheck38481 :
    checkMaskFor missing38481 StrongPackedBucketN12A4Shard300.record38481 = true := by
  decide

def missing38482 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1514477283119759360
theorem maskCheck38482 :
    checkMaskFor missing38482 StrongPackedBucketN12A4Shard300.record38482 = true := by
  decide

def missing38483 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2018880441385254912
theorem maskCheck38483 :
    checkMaskFor missing38483 StrongPackedBucketN12A4Shard300.record38483 = true := by
  decide

def missing38484 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2415197208593858560
theorem maskCheck38484 :
    checkMaskFor missing38484 StrongPackedBucketN12A4Shard300.record38484 = true := by
  decide

def missing38485 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2919600366859354112
theorem maskCheck38485 :
    checkMaskFor missing38485 StrongPackedBucketN12A4Shard300.record38485 = true := by
  decide

def missing38486 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2955629163878318080
theorem maskCheck38486 :
    checkMaskFor missing38486 StrongPackedBucketN12A4Shard300.record38486 = true := by
  decide

def missing38487 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3171801945992101888
theorem maskCheck38487 :
    checkMaskFor missing38487 StrongPackedBucketN12A4Shard300.record38487 = true := by
  decide

def missing38488 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4721040217807552512
theorem maskCheck38488 :
    checkMaskFor missing38488 StrongPackedBucketN12A4Shard300.record38488 = true := by
  decide

def missing38489 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4829126608864444416
theorem maskCheck38489 :
    checkMaskFor missing38489 StrongPackedBucketN12A4Shard300.record38489 = true := by
  decide

def missing38490 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4937212999921336320
theorem maskCheck38490 :
    checkMaskFor missing38490 StrongPackedBucketN12A4Shard300.record38490 = true := by
  decide

def missing38491 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5045299390978228224
theorem maskCheck38491 :
    checkMaskFor missing38491 StrongPackedBucketN12A4Shard300.record38491 = true := by
  decide

def missing38492 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5225443376073048064
theorem maskCheck38492 :
    checkMaskFor missing38492 StrongPackedBucketN12A4Shard300.record38492 = true := by
  decide

def missing38493 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5261472173092012032
theorem maskCheck38493 :
    checkMaskFor missing38493 StrongPackedBucketN12A4Shard300.record38493 = true := by
  decide

def missing38494 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5477644955205795840
theorem maskCheck38494 :
    checkMaskFor missing38494 StrongPackedBucketN12A4Shard300.record38494 = true := by
  decide

def missing38495 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6054105707509219328
theorem maskCheck38495 :
    checkMaskFor missing38495 StrongPackedBucketN12A4Shard300.record38495 = true := by
  decide

def missing38496 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6954825632983318528
theorem maskCheck38496 :
    checkMaskFor missing38496 StrongPackedBucketN12A4Shard300.record38496 = true := by
  decide

def missing38497 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7495257588267778048
theorem maskCheck38497 :
    checkMaskFor missing38497 StrongPackedBucketN12A4Shard300.record38497 = true := by
  decide

def missing38498 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9332726236234940416
theorem maskCheck38498 :
    checkMaskFor missing38498 StrongPackedBucketN12A4Shard300.record38498 = true := by
  decide

def missing38499 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9404783830272868352
theorem maskCheck38499 :
    checkMaskFor missing38499 StrongPackedBucketN12A4Shard300.record38499 = true := by
  decide

def missing38500 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9440812627291832320
theorem maskCheck38500 :
    checkMaskFor missing38500 StrongPackedBucketN12A4Shard300.record38500 = true := by
  decide

def missing38501 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9548899018348724224
theorem maskCheck38501 :
    checkMaskFor missing38501 StrongPackedBucketN12A4Shard300.record38501 = true := by
  decide

def missing38502 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9656985409405616128
theorem maskCheck38502 :
    checkMaskFor missing38502 StrongPackedBucketN12A4Shard300.record38502 = true := by
  decide

def missing38503 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9837129394500435968
theorem maskCheck38503 :
    checkMaskFor missing38503 StrongPackedBucketN12A4Shard300.record38503 = true := by
  decide

def missing38504 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9873158191519399936
theorem maskCheck38504 :
    checkMaskFor missing38504 StrongPackedBucketN12A4Shard300.record38504 = true := by
  decide

def missing38505 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9945215785557327872
theorem maskCheck38505 :
    checkMaskFor missing38505 StrongPackedBucketN12A4Shard300.record38505 = true := by
  decide

def missing38506 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10413590146803859456
theorem maskCheck38506 :
    checkMaskFor missing38506 StrongPackedBucketN12A4Shard300.record38506 = true := by
  decide

def missing38507 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10449618943822823424
theorem maskCheck38507 :
    checkMaskFor missing38507 StrongPackedBucketN12A4Shard300.record38507 = true := by
  decide

def missing38508 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10521676537860751360
theorem maskCheck38508 :
    checkMaskFor missing38508 StrongPackedBucketN12A4Shard300.record38508 = true := by
  decide

def missing38509 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10665791725936607232
theorem maskCheck38509 :
    checkMaskFor missing38509 StrongPackedBucketN12A4Shard300.record38509 = true := by
  decide

def missing38510 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10954022102088318976
theorem maskCheck38510 :
    checkMaskFor missing38510 StrongPackedBucketN12A4Shard300.record38510 = true := by
  decide

def missing38511 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11566511651410706432
theorem maskCheck38511 :
    checkMaskFor missing38511 StrongPackedBucketN12A4Shard300.record38511 = true := by
  decide

def missing38512 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12106943606695165952
theorem maskCheck38512 :
    checkMaskFor missing38512 StrongPackedBucketN12A4Shard300.record38512 = true := by
  decide

def missing38513 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13872354660624400384
theorem maskCheck38513 :
    checkMaskFor missing38513 StrongPackedBucketN12A4Shard300.record38513 = true := by
  decide

def missing38514 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13908383457643364352
theorem maskCheck38514 :
    checkMaskFor missing38514 StrongPackedBucketN12A4Shard300.record38514 = true := by
  decide

def missing38515 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13980441051681292288
theorem maskCheck38515 :
    checkMaskFor missing38515 StrongPackedBucketN12A4Shard300.record38515 = true := by
  decide

def missing38516 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14124556239757148160
theorem maskCheck38516 :
    checkMaskFor missing38516 StrongPackedBucketN12A4Shard300.record38516 = true := by
  decide

def missing38517 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14412786615908859904
theorem maskCheck38517 :
    checkMaskFor missing38517 StrongPackedBucketN12A4Shard300.record38517 = true := by
  decide

def missing38518 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14989247368212283392
theorem maskCheck38518 :
    checkMaskFor missing38518 StrongPackedBucketN12A4Shard300.record38518 = true := by
  decide

def missing38519 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18556098273089716224
theorem maskCheck38519 :
    checkMaskFor missing38519 StrongPackedBucketN12A4Shard300.record38519 = true := by
  decide

def missing38520 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18772271055203500032
theorem maskCheck38520 :
    checkMaskFor missing38520 StrongPackedBucketN12A4Shard300.record38520 = true := by
  decide

def missing38521 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23095726697479176192
theorem maskCheck38521 :
    checkMaskFor missing38521 StrongPackedBucketN12A4Shard300.record38521 = true := by
  decide

def missing38522 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27707412715906564096
theorem maskCheck38522 :
    checkMaskFor missing38522 StrongPackedBucketN12A4Shard300.record38522 = true := by
  decide

def missing38523 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46154156789616115712
theorem maskCheck38523 :
    checkMaskFor missing38523 StrongPackedBucketN12A4Shard300.record38523 = true := by
  decide

def missing38524 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46190185586635079680
theorem maskCheck38524 :
    checkMaskFor missing38524 StrongPackedBucketN12A4Shard300.record38524 = true := by
  decide

def missing38525 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46406358368748863488
theorem maskCheck38525 :
    checkMaskFor missing38525 StrongPackedBucketN12A4Shard300.record38525 = true := by
  decide

def missing38526 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46694588744900575232
theorem maskCheck38526 :
    checkMaskFor missing38526 StrongPackedBucketN12A4Shard300.record38526 = true := by
  decide

def missing38527 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50729814011024539648
theorem maskCheck38527 :
    checkMaskFor missing38527 StrongPackedBucketN12A4Shard300.record38527 = true := by
  decide

def missing38400_38401 : List (BitVec (edgeCount 12)) :=
  [missing38400]
abbrev records38400_38401 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38400]
theorem aligned38400_38401 :
    AlignedValid 12 4 missing38400_38401 records38400_38401 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38400
    maskCheck38400 AlignedValid.nil

def missing38401_38402 : List (BitVec (edgeCount 12)) :=
  [missing38401]
abbrev records38401_38402 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38401]
theorem aligned38401_38402 :
    AlignedValid 12 4 missing38401_38402 records38401_38402 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38401
    maskCheck38401 AlignedValid.nil

def missing38400_38402 : List (BitVec (edgeCount 12)) :=
  missing38400_38401 ++ missing38401_38402
abbrev records38400_38402 : List Blob :=
  records38400_38401 ++ records38401_38402
theorem aligned38400_38402 :
    AlignedValid 12 4 missing38400_38402 records38400_38402 :=
  aligned38400_38401.append aligned38401_38402

def missing38402_38403 : List (BitVec (edgeCount 12)) :=
  [missing38402]
abbrev records38402_38403 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38402]
theorem aligned38402_38403 :
    AlignedValid 12 4 missing38402_38403 records38402_38403 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38402
    maskCheck38402 AlignedValid.nil

def missing38403_38404 : List (BitVec (edgeCount 12)) :=
  [missing38403]
abbrev records38403_38404 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38403]
theorem aligned38403_38404 :
    AlignedValid 12 4 missing38403_38404 records38403_38404 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38403
    maskCheck38403 AlignedValid.nil

def missing38402_38404 : List (BitVec (edgeCount 12)) :=
  missing38402_38403 ++ missing38403_38404
abbrev records38402_38404 : List Blob :=
  records38402_38403 ++ records38403_38404
theorem aligned38402_38404 :
    AlignedValid 12 4 missing38402_38404 records38402_38404 :=
  aligned38402_38403.append aligned38403_38404

def missing38400_38404 : List (BitVec (edgeCount 12)) :=
  missing38400_38402 ++ missing38402_38404
abbrev records38400_38404 : List Blob :=
  records38400_38402 ++ records38402_38404
theorem aligned38400_38404 :
    AlignedValid 12 4 missing38400_38404 records38400_38404 :=
  aligned38400_38402.append aligned38402_38404

def missing38404_38405 : List (BitVec (edgeCount 12)) :=
  [missing38404]
abbrev records38404_38405 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38404]
theorem aligned38404_38405 :
    AlignedValid 12 4 missing38404_38405 records38404_38405 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38404
    maskCheck38404 AlignedValid.nil

def missing38405_38406 : List (BitVec (edgeCount 12)) :=
  [missing38405]
abbrev records38405_38406 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38405]
theorem aligned38405_38406 :
    AlignedValid 12 4 missing38405_38406 records38405_38406 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38405
    maskCheck38405 AlignedValid.nil

def missing38404_38406 : List (BitVec (edgeCount 12)) :=
  missing38404_38405 ++ missing38405_38406
abbrev records38404_38406 : List Blob :=
  records38404_38405 ++ records38405_38406
theorem aligned38404_38406 :
    AlignedValid 12 4 missing38404_38406 records38404_38406 :=
  aligned38404_38405.append aligned38405_38406

def missing38406_38407 : List (BitVec (edgeCount 12)) :=
  [missing38406]
abbrev records38406_38407 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38406]
theorem aligned38406_38407 :
    AlignedValid 12 4 missing38406_38407 records38406_38407 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38406
    maskCheck38406 AlignedValid.nil

def missing38407_38408 : List (BitVec (edgeCount 12)) :=
  [missing38407]
abbrev records38407_38408 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38407]
theorem aligned38407_38408 :
    AlignedValid 12 4 missing38407_38408 records38407_38408 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38407
    maskCheck38407 AlignedValid.nil

def missing38406_38408 : List (BitVec (edgeCount 12)) :=
  missing38406_38407 ++ missing38407_38408
abbrev records38406_38408 : List Blob :=
  records38406_38407 ++ records38407_38408
theorem aligned38406_38408 :
    AlignedValid 12 4 missing38406_38408 records38406_38408 :=
  aligned38406_38407.append aligned38407_38408

def missing38404_38408 : List (BitVec (edgeCount 12)) :=
  missing38404_38406 ++ missing38406_38408
abbrev records38404_38408 : List Blob :=
  records38404_38406 ++ records38406_38408
theorem aligned38404_38408 :
    AlignedValid 12 4 missing38404_38408 records38404_38408 :=
  aligned38404_38406.append aligned38406_38408

def missing38400_38408 : List (BitVec (edgeCount 12)) :=
  missing38400_38404 ++ missing38404_38408
abbrev records38400_38408 : List Blob :=
  records38400_38404 ++ records38404_38408
theorem aligned38400_38408 :
    AlignedValid 12 4 missing38400_38408 records38400_38408 :=
  aligned38400_38404.append aligned38404_38408

def missing38408_38409 : List (BitVec (edgeCount 12)) :=
  [missing38408]
abbrev records38408_38409 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38408]
theorem aligned38408_38409 :
    AlignedValid 12 4 missing38408_38409 records38408_38409 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38408
    maskCheck38408 AlignedValid.nil

def missing38409_38410 : List (BitVec (edgeCount 12)) :=
  [missing38409]
abbrev records38409_38410 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38409]
theorem aligned38409_38410 :
    AlignedValid 12 4 missing38409_38410 records38409_38410 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38409
    maskCheck38409 AlignedValid.nil

def missing38408_38410 : List (BitVec (edgeCount 12)) :=
  missing38408_38409 ++ missing38409_38410
abbrev records38408_38410 : List Blob :=
  records38408_38409 ++ records38409_38410
theorem aligned38408_38410 :
    AlignedValid 12 4 missing38408_38410 records38408_38410 :=
  aligned38408_38409.append aligned38409_38410

def missing38410_38411 : List (BitVec (edgeCount 12)) :=
  [missing38410]
abbrev records38410_38411 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38410]
theorem aligned38410_38411 :
    AlignedValid 12 4 missing38410_38411 records38410_38411 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38410
    maskCheck38410 AlignedValid.nil

def missing38411_38412 : List (BitVec (edgeCount 12)) :=
  [missing38411]
abbrev records38411_38412 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38411]
theorem aligned38411_38412 :
    AlignedValid 12 4 missing38411_38412 records38411_38412 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38411
    maskCheck38411 AlignedValid.nil

def missing38410_38412 : List (BitVec (edgeCount 12)) :=
  missing38410_38411 ++ missing38411_38412
abbrev records38410_38412 : List Blob :=
  records38410_38411 ++ records38411_38412
theorem aligned38410_38412 :
    AlignedValid 12 4 missing38410_38412 records38410_38412 :=
  aligned38410_38411.append aligned38411_38412

def missing38408_38412 : List (BitVec (edgeCount 12)) :=
  missing38408_38410 ++ missing38410_38412
abbrev records38408_38412 : List Blob :=
  records38408_38410 ++ records38410_38412
theorem aligned38408_38412 :
    AlignedValid 12 4 missing38408_38412 records38408_38412 :=
  aligned38408_38410.append aligned38410_38412

def missing38412_38413 : List (BitVec (edgeCount 12)) :=
  [missing38412]
abbrev records38412_38413 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38412]
theorem aligned38412_38413 :
    AlignedValid 12 4 missing38412_38413 records38412_38413 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38412
    maskCheck38412 AlignedValid.nil

def missing38413_38414 : List (BitVec (edgeCount 12)) :=
  [missing38413]
abbrev records38413_38414 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38413]
theorem aligned38413_38414 :
    AlignedValid 12 4 missing38413_38414 records38413_38414 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38413
    maskCheck38413 AlignedValid.nil

def missing38412_38414 : List (BitVec (edgeCount 12)) :=
  missing38412_38413 ++ missing38413_38414
abbrev records38412_38414 : List Blob :=
  records38412_38413 ++ records38413_38414
theorem aligned38412_38414 :
    AlignedValid 12 4 missing38412_38414 records38412_38414 :=
  aligned38412_38413.append aligned38413_38414

def missing38414_38415 : List (BitVec (edgeCount 12)) :=
  [missing38414]
abbrev records38414_38415 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38414]
theorem aligned38414_38415 :
    AlignedValid 12 4 missing38414_38415 records38414_38415 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38414
    maskCheck38414 AlignedValid.nil

def missing38415_38416 : List (BitVec (edgeCount 12)) :=
  [missing38415]
abbrev records38415_38416 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38415]
theorem aligned38415_38416 :
    AlignedValid 12 4 missing38415_38416 records38415_38416 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38415
    maskCheck38415 AlignedValid.nil

def missing38414_38416 : List (BitVec (edgeCount 12)) :=
  missing38414_38415 ++ missing38415_38416
abbrev records38414_38416 : List Blob :=
  records38414_38415 ++ records38415_38416
theorem aligned38414_38416 :
    AlignedValid 12 4 missing38414_38416 records38414_38416 :=
  aligned38414_38415.append aligned38415_38416

def missing38412_38416 : List (BitVec (edgeCount 12)) :=
  missing38412_38414 ++ missing38414_38416
abbrev records38412_38416 : List Blob :=
  records38412_38414 ++ records38414_38416
theorem aligned38412_38416 :
    AlignedValid 12 4 missing38412_38416 records38412_38416 :=
  aligned38412_38414.append aligned38414_38416

def missing38408_38416 : List (BitVec (edgeCount 12)) :=
  missing38408_38412 ++ missing38412_38416
abbrev records38408_38416 : List Blob :=
  records38408_38412 ++ records38412_38416
theorem aligned38408_38416 :
    AlignedValid 12 4 missing38408_38416 records38408_38416 :=
  aligned38408_38412.append aligned38412_38416

def missing38400_38416 : List (BitVec (edgeCount 12)) :=
  missing38400_38408 ++ missing38408_38416
abbrev records38400_38416 : List Blob :=
  records38400_38408 ++ records38408_38416
theorem aligned38400_38416 :
    AlignedValid 12 4 missing38400_38416 records38400_38416 :=
  aligned38400_38408.append aligned38408_38416

def missing38416_38417 : List (BitVec (edgeCount 12)) :=
  [missing38416]
abbrev records38416_38417 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38416]
theorem aligned38416_38417 :
    AlignedValid 12 4 missing38416_38417 records38416_38417 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38416
    maskCheck38416 AlignedValid.nil

def missing38417_38418 : List (BitVec (edgeCount 12)) :=
  [missing38417]
abbrev records38417_38418 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38417]
theorem aligned38417_38418 :
    AlignedValid 12 4 missing38417_38418 records38417_38418 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38417
    maskCheck38417 AlignedValid.nil

def missing38416_38418 : List (BitVec (edgeCount 12)) :=
  missing38416_38417 ++ missing38417_38418
abbrev records38416_38418 : List Blob :=
  records38416_38417 ++ records38417_38418
theorem aligned38416_38418 :
    AlignedValid 12 4 missing38416_38418 records38416_38418 :=
  aligned38416_38417.append aligned38417_38418

def missing38418_38419 : List (BitVec (edgeCount 12)) :=
  [missing38418]
abbrev records38418_38419 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38418]
theorem aligned38418_38419 :
    AlignedValid 12 4 missing38418_38419 records38418_38419 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38418
    maskCheck38418 AlignedValid.nil

def missing38419_38420 : List (BitVec (edgeCount 12)) :=
  [missing38419]
abbrev records38419_38420 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38419]
theorem aligned38419_38420 :
    AlignedValid 12 4 missing38419_38420 records38419_38420 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38419
    maskCheck38419 AlignedValid.nil

def missing38418_38420 : List (BitVec (edgeCount 12)) :=
  missing38418_38419 ++ missing38419_38420
abbrev records38418_38420 : List Blob :=
  records38418_38419 ++ records38419_38420
theorem aligned38418_38420 :
    AlignedValid 12 4 missing38418_38420 records38418_38420 :=
  aligned38418_38419.append aligned38419_38420

def missing38416_38420 : List (BitVec (edgeCount 12)) :=
  missing38416_38418 ++ missing38418_38420
abbrev records38416_38420 : List Blob :=
  records38416_38418 ++ records38418_38420
theorem aligned38416_38420 :
    AlignedValid 12 4 missing38416_38420 records38416_38420 :=
  aligned38416_38418.append aligned38418_38420

def missing38420_38421 : List (BitVec (edgeCount 12)) :=
  [missing38420]
abbrev records38420_38421 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38420]
theorem aligned38420_38421 :
    AlignedValid 12 4 missing38420_38421 records38420_38421 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38420
    maskCheck38420 AlignedValid.nil

def missing38421_38422 : List (BitVec (edgeCount 12)) :=
  [missing38421]
abbrev records38421_38422 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38421]
theorem aligned38421_38422 :
    AlignedValid 12 4 missing38421_38422 records38421_38422 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38421
    maskCheck38421 AlignedValid.nil

def missing38420_38422 : List (BitVec (edgeCount 12)) :=
  missing38420_38421 ++ missing38421_38422
abbrev records38420_38422 : List Blob :=
  records38420_38421 ++ records38421_38422
theorem aligned38420_38422 :
    AlignedValid 12 4 missing38420_38422 records38420_38422 :=
  aligned38420_38421.append aligned38421_38422

def missing38422_38423 : List (BitVec (edgeCount 12)) :=
  [missing38422]
abbrev records38422_38423 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38422]
theorem aligned38422_38423 :
    AlignedValid 12 4 missing38422_38423 records38422_38423 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38422
    maskCheck38422 AlignedValid.nil

def missing38423_38424 : List (BitVec (edgeCount 12)) :=
  [missing38423]
abbrev records38423_38424 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38423]
theorem aligned38423_38424 :
    AlignedValid 12 4 missing38423_38424 records38423_38424 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38423
    maskCheck38423 AlignedValid.nil

def missing38422_38424 : List (BitVec (edgeCount 12)) :=
  missing38422_38423 ++ missing38423_38424
abbrev records38422_38424 : List Blob :=
  records38422_38423 ++ records38423_38424
theorem aligned38422_38424 :
    AlignedValid 12 4 missing38422_38424 records38422_38424 :=
  aligned38422_38423.append aligned38423_38424

def missing38420_38424 : List (BitVec (edgeCount 12)) :=
  missing38420_38422 ++ missing38422_38424
abbrev records38420_38424 : List Blob :=
  records38420_38422 ++ records38422_38424
theorem aligned38420_38424 :
    AlignedValid 12 4 missing38420_38424 records38420_38424 :=
  aligned38420_38422.append aligned38422_38424

def missing38416_38424 : List (BitVec (edgeCount 12)) :=
  missing38416_38420 ++ missing38420_38424
abbrev records38416_38424 : List Blob :=
  records38416_38420 ++ records38420_38424
theorem aligned38416_38424 :
    AlignedValid 12 4 missing38416_38424 records38416_38424 :=
  aligned38416_38420.append aligned38420_38424

def missing38424_38425 : List (BitVec (edgeCount 12)) :=
  [missing38424]
abbrev records38424_38425 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38424]
theorem aligned38424_38425 :
    AlignedValid 12 4 missing38424_38425 records38424_38425 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38424
    maskCheck38424 AlignedValid.nil

def missing38425_38426 : List (BitVec (edgeCount 12)) :=
  [missing38425]
abbrev records38425_38426 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38425]
theorem aligned38425_38426 :
    AlignedValid 12 4 missing38425_38426 records38425_38426 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38425
    maskCheck38425 AlignedValid.nil

def missing38424_38426 : List (BitVec (edgeCount 12)) :=
  missing38424_38425 ++ missing38425_38426
abbrev records38424_38426 : List Blob :=
  records38424_38425 ++ records38425_38426
theorem aligned38424_38426 :
    AlignedValid 12 4 missing38424_38426 records38424_38426 :=
  aligned38424_38425.append aligned38425_38426

def missing38426_38427 : List (BitVec (edgeCount 12)) :=
  [missing38426]
abbrev records38426_38427 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38426]
theorem aligned38426_38427 :
    AlignedValid 12 4 missing38426_38427 records38426_38427 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38426
    maskCheck38426 AlignedValid.nil

def missing38427_38428 : List (BitVec (edgeCount 12)) :=
  [missing38427]
abbrev records38427_38428 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38427]
theorem aligned38427_38428 :
    AlignedValid 12 4 missing38427_38428 records38427_38428 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38427
    maskCheck38427 AlignedValid.nil

def missing38426_38428 : List (BitVec (edgeCount 12)) :=
  missing38426_38427 ++ missing38427_38428
abbrev records38426_38428 : List Blob :=
  records38426_38427 ++ records38427_38428
theorem aligned38426_38428 :
    AlignedValid 12 4 missing38426_38428 records38426_38428 :=
  aligned38426_38427.append aligned38427_38428

def missing38424_38428 : List (BitVec (edgeCount 12)) :=
  missing38424_38426 ++ missing38426_38428
abbrev records38424_38428 : List Blob :=
  records38424_38426 ++ records38426_38428
theorem aligned38424_38428 :
    AlignedValid 12 4 missing38424_38428 records38424_38428 :=
  aligned38424_38426.append aligned38426_38428

def missing38428_38429 : List (BitVec (edgeCount 12)) :=
  [missing38428]
abbrev records38428_38429 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38428]
theorem aligned38428_38429 :
    AlignedValid 12 4 missing38428_38429 records38428_38429 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38428
    maskCheck38428 AlignedValid.nil

def missing38429_38430 : List (BitVec (edgeCount 12)) :=
  [missing38429]
abbrev records38429_38430 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38429]
theorem aligned38429_38430 :
    AlignedValid 12 4 missing38429_38430 records38429_38430 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38429
    maskCheck38429 AlignedValid.nil

def missing38428_38430 : List (BitVec (edgeCount 12)) :=
  missing38428_38429 ++ missing38429_38430
abbrev records38428_38430 : List Blob :=
  records38428_38429 ++ records38429_38430
theorem aligned38428_38430 :
    AlignedValid 12 4 missing38428_38430 records38428_38430 :=
  aligned38428_38429.append aligned38429_38430

def missing38430_38431 : List (BitVec (edgeCount 12)) :=
  [missing38430]
abbrev records38430_38431 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38430]
theorem aligned38430_38431 :
    AlignedValid 12 4 missing38430_38431 records38430_38431 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38430
    maskCheck38430 AlignedValid.nil

def missing38431_38432 : List (BitVec (edgeCount 12)) :=
  [missing38431]
abbrev records38431_38432 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38431]
theorem aligned38431_38432 :
    AlignedValid 12 4 missing38431_38432 records38431_38432 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38431
    maskCheck38431 AlignedValid.nil

def missing38430_38432 : List (BitVec (edgeCount 12)) :=
  missing38430_38431 ++ missing38431_38432
abbrev records38430_38432 : List Blob :=
  records38430_38431 ++ records38431_38432
theorem aligned38430_38432 :
    AlignedValid 12 4 missing38430_38432 records38430_38432 :=
  aligned38430_38431.append aligned38431_38432

def missing38428_38432 : List (BitVec (edgeCount 12)) :=
  missing38428_38430 ++ missing38430_38432
abbrev records38428_38432 : List Blob :=
  records38428_38430 ++ records38430_38432
theorem aligned38428_38432 :
    AlignedValid 12 4 missing38428_38432 records38428_38432 :=
  aligned38428_38430.append aligned38430_38432

def missing38424_38432 : List (BitVec (edgeCount 12)) :=
  missing38424_38428 ++ missing38428_38432
abbrev records38424_38432 : List Blob :=
  records38424_38428 ++ records38428_38432
theorem aligned38424_38432 :
    AlignedValid 12 4 missing38424_38432 records38424_38432 :=
  aligned38424_38428.append aligned38428_38432

def missing38416_38432 : List (BitVec (edgeCount 12)) :=
  missing38416_38424 ++ missing38424_38432
abbrev records38416_38432 : List Blob :=
  records38416_38424 ++ records38424_38432
theorem aligned38416_38432 :
    AlignedValid 12 4 missing38416_38432 records38416_38432 :=
  aligned38416_38424.append aligned38424_38432

def missing38400_38432 : List (BitVec (edgeCount 12)) :=
  missing38400_38416 ++ missing38416_38432
abbrev records38400_38432 : List Blob :=
  records38400_38416 ++ records38416_38432
theorem aligned38400_38432 :
    AlignedValid 12 4 missing38400_38432 records38400_38432 :=
  aligned38400_38416.append aligned38416_38432

def missing38432_38433 : List (BitVec (edgeCount 12)) :=
  [missing38432]
abbrev records38432_38433 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38432]
theorem aligned38432_38433 :
    AlignedValid 12 4 missing38432_38433 records38432_38433 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38432
    maskCheck38432 AlignedValid.nil

def missing38433_38434 : List (BitVec (edgeCount 12)) :=
  [missing38433]
abbrev records38433_38434 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38433]
theorem aligned38433_38434 :
    AlignedValid 12 4 missing38433_38434 records38433_38434 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38433
    maskCheck38433 AlignedValid.nil

def missing38432_38434 : List (BitVec (edgeCount 12)) :=
  missing38432_38433 ++ missing38433_38434
abbrev records38432_38434 : List Blob :=
  records38432_38433 ++ records38433_38434
theorem aligned38432_38434 :
    AlignedValid 12 4 missing38432_38434 records38432_38434 :=
  aligned38432_38433.append aligned38433_38434

def missing38434_38435 : List (BitVec (edgeCount 12)) :=
  [missing38434]
abbrev records38434_38435 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38434]
theorem aligned38434_38435 :
    AlignedValid 12 4 missing38434_38435 records38434_38435 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38434
    maskCheck38434 AlignedValid.nil

def missing38435_38436 : List (BitVec (edgeCount 12)) :=
  [missing38435]
abbrev records38435_38436 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38435]
theorem aligned38435_38436 :
    AlignedValid 12 4 missing38435_38436 records38435_38436 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38435
    maskCheck38435 AlignedValid.nil

def missing38434_38436 : List (BitVec (edgeCount 12)) :=
  missing38434_38435 ++ missing38435_38436
abbrev records38434_38436 : List Blob :=
  records38434_38435 ++ records38435_38436
theorem aligned38434_38436 :
    AlignedValid 12 4 missing38434_38436 records38434_38436 :=
  aligned38434_38435.append aligned38435_38436

def missing38432_38436 : List (BitVec (edgeCount 12)) :=
  missing38432_38434 ++ missing38434_38436
abbrev records38432_38436 : List Blob :=
  records38432_38434 ++ records38434_38436
theorem aligned38432_38436 :
    AlignedValid 12 4 missing38432_38436 records38432_38436 :=
  aligned38432_38434.append aligned38434_38436

def missing38436_38437 : List (BitVec (edgeCount 12)) :=
  [missing38436]
abbrev records38436_38437 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38436]
theorem aligned38436_38437 :
    AlignedValid 12 4 missing38436_38437 records38436_38437 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38436
    maskCheck38436 AlignedValid.nil

def missing38437_38438 : List (BitVec (edgeCount 12)) :=
  [missing38437]
abbrev records38437_38438 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38437]
theorem aligned38437_38438 :
    AlignedValid 12 4 missing38437_38438 records38437_38438 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38437
    maskCheck38437 AlignedValid.nil

def missing38436_38438 : List (BitVec (edgeCount 12)) :=
  missing38436_38437 ++ missing38437_38438
abbrev records38436_38438 : List Blob :=
  records38436_38437 ++ records38437_38438
theorem aligned38436_38438 :
    AlignedValid 12 4 missing38436_38438 records38436_38438 :=
  aligned38436_38437.append aligned38437_38438

def missing38438_38439 : List (BitVec (edgeCount 12)) :=
  [missing38438]
abbrev records38438_38439 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38438]
theorem aligned38438_38439 :
    AlignedValid 12 4 missing38438_38439 records38438_38439 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38438
    maskCheck38438 AlignedValid.nil

def missing38439_38440 : List (BitVec (edgeCount 12)) :=
  [missing38439]
abbrev records38439_38440 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38439]
theorem aligned38439_38440 :
    AlignedValid 12 4 missing38439_38440 records38439_38440 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38439
    maskCheck38439 AlignedValid.nil

def missing38438_38440 : List (BitVec (edgeCount 12)) :=
  missing38438_38439 ++ missing38439_38440
abbrev records38438_38440 : List Blob :=
  records38438_38439 ++ records38439_38440
theorem aligned38438_38440 :
    AlignedValid 12 4 missing38438_38440 records38438_38440 :=
  aligned38438_38439.append aligned38439_38440

def missing38436_38440 : List (BitVec (edgeCount 12)) :=
  missing38436_38438 ++ missing38438_38440
abbrev records38436_38440 : List Blob :=
  records38436_38438 ++ records38438_38440
theorem aligned38436_38440 :
    AlignedValid 12 4 missing38436_38440 records38436_38440 :=
  aligned38436_38438.append aligned38438_38440

def missing38432_38440 : List (BitVec (edgeCount 12)) :=
  missing38432_38436 ++ missing38436_38440
abbrev records38432_38440 : List Blob :=
  records38432_38436 ++ records38436_38440
theorem aligned38432_38440 :
    AlignedValid 12 4 missing38432_38440 records38432_38440 :=
  aligned38432_38436.append aligned38436_38440

def missing38440_38441 : List (BitVec (edgeCount 12)) :=
  [missing38440]
abbrev records38440_38441 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38440]
theorem aligned38440_38441 :
    AlignedValid 12 4 missing38440_38441 records38440_38441 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38440
    maskCheck38440 AlignedValid.nil

def missing38441_38442 : List (BitVec (edgeCount 12)) :=
  [missing38441]
abbrev records38441_38442 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38441]
theorem aligned38441_38442 :
    AlignedValid 12 4 missing38441_38442 records38441_38442 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38441
    maskCheck38441 AlignedValid.nil

def missing38440_38442 : List (BitVec (edgeCount 12)) :=
  missing38440_38441 ++ missing38441_38442
abbrev records38440_38442 : List Blob :=
  records38440_38441 ++ records38441_38442
theorem aligned38440_38442 :
    AlignedValid 12 4 missing38440_38442 records38440_38442 :=
  aligned38440_38441.append aligned38441_38442

def missing38442_38443 : List (BitVec (edgeCount 12)) :=
  [missing38442]
abbrev records38442_38443 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38442]
theorem aligned38442_38443 :
    AlignedValid 12 4 missing38442_38443 records38442_38443 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38442
    maskCheck38442 AlignedValid.nil

def missing38443_38444 : List (BitVec (edgeCount 12)) :=
  [missing38443]
abbrev records38443_38444 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38443]
theorem aligned38443_38444 :
    AlignedValid 12 4 missing38443_38444 records38443_38444 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38443
    maskCheck38443 AlignedValid.nil

def missing38442_38444 : List (BitVec (edgeCount 12)) :=
  missing38442_38443 ++ missing38443_38444
abbrev records38442_38444 : List Blob :=
  records38442_38443 ++ records38443_38444
theorem aligned38442_38444 :
    AlignedValid 12 4 missing38442_38444 records38442_38444 :=
  aligned38442_38443.append aligned38443_38444

def missing38440_38444 : List (BitVec (edgeCount 12)) :=
  missing38440_38442 ++ missing38442_38444
abbrev records38440_38444 : List Blob :=
  records38440_38442 ++ records38442_38444
theorem aligned38440_38444 :
    AlignedValid 12 4 missing38440_38444 records38440_38444 :=
  aligned38440_38442.append aligned38442_38444

def missing38444_38445 : List (BitVec (edgeCount 12)) :=
  [missing38444]
abbrev records38444_38445 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38444]
theorem aligned38444_38445 :
    AlignedValid 12 4 missing38444_38445 records38444_38445 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38444
    maskCheck38444 AlignedValid.nil

def missing38445_38446 : List (BitVec (edgeCount 12)) :=
  [missing38445]
abbrev records38445_38446 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38445]
theorem aligned38445_38446 :
    AlignedValid 12 4 missing38445_38446 records38445_38446 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38445
    maskCheck38445 AlignedValid.nil

def missing38444_38446 : List (BitVec (edgeCount 12)) :=
  missing38444_38445 ++ missing38445_38446
abbrev records38444_38446 : List Blob :=
  records38444_38445 ++ records38445_38446
theorem aligned38444_38446 :
    AlignedValid 12 4 missing38444_38446 records38444_38446 :=
  aligned38444_38445.append aligned38445_38446

def missing38446_38447 : List (BitVec (edgeCount 12)) :=
  [missing38446]
abbrev records38446_38447 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38446]
theorem aligned38446_38447 :
    AlignedValid 12 4 missing38446_38447 records38446_38447 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38446
    maskCheck38446 AlignedValid.nil

def missing38447_38448 : List (BitVec (edgeCount 12)) :=
  [missing38447]
abbrev records38447_38448 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38447]
theorem aligned38447_38448 :
    AlignedValid 12 4 missing38447_38448 records38447_38448 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38447
    maskCheck38447 AlignedValid.nil

def missing38446_38448 : List (BitVec (edgeCount 12)) :=
  missing38446_38447 ++ missing38447_38448
abbrev records38446_38448 : List Blob :=
  records38446_38447 ++ records38447_38448
theorem aligned38446_38448 :
    AlignedValid 12 4 missing38446_38448 records38446_38448 :=
  aligned38446_38447.append aligned38447_38448

def missing38444_38448 : List (BitVec (edgeCount 12)) :=
  missing38444_38446 ++ missing38446_38448
abbrev records38444_38448 : List Blob :=
  records38444_38446 ++ records38446_38448
theorem aligned38444_38448 :
    AlignedValid 12 4 missing38444_38448 records38444_38448 :=
  aligned38444_38446.append aligned38446_38448

def missing38440_38448 : List (BitVec (edgeCount 12)) :=
  missing38440_38444 ++ missing38444_38448
abbrev records38440_38448 : List Blob :=
  records38440_38444 ++ records38444_38448
theorem aligned38440_38448 :
    AlignedValid 12 4 missing38440_38448 records38440_38448 :=
  aligned38440_38444.append aligned38444_38448

def missing38432_38448 : List (BitVec (edgeCount 12)) :=
  missing38432_38440 ++ missing38440_38448
abbrev records38432_38448 : List Blob :=
  records38432_38440 ++ records38440_38448
theorem aligned38432_38448 :
    AlignedValid 12 4 missing38432_38448 records38432_38448 :=
  aligned38432_38440.append aligned38440_38448

def missing38448_38449 : List (BitVec (edgeCount 12)) :=
  [missing38448]
abbrev records38448_38449 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38448]
theorem aligned38448_38449 :
    AlignedValid 12 4 missing38448_38449 records38448_38449 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38448
    maskCheck38448 AlignedValid.nil

def missing38449_38450 : List (BitVec (edgeCount 12)) :=
  [missing38449]
abbrev records38449_38450 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38449]
theorem aligned38449_38450 :
    AlignedValid 12 4 missing38449_38450 records38449_38450 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38449
    maskCheck38449 AlignedValid.nil

def missing38448_38450 : List (BitVec (edgeCount 12)) :=
  missing38448_38449 ++ missing38449_38450
abbrev records38448_38450 : List Blob :=
  records38448_38449 ++ records38449_38450
theorem aligned38448_38450 :
    AlignedValid 12 4 missing38448_38450 records38448_38450 :=
  aligned38448_38449.append aligned38449_38450

def missing38450_38451 : List (BitVec (edgeCount 12)) :=
  [missing38450]
abbrev records38450_38451 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38450]
theorem aligned38450_38451 :
    AlignedValid 12 4 missing38450_38451 records38450_38451 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38450
    maskCheck38450 AlignedValid.nil

def missing38451_38452 : List (BitVec (edgeCount 12)) :=
  [missing38451]
abbrev records38451_38452 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38451]
theorem aligned38451_38452 :
    AlignedValid 12 4 missing38451_38452 records38451_38452 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38451
    maskCheck38451 AlignedValid.nil

def missing38450_38452 : List (BitVec (edgeCount 12)) :=
  missing38450_38451 ++ missing38451_38452
abbrev records38450_38452 : List Blob :=
  records38450_38451 ++ records38451_38452
theorem aligned38450_38452 :
    AlignedValid 12 4 missing38450_38452 records38450_38452 :=
  aligned38450_38451.append aligned38451_38452

def missing38448_38452 : List (BitVec (edgeCount 12)) :=
  missing38448_38450 ++ missing38450_38452
abbrev records38448_38452 : List Blob :=
  records38448_38450 ++ records38450_38452
theorem aligned38448_38452 :
    AlignedValid 12 4 missing38448_38452 records38448_38452 :=
  aligned38448_38450.append aligned38450_38452

def missing38452_38453 : List (BitVec (edgeCount 12)) :=
  [missing38452]
abbrev records38452_38453 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38452]
theorem aligned38452_38453 :
    AlignedValid 12 4 missing38452_38453 records38452_38453 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38452
    maskCheck38452 AlignedValid.nil

def missing38453_38454 : List (BitVec (edgeCount 12)) :=
  [missing38453]
abbrev records38453_38454 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38453]
theorem aligned38453_38454 :
    AlignedValid 12 4 missing38453_38454 records38453_38454 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38453
    maskCheck38453 AlignedValid.nil

def missing38452_38454 : List (BitVec (edgeCount 12)) :=
  missing38452_38453 ++ missing38453_38454
abbrev records38452_38454 : List Blob :=
  records38452_38453 ++ records38453_38454
theorem aligned38452_38454 :
    AlignedValid 12 4 missing38452_38454 records38452_38454 :=
  aligned38452_38453.append aligned38453_38454

def missing38454_38455 : List (BitVec (edgeCount 12)) :=
  [missing38454]
abbrev records38454_38455 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38454]
theorem aligned38454_38455 :
    AlignedValid 12 4 missing38454_38455 records38454_38455 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38454
    maskCheck38454 AlignedValid.nil

def missing38455_38456 : List (BitVec (edgeCount 12)) :=
  [missing38455]
abbrev records38455_38456 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38455]
theorem aligned38455_38456 :
    AlignedValid 12 4 missing38455_38456 records38455_38456 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38455
    maskCheck38455 AlignedValid.nil

def missing38454_38456 : List (BitVec (edgeCount 12)) :=
  missing38454_38455 ++ missing38455_38456
abbrev records38454_38456 : List Blob :=
  records38454_38455 ++ records38455_38456
theorem aligned38454_38456 :
    AlignedValid 12 4 missing38454_38456 records38454_38456 :=
  aligned38454_38455.append aligned38455_38456

def missing38452_38456 : List (BitVec (edgeCount 12)) :=
  missing38452_38454 ++ missing38454_38456
abbrev records38452_38456 : List Blob :=
  records38452_38454 ++ records38454_38456
theorem aligned38452_38456 :
    AlignedValid 12 4 missing38452_38456 records38452_38456 :=
  aligned38452_38454.append aligned38454_38456

def missing38448_38456 : List (BitVec (edgeCount 12)) :=
  missing38448_38452 ++ missing38452_38456
abbrev records38448_38456 : List Blob :=
  records38448_38452 ++ records38452_38456
theorem aligned38448_38456 :
    AlignedValid 12 4 missing38448_38456 records38448_38456 :=
  aligned38448_38452.append aligned38452_38456

def missing38456_38457 : List (BitVec (edgeCount 12)) :=
  [missing38456]
abbrev records38456_38457 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38456]
theorem aligned38456_38457 :
    AlignedValid 12 4 missing38456_38457 records38456_38457 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38456
    maskCheck38456 AlignedValid.nil

def missing38457_38458 : List (BitVec (edgeCount 12)) :=
  [missing38457]
abbrev records38457_38458 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38457]
theorem aligned38457_38458 :
    AlignedValid 12 4 missing38457_38458 records38457_38458 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38457
    maskCheck38457 AlignedValid.nil

def missing38456_38458 : List (BitVec (edgeCount 12)) :=
  missing38456_38457 ++ missing38457_38458
abbrev records38456_38458 : List Blob :=
  records38456_38457 ++ records38457_38458
theorem aligned38456_38458 :
    AlignedValid 12 4 missing38456_38458 records38456_38458 :=
  aligned38456_38457.append aligned38457_38458

def missing38458_38459 : List (BitVec (edgeCount 12)) :=
  [missing38458]
abbrev records38458_38459 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38458]
theorem aligned38458_38459 :
    AlignedValid 12 4 missing38458_38459 records38458_38459 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38458
    maskCheck38458 AlignedValid.nil

def missing38459_38460 : List (BitVec (edgeCount 12)) :=
  [missing38459]
abbrev records38459_38460 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38459]
theorem aligned38459_38460 :
    AlignedValid 12 4 missing38459_38460 records38459_38460 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38459
    maskCheck38459 AlignedValid.nil

def missing38458_38460 : List (BitVec (edgeCount 12)) :=
  missing38458_38459 ++ missing38459_38460
abbrev records38458_38460 : List Blob :=
  records38458_38459 ++ records38459_38460
theorem aligned38458_38460 :
    AlignedValid 12 4 missing38458_38460 records38458_38460 :=
  aligned38458_38459.append aligned38459_38460

def missing38456_38460 : List (BitVec (edgeCount 12)) :=
  missing38456_38458 ++ missing38458_38460
abbrev records38456_38460 : List Blob :=
  records38456_38458 ++ records38458_38460
theorem aligned38456_38460 :
    AlignedValid 12 4 missing38456_38460 records38456_38460 :=
  aligned38456_38458.append aligned38458_38460

def missing38460_38461 : List (BitVec (edgeCount 12)) :=
  [missing38460]
abbrev records38460_38461 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38460]
theorem aligned38460_38461 :
    AlignedValid 12 4 missing38460_38461 records38460_38461 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38460
    maskCheck38460 AlignedValid.nil

def missing38461_38462 : List (BitVec (edgeCount 12)) :=
  [missing38461]
abbrev records38461_38462 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38461]
theorem aligned38461_38462 :
    AlignedValid 12 4 missing38461_38462 records38461_38462 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38461
    maskCheck38461 AlignedValid.nil

def missing38460_38462 : List (BitVec (edgeCount 12)) :=
  missing38460_38461 ++ missing38461_38462
abbrev records38460_38462 : List Blob :=
  records38460_38461 ++ records38461_38462
theorem aligned38460_38462 :
    AlignedValid 12 4 missing38460_38462 records38460_38462 :=
  aligned38460_38461.append aligned38461_38462

def missing38462_38463 : List (BitVec (edgeCount 12)) :=
  [missing38462]
abbrev records38462_38463 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38462]
theorem aligned38462_38463 :
    AlignedValid 12 4 missing38462_38463 records38462_38463 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38462
    maskCheck38462 AlignedValid.nil

def missing38463_38464 : List (BitVec (edgeCount 12)) :=
  [missing38463]
abbrev records38463_38464 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38463]
theorem aligned38463_38464 :
    AlignedValid 12 4 missing38463_38464 records38463_38464 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38463
    maskCheck38463 AlignedValid.nil

def missing38462_38464 : List (BitVec (edgeCount 12)) :=
  missing38462_38463 ++ missing38463_38464
abbrev records38462_38464 : List Blob :=
  records38462_38463 ++ records38463_38464
theorem aligned38462_38464 :
    AlignedValid 12 4 missing38462_38464 records38462_38464 :=
  aligned38462_38463.append aligned38463_38464

def missing38460_38464 : List (BitVec (edgeCount 12)) :=
  missing38460_38462 ++ missing38462_38464
abbrev records38460_38464 : List Blob :=
  records38460_38462 ++ records38462_38464
theorem aligned38460_38464 :
    AlignedValid 12 4 missing38460_38464 records38460_38464 :=
  aligned38460_38462.append aligned38462_38464

def missing38456_38464 : List (BitVec (edgeCount 12)) :=
  missing38456_38460 ++ missing38460_38464
abbrev records38456_38464 : List Blob :=
  records38456_38460 ++ records38460_38464
theorem aligned38456_38464 :
    AlignedValid 12 4 missing38456_38464 records38456_38464 :=
  aligned38456_38460.append aligned38460_38464

def missing38448_38464 : List (BitVec (edgeCount 12)) :=
  missing38448_38456 ++ missing38456_38464
abbrev records38448_38464 : List Blob :=
  records38448_38456 ++ records38456_38464
theorem aligned38448_38464 :
    AlignedValid 12 4 missing38448_38464 records38448_38464 :=
  aligned38448_38456.append aligned38456_38464

def missing38432_38464 : List (BitVec (edgeCount 12)) :=
  missing38432_38448 ++ missing38448_38464
abbrev records38432_38464 : List Blob :=
  records38432_38448 ++ records38448_38464
theorem aligned38432_38464 :
    AlignedValid 12 4 missing38432_38464 records38432_38464 :=
  aligned38432_38448.append aligned38448_38464

def missing38400_38464 : List (BitVec (edgeCount 12)) :=
  missing38400_38432 ++ missing38432_38464
abbrev records38400_38464 : List Blob :=
  records38400_38432 ++ records38432_38464
theorem aligned38400_38464 :
    AlignedValid 12 4 missing38400_38464 records38400_38464 :=
  aligned38400_38432.append aligned38432_38464

def missing38464_38465 : List (BitVec (edgeCount 12)) :=
  [missing38464]
abbrev records38464_38465 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38464]
theorem aligned38464_38465 :
    AlignedValid 12 4 missing38464_38465 records38464_38465 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38464
    maskCheck38464 AlignedValid.nil

def missing38465_38466 : List (BitVec (edgeCount 12)) :=
  [missing38465]
abbrev records38465_38466 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38465]
theorem aligned38465_38466 :
    AlignedValid 12 4 missing38465_38466 records38465_38466 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38465
    maskCheck38465 AlignedValid.nil

def missing38464_38466 : List (BitVec (edgeCount 12)) :=
  missing38464_38465 ++ missing38465_38466
abbrev records38464_38466 : List Blob :=
  records38464_38465 ++ records38465_38466
theorem aligned38464_38466 :
    AlignedValid 12 4 missing38464_38466 records38464_38466 :=
  aligned38464_38465.append aligned38465_38466

def missing38466_38467 : List (BitVec (edgeCount 12)) :=
  [missing38466]
abbrev records38466_38467 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38466]
theorem aligned38466_38467 :
    AlignedValid 12 4 missing38466_38467 records38466_38467 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38466
    maskCheck38466 AlignedValid.nil

def missing38467_38468 : List (BitVec (edgeCount 12)) :=
  [missing38467]
abbrev records38467_38468 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38467]
theorem aligned38467_38468 :
    AlignedValid 12 4 missing38467_38468 records38467_38468 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38467
    maskCheck38467 AlignedValid.nil

def missing38466_38468 : List (BitVec (edgeCount 12)) :=
  missing38466_38467 ++ missing38467_38468
abbrev records38466_38468 : List Blob :=
  records38466_38467 ++ records38467_38468
theorem aligned38466_38468 :
    AlignedValid 12 4 missing38466_38468 records38466_38468 :=
  aligned38466_38467.append aligned38467_38468

def missing38464_38468 : List (BitVec (edgeCount 12)) :=
  missing38464_38466 ++ missing38466_38468
abbrev records38464_38468 : List Blob :=
  records38464_38466 ++ records38466_38468
theorem aligned38464_38468 :
    AlignedValid 12 4 missing38464_38468 records38464_38468 :=
  aligned38464_38466.append aligned38466_38468

def missing38468_38469 : List (BitVec (edgeCount 12)) :=
  [missing38468]
abbrev records38468_38469 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38468]
theorem aligned38468_38469 :
    AlignedValid 12 4 missing38468_38469 records38468_38469 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38468
    maskCheck38468 AlignedValid.nil

def missing38469_38470 : List (BitVec (edgeCount 12)) :=
  [missing38469]
abbrev records38469_38470 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38469]
theorem aligned38469_38470 :
    AlignedValid 12 4 missing38469_38470 records38469_38470 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38469
    maskCheck38469 AlignedValid.nil

def missing38468_38470 : List (BitVec (edgeCount 12)) :=
  missing38468_38469 ++ missing38469_38470
abbrev records38468_38470 : List Blob :=
  records38468_38469 ++ records38469_38470
theorem aligned38468_38470 :
    AlignedValid 12 4 missing38468_38470 records38468_38470 :=
  aligned38468_38469.append aligned38469_38470

def missing38470_38471 : List (BitVec (edgeCount 12)) :=
  [missing38470]
abbrev records38470_38471 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38470]
theorem aligned38470_38471 :
    AlignedValid 12 4 missing38470_38471 records38470_38471 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38470
    maskCheck38470 AlignedValid.nil

def missing38471_38472 : List (BitVec (edgeCount 12)) :=
  [missing38471]
abbrev records38471_38472 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38471]
theorem aligned38471_38472 :
    AlignedValid 12 4 missing38471_38472 records38471_38472 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38471
    maskCheck38471 AlignedValid.nil

def missing38470_38472 : List (BitVec (edgeCount 12)) :=
  missing38470_38471 ++ missing38471_38472
abbrev records38470_38472 : List Blob :=
  records38470_38471 ++ records38471_38472
theorem aligned38470_38472 :
    AlignedValid 12 4 missing38470_38472 records38470_38472 :=
  aligned38470_38471.append aligned38471_38472

def missing38468_38472 : List (BitVec (edgeCount 12)) :=
  missing38468_38470 ++ missing38470_38472
abbrev records38468_38472 : List Blob :=
  records38468_38470 ++ records38470_38472
theorem aligned38468_38472 :
    AlignedValid 12 4 missing38468_38472 records38468_38472 :=
  aligned38468_38470.append aligned38470_38472

def missing38464_38472 : List (BitVec (edgeCount 12)) :=
  missing38464_38468 ++ missing38468_38472
abbrev records38464_38472 : List Blob :=
  records38464_38468 ++ records38468_38472
theorem aligned38464_38472 :
    AlignedValid 12 4 missing38464_38472 records38464_38472 :=
  aligned38464_38468.append aligned38468_38472

def missing38472_38473 : List (BitVec (edgeCount 12)) :=
  [missing38472]
abbrev records38472_38473 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38472]
theorem aligned38472_38473 :
    AlignedValid 12 4 missing38472_38473 records38472_38473 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38472
    maskCheck38472 AlignedValid.nil

def missing38473_38474 : List (BitVec (edgeCount 12)) :=
  [missing38473]
abbrev records38473_38474 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38473]
theorem aligned38473_38474 :
    AlignedValid 12 4 missing38473_38474 records38473_38474 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38473
    maskCheck38473 AlignedValid.nil

def missing38472_38474 : List (BitVec (edgeCount 12)) :=
  missing38472_38473 ++ missing38473_38474
abbrev records38472_38474 : List Blob :=
  records38472_38473 ++ records38473_38474
theorem aligned38472_38474 :
    AlignedValid 12 4 missing38472_38474 records38472_38474 :=
  aligned38472_38473.append aligned38473_38474

def missing38474_38475 : List (BitVec (edgeCount 12)) :=
  [missing38474]
abbrev records38474_38475 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38474]
theorem aligned38474_38475 :
    AlignedValid 12 4 missing38474_38475 records38474_38475 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38474
    maskCheck38474 AlignedValid.nil

def missing38475_38476 : List (BitVec (edgeCount 12)) :=
  [missing38475]
abbrev records38475_38476 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38475]
theorem aligned38475_38476 :
    AlignedValid 12 4 missing38475_38476 records38475_38476 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38475
    maskCheck38475 AlignedValid.nil

def missing38474_38476 : List (BitVec (edgeCount 12)) :=
  missing38474_38475 ++ missing38475_38476
abbrev records38474_38476 : List Blob :=
  records38474_38475 ++ records38475_38476
theorem aligned38474_38476 :
    AlignedValid 12 4 missing38474_38476 records38474_38476 :=
  aligned38474_38475.append aligned38475_38476

def missing38472_38476 : List (BitVec (edgeCount 12)) :=
  missing38472_38474 ++ missing38474_38476
abbrev records38472_38476 : List Blob :=
  records38472_38474 ++ records38474_38476
theorem aligned38472_38476 :
    AlignedValid 12 4 missing38472_38476 records38472_38476 :=
  aligned38472_38474.append aligned38474_38476

def missing38476_38477 : List (BitVec (edgeCount 12)) :=
  [missing38476]
abbrev records38476_38477 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38476]
theorem aligned38476_38477 :
    AlignedValid 12 4 missing38476_38477 records38476_38477 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38476
    maskCheck38476 AlignedValid.nil

def missing38477_38478 : List (BitVec (edgeCount 12)) :=
  [missing38477]
abbrev records38477_38478 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38477]
theorem aligned38477_38478 :
    AlignedValid 12 4 missing38477_38478 records38477_38478 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38477
    maskCheck38477 AlignedValid.nil

def missing38476_38478 : List (BitVec (edgeCount 12)) :=
  missing38476_38477 ++ missing38477_38478
abbrev records38476_38478 : List Blob :=
  records38476_38477 ++ records38477_38478
theorem aligned38476_38478 :
    AlignedValid 12 4 missing38476_38478 records38476_38478 :=
  aligned38476_38477.append aligned38477_38478

def missing38478_38479 : List (BitVec (edgeCount 12)) :=
  [missing38478]
abbrev records38478_38479 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38478]
theorem aligned38478_38479 :
    AlignedValid 12 4 missing38478_38479 records38478_38479 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38478
    maskCheck38478 AlignedValid.nil

def missing38479_38480 : List (BitVec (edgeCount 12)) :=
  [missing38479]
abbrev records38479_38480 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38479]
theorem aligned38479_38480 :
    AlignedValid 12 4 missing38479_38480 records38479_38480 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38479
    maskCheck38479 AlignedValid.nil

def missing38478_38480 : List (BitVec (edgeCount 12)) :=
  missing38478_38479 ++ missing38479_38480
abbrev records38478_38480 : List Blob :=
  records38478_38479 ++ records38479_38480
theorem aligned38478_38480 :
    AlignedValid 12 4 missing38478_38480 records38478_38480 :=
  aligned38478_38479.append aligned38479_38480

def missing38476_38480 : List (BitVec (edgeCount 12)) :=
  missing38476_38478 ++ missing38478_38480
abbrev records38476_38480 : List Blob :=
  records38476_38478 ++ records38478_38480
theorem aligned38476_38480 :
    AlignedValid 12 4 missing38476_38480 records38476_38480 :=
  aligned38476_38478.append aligned38478_38480

def missing38472_38480 : List (BitVec (edgeCount 12)) :=
  missing38472_38476 ++ missing38476_38480
abbrev records38472_38480 : List Blob :=
  records38472_38476 ++ records38476_38480
theorem aligned38472_38480 :
    AlignedValid 12 4 missing38472_38480 records38472_38480 :=
  aligned38472_38476.append aligned38476_38480

def missing38464_38480 : List (BitVec (edgeCount 12)) :=
  missing38464_38472 ++ missing38472_38480
abbrev records38464_38480 : List Blob :=
  records38464_38472 ++ records38472_38480
theorem aligned38464_38480 :
    AlignedValid 12 4 missing38464_38480 records38464_38480 :=
  aligned38464_38472.append aligned38472_38480

def missing38480_38481 : List (BitVec (edgeCount 12)) :=
  [missing38480]
abbrev records38480_38481 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38480]
theorem aligned38480_38481 :
    AlignedValid 12 4 missing38480_38481 records38480_38481 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38480
    maskCheck38480 AlignedValid.nil

def missing38481_38482 : List (BitVec (edgeCount 12)) :=
  [missing38481]
abbrev records38481_38482 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38481]
theorem aligned38481_38482 :
    AlignedValid 12 4 missing38481_38482 records38481_38482 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38481
    maskCheck38481 AlignedValid.nil

def missing38480_38482 : List (BitVec (edgeCount 12)) :=
  missing38480_38481 ++ missing38481_38482
abbrev records38480_38482 : List Blob :=
  records38480_38481 ++ records38481_38482
theorem aligned38480_38482 :
    AlignedValid 12 4 missing38480_38482 records38480_38482 :=
  aligned38480_38481.append aligned38481_38482

def missing38482_38483 : List (BitVec (edgeCount 12)) :=
  [missing38482]
abbrev records38482_38483 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38482]
theorem aligned38482_38483 :
    AlignedValid 12 4 missing38482_38483 records38482_38483 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38482
    maskCheck38482 AlignedValid.nil

def missing38483_38484 : List (BitVec (edgeCount 12)) :=
  [missing38483]
abbrev records38483_38484 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38483]
theorem aligned38483_38484 :
    AlignedValid 12 4 missing38483_38484 records38483_38484 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38483
    maskCheck38483 AlignedValid.nil

def missing38482_38484 : List (BitVec (edgeCount 12)) :=
  missing38482_38483 ++ missing38483_38484
abbrev records38482_38484 : List Blob :=
  records38482_38483 ++ records38483_38484
theorem aligned38482_38484 :
    AlignedValid 12 4 missing38482_38484 records38482_38484 :=
  aligned38482_38483.append aligned38483_38484

def missing38480_38484 : List (BitVec (edgeCount 12)) :=
  missing38480_38482 ++ missing38482_38484
abbrev records38480_38484 : List Blob :=
  records38480_38482 ++ records38482_38484
theorem aligned38480_38484 :
    AlignedValid 12 4 missing38480_38484 records38480_38484 :=
  aligned38480_38482.append aligned38482_38484

def missing38484_38485 : List (BitVec (edgeCount 12)) :=
  [missing38484]
abbrev records38484_38485 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38484]
theorem aligned38484_38485 :
    AlignedValid 12 4 missing38484_38485 records38484_38485 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38484
    maskCheck38484 AlignedValid.nil

def missing38485_38486 : List (BitVec (edgeCount 12)) :=
  [missing38485]
abbrev records38485_38486 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38485]
theorem aligned38485_38486 :
    AlignedValid 12 4 missing38485_38486 records38485_38486 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38485
    maskCheck38485 AlignedValid.nil

def missing38484_38486 : List (BitVec (edgeCount 12)) :=
  missing38484_38485 ++ missing38485_38486
abbrev records38484_38486 : List Blob :=
  records38484_38485 ++ records38485_38486
theorem aligned38484_38486 :
    AlignedValid 12 4 missing38484_38486 records38484_38486 :=
  aligned38484_38485.append aligned38485_38486

def missing38486_38487 : List (BitVec (edgeCount 12)) :=
  [missing38486]
abbrev records38486_38487 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38486]
theorem aligned38486_38487 :
    AlignedValid 12 4 missing38486_38487 records38486_38487 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38486
    maskCheck38486 AlignedValid.nil

def missing38487_38488 : List (BitVec (edgeCount 12)) :=
  [missing38487]
abbrev records38487_38488 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38487]
theorem aligned38487_38488 :
    AlignedValid 12 4 missing38487_38488 records38487_38488 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38487
    maskCheck38487 AlignedValid.nil

def missing38486_38488 : List (BitVec (edgeCount 12)) :=
  missing38486_38487 ++ missing38487_38488
abbrev records38486_38488 : List Blob :=
  records38486_38487 ++ records38487_38488
theorem aligned38486_38488 :
    AlignedValid 12 4 missing38486_38488 records38486_38488 :=
  aligned38486_38487.append aligned38487_38488

def missing38484_38488 : List (BitVec (edgeCount 12)) :=
  missing38484_38486 ++ missing38486_38488
abbrev records38484_38488 : List Blob :=
  records38484_38486 ++ records38486_38488
theorem aligned38484_38488 :
    AlignedValid 12 4 missing38484_38488 records38484_38488 :=
  aligned38484_38486.append aligned38486_38488

def missing38480_38488 : List (BitVec (edgeCount 12)) :=
  missing38480_38484 ++ missing38484_38488
abbrev records38480_38488 : List Blob :=
  records38480_38484 ++ records38484_38488
theorem aligned38480_38488 :
    AlignedValid 12 4 missing38480_38488 records38480_38488 :=
  aligned38480_38484.append aligned38484_38488

def missing38488_38489 : List (BitVec (edgeCount 12)) :=
  [missing38488]
abbrev records38488_38489 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38488]
theorem aligned38488_38489 :
    AlignedValid 12 4 missing38488_38489 records38488_38489 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38488
    maskCheck38488 AlignedValid.nil

def missing38489_38490 : List (BitVec (edgeCount 12)) :=
  [missing38489]
abbrev records38489_38490 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38489]
theorem aligned38489_38490 :
    AlignedValid 12 4 missing38489_38490 records38489_38490 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38489
    maskCheck38489 AlignedValid.nil

def missing38488_38490 : List (BitVec (edgeCount 12)) :=
  missing38488_38489 ++ missing38489_38490
abbrev records38488_38490 : List Blob :=
  records38488_38489 ++ records38489_38490
theorem aligned38488_38490 :
    AlignedValid 12 4 missing38488_38490 records38488_38490 :=
  aligned38488_38489.append aligned38489_38490

def missing38490_38491 : List (BitVec (edgeCount 12)) :=
  [missing38490]
abbrev records38490_38491 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38490]
theorem aligned38490_38491 :
    AlignedValid 12 4 missing38490_38491 records38490_38491 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38490
    maskCheck38490 AlignedValid.nil

def missing38491_38492 : List (BitVec (edgeCount 12)) :=
  [missing38491]
abbrev records38491_38492 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38491]
theorem aligned38491_38492 :
    AlignedValid 12 4 missing38491_38492 records38491_38492 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38491
    maskCheck38491 AlignedValid.nil

def missing38490_38492 : List (BitVec (edgeCount 12)) :=
  missing38490_38491 ++ missing38491_38492
abbrev records38490_38492 : List Blob :=
  records38490_38491 ++ records38491_38492
theorem aligned38490_38492 :
    AlignedValid 12 4 missing38490_38492 records38490_38492 :=
  aligned38490_38491.append aligned38491_38492

def missing38488_38492 : List (BitVec (edgeCount 12)) :=
  missing38488_38490 ++ missing38490_38492
abbrev records38488_38492 : List Blob :=
  records38488_38490 ++ records38490_38492
theorem aligned38488_38492 :
    AlignedValid 12 4 missing38488_38492 records38488_38492 :=
  aligned38488_38490.append aligned38490_38492

def missing38492_38493 : List (BitVec (edgeCount 12)) :=
  [missing38492]
abbrev records38492_38493 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38492]
theorem aligned38492_38493 :
    AlignedValid 12 4 missing38492_38493 records38492_38493 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38492
    maskCheck38492 AlignedValid.nil

def missing38493_38494 : List (BitVec (edgeCount 12)) :=
  [missing38493]
abbrev records38493_38494 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38493]
theorem aligned38493_38494 :
    AlignedValid 12 4 missing38493_38494 records38493_38494 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38493
    maskCheck38493 AlignedValid.nil

def missing38492_38494 : List (BitVec (edgeCount 12)) :=
  missing38492_38493 ++ missing38493_38494
abbrev records38492_38494 : List Blob :=
  records38492_38493 ++ records38493_38494
theorem aligned38492_38494 :
    AlignedValid 12 4 missing38492_38494 records38492_38494 :=
  aligned38492_38493.append aligned38493_38494

def missing38494_38495 : List (BitVec (edgeCount 12)) :=
  [missing38494]
abbrev records38494_38495 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38494]
theorem aligned38494_38495 :
    AlignedValid 12 4 missing38494_38495 records38494_38495 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38494
    maskCheck38494 AlignedValid.nil

def missing38495_38496 : List (BitVec (edgeCount 12)) :=
  [missing38495]
abbrev records38495_38496 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38495]
theorem aligned38495_38496 :
    AlignedValid 12 4 missing38495_38496 records38495_38496 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38495
    maskCheck38495 AlignedValid.nil

def missing38494_38496 : List (BitVec (edgeCount 12)) :=
  missing38494_38495 ++ missing38495_38496
abbrev records38494_38496 : List Blob :=
  records38494_38495 ++ records38495_38496
theorem aligned38494_38496 :
    AlignedValid 12 4 missing38494_38496 records38494_38496 :=
  aligned38494_38495.append aligned38495_38496

def missing38492_38496 : List (BitVec (edgeCount 12)) :=
  missing38492_38494 ++ missing38494_38496
abbrev records38492_38496 : List Blob :=
  records38492_38494 ++ records38494_38496
theorem aligned38492_38496 :
    AlignedValid 12 4 missing38492_38496 records38492_38496 :=
  aligned38492_38494.append aligned38494_38496

def missing38488_38496 : List (BitVec (edgeCount 12)) :=
  missing38488_38492 ++ missing38492_38496
abbrev records38488_38496 : List Blob :=
  records38488_38492 ++ records38492_38496
theorem aligned38488_38496 :
    AlignedValid 12 4 missing38488_38496 records38488_38496 :=
  aligned38488_38492.append aligned38492_38496

def missing38480_38496 : List (BitVec (edgeCount 12)) :=
  missing38480_38488 ++ missing38488_38496
abbrev records38480_38496 : List Blob :=
  records38480_38488 ++ records38488_38496
theorem aligned38480_38496 :
    AlignedValid 12 4 missing38480_38496 records38480_38496 :=
  aligned38480_38488.append aligned38488_38496

def missing38464_38496 : List (BitVec (edgeCount 12)) :=
  missing38464_38480 ++ missing38480_38496
abbrev records38464_38496 : List Blob :=
  records38464_38480 ++ records38480_38496
theorem aligned38464_38496 :
    AlignedValid 12 4 missing38464_38496 records38464_38496 :=
  aligned38464_38480.append aligned38480_38496

def missing38496_38497 : List (BitVec (edgeCount 12)) :=
  [missing38496]
abbrev records38496_38497 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38496]
theorem aligned38496_38497 :
    AlignedValid 12 4 missing38496_38497 records38496_38497 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38496
    maskCheck38496 AlignedValid.nil

def missing38497_38498 : List (BitVec (edgeCount 12)) :=
  [missing38497]
abbrev records38497_38498 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38497]
theorem aligned38497_38498 :
    AlignedValid 12 4 missing38497_38498 records38497_38498 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38497
    maskCheck38497 AlignedValid.nil

def missing38496_38498 : List (BitVec (edgeCount 12)) :=
  missing38496_38497 ++ missing38497_38498
abbrev records38496_38498 : List Blob :=
  records38496_38497 ++ records38497_38498
theorem aligned38496_38498 :
    AlignedValid 12 4 missing38496_38498 records38496_38498 :=
  aligned38496_38497.append aligned38497_38498

def missing38498_38499 : List (BitVec (edgeCount 12)) :=
  [missing38498]
abbrev records38498_38499 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38498]
theorem aligned38498_38499 :
    AlignedValid 12 4 missing38498_38499 records38498_38499 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38498
    maskCheck38498 AlignedValid.nil

def missing38499_38500 : List (BitVec (edgeCount 12)) :=
  [missing38499]
abbrev records38499_38500 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38499]
theorem aligned38499_38500 :
    AlignedValid 12 4 missing38499_38500 records38499_38500 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38499
    maskCheck38499 AlignedValid.nil

def missing38498_38500 : List (BitVec (edgeCount 12)) :=
  missing38498_38499 ++ missing38499_38500
abbrev records38498_38500 : List Blob :=
  records38498_38499 ++ records38499_38500
theorem aligned38498_38500 :
    AlignedValid 12 4 missing38498_38500 records38498_38500 :=
  aligned38498_38499.append aligned38499_38500

def missing38496_38500 : List (BitVec (edgeCount 12)) :=
  missing38496_38498 ++ missing38498_38500
abbrev records38496_38500 : List Blob :=
  records38496_38498 ++ records38498_38500
theorem aligned38496_38500 :
    AlignedValid 12 4 missing38496_38500 records38496_38500 :=
  aligned38496_38498.append aligned38498_38500

def missing38500_38501 : List (BitVec (edgeCount 12)) :=
  [missing38500]
abbrev records38500_38501 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38500]
theorem aligned38500_38501 :
    AlignedValid 12 4 missing38500_38501 records38500_38501 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38500
    maskCheck38500 AlignedValid.nil

def missing38501_38502 : List (BitVec (edgeCount 12)) :=
  [missing38501]
abbrev records38501_38502 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38501]
theorem aligned38501_38502 :
    AlignedValid 12 4 missing38501_38502 records38501_38502 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38501
    maskCheck38501 AlignedValid.nil

def missing38500_38502 : List (BitVec (edgeCount 12)) :=
  missing38500_38501 ++ missing38501_38502
abbrev records38500_38502 : List Blob :=
  records38500_38501 ++ records38501_38502
theorem aligned38500_38502 :
    AlignedValid 12 4 missing38500_38502 records38500_38502 :=
  aligned38500_38501.append aligned38501_38502

def missing38502_38503 : List (BitVec (edgeCount 12)) :=
  [missing38502]
abbrev records38502_38503 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38502]
theorem aligned38502_38503 :
    AlignedValid 12 4 missing38502_38503 records38502_38503 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38502
    maskCheck38502 AlignedValid.nil

def missing38503_38504 : List (BitVec (edgeCount 12)) :=
  [missing38503]
abbrev records38503_38504 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38503]
theorem aligned38503_38504 :
    AlignedValid 12 4 missing38503_38504 records38503_38504 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38503
    maskCheck38503 AlignedValid.nil

def missing38502_38504 : List (BitVec (edgeCount 12)) :=
  missing38502_38503 ++ missing38503_38504
abbrev records38502_38504 : List Blob :=
  records38502_38503 ++ records38503_38504
theorem aligned38502_38504 :
    AlignedValid 12 4 missing38502_38504 records38502_38504 :=
  aligned38502_38503.append aligned38503_38504

def missing38500_38504 : List (BitVec (edgeCount 12)) :=
  missing38500_38502 ++ missing38502_38504
abbrev records38500_38504 : List Blob :=
  records38500_38502 ++ records38502_38504
theorem aligned38500_38504 :
    AlignedValid 12 4 missing38500_38504 records38500_38504 :=
  aligned38500_38502.append aligned38502_38504

def missing38496_38504 : List (BitVec (edgeCount 12)) :=
  missing38496_38500 ++ missing38500_38504
abbrev records38496_38504 : List Blob :=
  records38496_38500 ++ records38500_38504
theorem aligned38496_38504 :
    AlignedValid 12 4 missing38496_38504 records38496_38504 :=
  aligned38496_38500.append aligned38500_38504

def missing38504_38505 : List (BitVec (edgeCount 12)) :=
  [missing38504]
abbrev records38504_38505 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38504]
theorem aligned38504_38505 :
    AlignedValid 12 4 missing38504_38505 records38504_38505 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38504
    maskCheck38504 AlignedValid.nil

def missing38505_38506 : List (BitVec (edgeCount 12)) :=
  [missing38505]
abbrev records38505_38506 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38505]
theorem aligned38505_38506 :
    AlignedValid 12 4 missing38505_38506 records38505_38506 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38505
    maskCheck38505 AlignedValid.nil

def missing38504_38506 : List (BitVec (edgeCount 12)) :=
  missing38504_38505 ++ missing38505_38506
abbrev records38504_38506 : List Blob :=
  records38504_38505 ++ records38505_38506
theorem aligned38504_38506 :
    AlignedValid 12 4 missing38504_38506 records38504_38506 :=
  aligned38504_38505.append aligned38505_38506

def missing38506_38507 : List (BitVec (edgeCount 12)) :=
  [missing38506]
abbrev records38506_38507 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38506]
theorem aligned38506_38507 :
    AlignedValid 12 4 missing38506_38507 records38506_38507 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38506
    maskCheck38506 AlignedValid.nil

def missing38507_38508 : List (BitVec (edgeCount 12)) :=
  [missing38507]
abbrev records38507_38508 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38507]
theorem aligned38507_38508 :
    AlignedValid 12 4 missing38507_38508 records38507_38508 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38507
    maskCheck38507 AlignedValid.nil

def missing38506_38508 : List (BitVec (edgeCount 12)) :=
  missing38506_38507 ++ missing38507_38508
abbrev records38506_38508 : List Blob :=
  records38506_38507 ++ records38507_38508
theorem aligned38506_38508 :
    AlignedValid 12 4 missing38506_38508 records38506_38508 :=
  aligned38506_38507.append aligned38507_38508

def missing38504_38508 : List (BitVec (edgeCount 12)) :=
  missing38504_38506 ++ missing38506_38508
abbrev records38504_38508 : List Blob :=
  records38504_38506 ++ records38506_38508
theorem aligned38504_38508 :
    AlignedValid 12 4 missing38504_38508 records38504_38508 :=
  aligned38504_38506.append aligned38506_38508

def missing38508_38509 : List (BitVec (edgeCount 12)) :=
  [missing38508]
abbrev records38508_38509 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38508]
theorem aligned38508_38509 :
    AlignedValid 12 4 missing38508_38509 records38508_38509 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38508
    maskCheck38508 AlignedValid.nil

def missing38509_38510 : List (BitVec (edgeCount 12)) :=
  [missing38509]
abbrev records38509_38510 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38509]
theorem aligned38509_38510 :
    AlignedValid 12 4 missing38509_38510 records38509_38510 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38509
    maskCheck38509 AlignedValid.nil

def missing38508_38510 : List (BitVec (edgeCount 12)) :=
  missing38508_38509 ++ missing38509_38510
abbrev records38508_38510 : List Blob :=
  records38508_38509 ++ records38509_38510
theorem aligned38508_38510 :
    AlignedValid 12 4 missing38508_38510 records38508_38510 :=
  aligned38508_38509.append aligned38509_38510

def missing38510_38511 : List (BitVec (edgeCount 12)) :=
  [missing38510]
abbrev records38510_38511 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38510]
theorem aligned38510_38511 :
    AlignedValid 12 4 missing38510_38511 records38510_38511 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38510
    maskCheck38510 AlignedValid.nil

def missing38511_38512 : List (BitVec (edgeCount 12)) :=
  [missing38511]
abbrev records38511_38512 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38511]
theorem aligned38511_38512 :
    AlignedValid 12 4 missing38511_38512 records38511_38512 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38511
    maskCheck38511 AlignedValid.nil

def missing38510_38512 : List (BitVec (edgeCount 12)) :=
  missing38510_38511 ++ missing38511_38512
abbrev records38510_38512 : List Blob :=
  records38510_38511 ++ records38511_38512
theorem aligned38510_38512 :
    AlignedValid 12 4 missing38510_38512 records38510_38512 :=
  aligned38510_38511.append aligned38511_38512

def missing38508_38512 : List (BitVec (edgeCount 12)) :=
  missing38508_38510 ++ missing38510_38512
abbrev records38508_38512 : List Blob :=
  records38508_38510 ++ records38510_38512
theorem aligned38508_38512 :
    AlignedValid 12 4 missing38508_38512 records38508_38512 :=
  aligned38508_38510.append aligned38510_38512

def missing38504_38512 : List (BitVec (edgeCount 12)) :=
  missing38504_38508 ++ missing38508_38512
abbrev records38504_38512 : List Blob :=
  records38504_38508 ++ records38508_38512
theorem aligned38504_38512 :
    AlignedValid 12 4 missing38504_38512 records38504_38512 :=
  aligned38504_38508.append aligned38508_38512

def missing38496_38512 : List (BitVec (edgeCount 12)) :=
  missing38496_38504 ++ missing38504_38512
abbrev records38496_38512 : List Blob :=
  records38496_38504 ++ records38504_38512
theorem aligned38496_38512 :
    AlignedValid 12 4 missing38496_38512 records38496_38512 :=
  aligned38496_38504.append aligned38504_38512

def missing38512_38513 : List (BitVec (edgeCount 12)) :=
  [missing38512]
abbrev records38512_38513 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38512]
theorem aligned38512_38513 :
    AlignedValid 12 4 missing38512_38513 records38512_38513 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38512
    maskCheck38512 AlignedValid.nil

def missing38513_38514 : List (BitVec (edgeCount 12)) :=
  [missing38513]
abbrev records38513_38514 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38513]
theorem aligned38513_38514 :
    AlignedValid 12 4 missing38513_38514 records38513_38514 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38513
    maskCheck38513 AlignedValid.nil

def missing38512_38514 : List (BitVec (edgeCount 12)) :=
  missing38512_38513 ++ missing38513_38514
abbrev records38512_38514 : List Blob :=
  records38512_38513 ++ records38513_38514
theorem aligned38512_38514 :
    AlignedValid 12 4 missing38512_38514 records38512_38514 :=
  aligned38512_38513.append aligned38513_38514

def missing38514_38515 : List (BitVec (edgeCount 12)) :=
  [missing38514]
abbrev records38514_38515 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38514]
theorem aligned38514_38515 :
    AlignedValid 12 4 missing38514_38515 records38514_38515 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38514
    maskCheck38514 AlignedValid.nil

def missing38515_38516 : List (BitVec (edgeCount 12)) :=
  [missing38515]
abbrev records38515_38516 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38515]
theorem aligned38515_38516 :
    AlignedValid 12 4 missing38515_38516 records38515_38516 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38515
    maskCheck38515 AlignedValid.nil

def missing38514_38516 : List (BitVec (edgeCount 12)) :=
  missing38514_38515 ++ missing38515_38516
abbrev records38514_38516 : List Blob :=
  records38514_38515 ++ records38515_38516
theorem aligned38514_38516 :
    AlignedValid 12 4 missing38514_38516 records38514_38516 :=
  aligned38514_38515.append aligned38515_38516

def missing38512_38516 : List (BitVec (edgeCount 12)) :=
  missing38512_38514 ++ missing38514_38516
abbrev records38512_38516 : List Blob :=
  records38512_38514 ++ records38514_38516
theorem aligned38512_38516 :
    AlignedValid 12 4 missing38512_38516 records38512_38516 :=
  aligned38512_38514.append aligned38514_38516

def missing38516_38517 : List (BitVec (edgeCount 12)) :=
  [missing38516]
abbrev records38516_38517 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38516]
theorem aligned38516_38517 :
    AlignedValid 12 4 missing38516_38517 records38516_38517 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38516
    maskCheck38516 AlignedValid.nil

def missing38517_38518 : List (BitVec (edgeCount 12)) :=
  [missing38517]
abbrev records38517_38518 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38517]
theorem aligned38517_38518 :
    AlignedValid 12 4 missing38517_38518 records38517_38518 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38517
    maskCheck38517 AlignedValid.nil

def missing38516_38518 : List (BitVec (edgeCount 12)) :=
  missing38516_38517 ++ missing38517_38518
abbrev records38516_38518 : List Blob :=
  records38516_38517 ++ records38517_38518
theorem aligned38516_38518 :
    AlignedValid 12 4 missing38516_38518 records38516_38518 :=
  aligned38516_38517.append aligned38517_38518

def missing38518_38519 : List (BitVec (edgeCount 12)) :=
  [missing38518]
abbrev records38518_38519 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38518]
theorem aligned38518_38519 :
    AlignedValid 12 4 missing38518_38519 records38518_38519 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38518
    maskCheck38518 AlignedValid.nil

def missing38519_38520 : List (BitVec (edgeCount 12)) :=
  [missing38519]
abbrev records38519_38520 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38519]
theorem aligned38519_38520 :
    AlignedValid 12 4 missing38519_38520 records38519_38520 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38519
    maskCheck38519 AlignedValid.nil

def missing38518_38520 : List (BitVec (edgeCount 12)) :=
  missing38518_38519 ++ missing38519_38520
abbrev records38518_38520 : List Blob :=
  records38518_38519 ++ records38519_38520
theorem aligned38518_38520 :
    AlignedValid 12 4 missing38518_38520 records38518_38520 :=
  aligned38518_38519.append aligned38519_38520

def missing38516_38520 : List (BitVec (edgeCount 12)) :=
  missing38516_38518 ++ missing38518_38520
abbrev records38516_38520 : List Blob :=
  records38516_38518 ++ records38518_38520
theorem aligned38516_38520 :
    AlignedValid 12 4 missing38516_38520 records38516_38520 :=
  aligned38516_38518.append aligned38518_38520

def missing38512_38520 : List (BitVec (edgeCount 12)) :=
  missing38512_38516 ++ missing38516_38520
abbrev records38512_38520 : List Blob :=
  records38512_38516 ++ records38516_38520
theorem aligned38512_38520 :
    AlignedValid 12 4 missing38512_38520 records38512_38520 :=
  aligned38512_38516.append aligned38516_38520

def missing38520_38521 : List (BitVec (edgeCount 12)) :=
  [missing38520]
abbrev records38520_38521 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38520]
theorem aligned38520_38521 :
    AlignedValid 12 4 missing38520_38521 records38520_38521 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38520
    maskCheck38520 AlignedValid.nil

def missing38521_38522 : List (BitVec (edgeCount 12)) :=
  [missing38521]
abbrev records38521_38522 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38521]
theorem aligned38521_38522 :
    AlignedValid 12 4 missing38521_38522 records38521_38522 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38521
    maskCheck38521 AlignedValid.nil

def missing38520_38522 : List (BitVec (edgeCount 12)) :=
  missing38520_38521 ++ missing38521_38522
abbrev records38520_38522 : List Blob :=
  records38520_38521 ++ records38521_38522
theorem aligned38520_38522 :
    AlignedValid 12 4 missing38520_38522 records38520_38522 :=
  aligned38520_38521.append aligned38521_38522

def missing38522_38523 : List (BitVec (edgeCount 12)) :=
  [missing38522]
abbrev records38522_38523 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38522]
theorem aligned38522_38523 :
    AlignedValid 12 4 missing38522_38523 records38522_38523 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38522
    maskCheck38522 AlignedValid.nil

def missing38523_38524 : List (BitVec (edgeCount 12)) :=
  [missing38523]
abbrev records38523_38524 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38523]
theorem aligned38523_38524 :
    AlignedValid 12 4 missing38523_38524 records38523_38524 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38523
    maskCheck38523 AlignedValid.nil

def missing38522_38524 : List (BitVec (edgeCount 12)) :=
  missing38522_38523 ++ missing38523_38524
abbrev records38522_38524 : List Blob :=
  records38522_38523 ++ records38523_38524
theorem aligned38522_38524 :
    AlignedValid 12 4 missing38522_38524 records38522_38524 :=
  aligned38522_38523.append aligned38523_38524

def missing38520_38524 : List (BitVec (edgeCount 12)) :=
  missing38520_38522 ++ missing38522_38524
abbrev records38520_38524 : List Blob :=
  records38520_38522 ++ records38522_38524
theorem aligned38520_38524 :
    AlignedValid 12 4 missing38520_38524 records38520_38524 :=
  aligned38520_38522.append aligned38522_38524

def missing38524_38525 : List (BitVec (edgeCount 12)) :=
  [missing38524]
abbrev records38524_38525 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38524]
theorem aligned38524_38525 :
    AlignedValid 12 4 missing38524_38525 records38524_38525 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38524
    maskCheck38524 AlignedValid.nil

def missing38525_38526 : List (BitVec (edgeCount 12)) :=
  [missing38525]
abbrev records38525_38526 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38525]
theorem aligned38525_38526 :
    AlignedValid 12 4 missing38525_38526 records38525_38526 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38525
    maskCheck38525 AlignedValid.nil

def missing38524_38526 : List (BitVec (edgeCount 12)) :=
  missing38524_38525 ++ missing38525_38526
abbrev records38524_38526 : List Blob :=
  records38524_38525 ++ records38525_38526
theorem aligned38524_38526 :
    AlignedValid 12 4 missing38524_38526 records38524_38526 :=
  aligned38524_38525.append aligned38525_38526

def missing38526_38527 : List (BitVec (edgeCount 12)) :=
  [missing38526]
abbrev records38526_38527 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38526]
theorem aligned38526_38527 :
    AlignedValid 12 4 missing38526_38527 records38526_38527 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38526
    maskCheck38526 AlignedValid.nil

def missing38527_38528 : List (BitVec (edgeCount 12)) :=
  [missing38527]
abbrev records38527_38528 : List Blob :=
  [StrongPackedBucketN12A4Shard300.record38527]
theorem aligned38527_38528 :
    AlignedValid 12 4 missing38527_38528 records38527_38528 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard300.check38527
    maskCheck38527 AlignedValid.nil

def missing38526_38528 : List (BitVec (edgeCount 12)) :=
  missing38526_38527 ++ missing38527_38528
abbrev records38526_38528 : List Blob :=
  records38526_38527 ++ records38527_38528
theorem aligned38526_38528 :
    AlignedValid 12 4 missing38526_38528 records38526_38528 :=
  aligned38526_38527.append aligned38527_38528

def missing38524_38528 : List (BitVec (edgeCount 12)) :=
  missing38524_38526 ++ missing38526_38528
abbrev records38524_38528 : List Blob :=
  records38524_38526 ++ records38526_38528
theorem aligned38524_38528 :
    AlignedValid 12 4 missing38524_38528 records38524_38528 :=
  aligned38524_38526.append aligned38526_38528

def missing38520_38528 : List (BitVec (edgeCount 12)) :=
  missing38520_38524 ++ missing38524_38528
abbrev records38520_38528 : List Blob :=
  records38520_38524 ++ records38524_38528
theorem aligned38520_38528 :
    AlignedValid 12 4 missing38520_38528 records38520_38528 :=
  aligned38520_38524.append aligned38524_38528

def missing38512_38528 : List (BitVec (edgeCount 12)) :=
  missing38512_38520 ++ missing38520_38528
abbrev records38512_38528 : List Blob :=
  records38512_38520 ++ records38520_38528
theorem aligned38512_38528 :
    AlignedValid 12 4 missing38512_38528 records38512_38528 :=
  aligned38512_38520.append aligned38520_38528

def missing38496_38528 : List (BitVec (edgeCount 12)) :=
  missing38496_38512 ++ missing38512_38528
abbrev records38496_38528 : List Blob :=
  records38496_38512 ++ records38512_38528
theorem aligned38496_38528 :
    AlignedValid 12 4 missing38496_38528 records38496_38528 :=
  aligned38496_38512.append aligned38512_38528

def missing38464_38528 : List (BitVec (edgeCount 12)) :=
  missing38464_38496 ++ missing38496_38528
abbrev records38464_38528 : List Blob :=
  records38464_38496 ++ records38496_38528
theorem aligned38464_38528 :
    AlignedValid 12 4 missing38464_38528 records38464_38528 :=
  aligned38464_38496.append aligned38496_38528

def missing38400_38528 : List (BitVec (edgeCount 12)) :=
  missing38400_38464 ++ missing38464_38528
abbrev records38400_38528 : List Blob :=
  records38400_38464 ++ records38464_38528
theorem aligned38400_38528 :
    AlignedValid 12 4 missing38400_38528 records38400_38528 :=
  aligned38400_38464.append aligned38464_38528

abbrev missing : List (BitVec (edgeCount 12)) := missing38400_38528
abbrev records : List Blob := records38400_38528
theorem aligned : AlignedValid 12 4 missing records := aligned38400_38528

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard300
