/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard168

/-! Decode-only alignment checks for n=12, a=4, records 21504--21631. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard168

open PackedBucketCertificate

def missing21504 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42406738929374986240
theorem maskCheck21504 :
    checkMaskFor missing21504 StrongPackedBucketN12A4Shard168.record21504 = true := by
  decide

def missing21505 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42442767726393950208
theorem maskCheck21505 :
    checkMaskFor missing21505 StrongPackedBucketN12A4Shard168.record21505 = true := by
  decide

def missing21506 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42514825320431878144
theorem maskCheck21506 :
    checkMaskFor missing21506 StrongPackedBucketN12A4Shard168.record21506 = true := by
  decide

def missing21507 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42767026899564625920
theorem maskCheck21507 :
    checkMaskFor missing21507 StrongPackedBucketN12A4Shard168.record21507 = true := by
  decide

def missing21508 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42839084493602553856
theorem maskCheck21508 :
    checkMaskFor missing21508 StrongPackedBucketN12A4Shard168.record21508 = true := by
  decide

def missing21509 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42875113290621517824
theorem maskCheck21509 :
    checkMaskFor missing21509 StrongPackedBucketN12A4Shard168.record21509 = true := by
  decide

def missing21510 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42983199681678409728
theorem maskCheck21510 :
    checkMaskFor missing21510 StrongPackedBucketN12A4Shard168.record21510 = true := by
  decide

def missing21511 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43019228478697373696
theorem maskCheck21511 :
    checkMaskFor missing21511 StrongPackedBucketN12A4Shard168.record21511 = true := by
  decide

def missing21512 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43091286072735301632
theorem maskCheck21512 :
    checkMaskFor missing21512 StrongPackedBucketN12A4Shard168.record21512 = true := by
  decide

def missing21513 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45000812314740391936
theorem maskCheck21513 :
    checkMaskFor missing21513 StrongPackedBucketN12A4Shard168.record21513 = true := by
  decide

def missing21514 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45036841111759355904
theorem maskCheck21514 :
    checkMaskFor missing21514 StrongPackedBucketN12A4Shard168.record21514 = true := by
  decide

def missing21515 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45108898705797283840
theorem maskCheck21515 :
    checkMaskFor missing21515 StrongPackedBucketN12A4Shard168.record21515 = true := by
  decide

def missing21516 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46369906601461022720
theorem maskCheck21516 :
    checkMaskFor missing21516 StrongPackedBucketN12A4Shard168.record21516 = true := by
  decide

def missing21517 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46514021789536878592
theorem maskCheck21517 :
    checkMaskFor missing21517 StrongPackedBucketN12A4Shard168.record21517 = true := by
  decide

def missing21518 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46586079383574806528
theorem maskCheck21518 :
    checkMaskFor missing21518 StrongPackedBucketN12A4Shard168.record21518 = true := by
  decide

def missing21519 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46622108180593770496
theorem maskCheck21519 :
    checkMaskFor missing21519 StrongPackedBucketN12A4Shard168.record21519 = true := by
  decide

def missing21520 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47018424947802374144
theorem maskCheck21520 :
    checkMaskFor missing21520 StrongPackedBucketN12A4Shard168.record21520 = true := by
  decide

def missing21521 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47054453744821338112
theorem maskCheck21521 :
    checkMaskFor missing21521 StrongPackedBucketN12A4Shard168.record21521 = true := by
  decide

def missing21522 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47378712917992013824
theorem maskCheck21522 :
    checkMaskFor missing21522 StrongPackedBucketN12A4Shard168.record21522 = true := by
  decide

def missing21523 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47450770512029941760
theorem maskCheck21523 :
    checkMaskFor missing21523 StrongPackedBucketN12A4Shard168.record21523 = true := by
  decide

def missing21524 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47486799309048905728
theorem maskCheck21524 :
    checkMaskFor missing21524 StrongPackedBucketN12A4Shard168.record21524 = true := by
  decide

def missing21525 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47594885700105797632
theorem maskCheck21525 :
    checkMaskFor missing21525 StrongPackedBucketN12A4Shard168.record21525 = true := by
  decide

def missing21526 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47630914497124761600
theorem maskCheck21526 :
    checkMaskFor missing21526 StrongPackedBucketN12A4Shard168.record21526 = true := by
  decide

def missing21527 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49612498333167779840
theorem maskCheck21527 :
    checkMaskFor missing21527 StrongPackedBucketN12A4Shard168.record21527 = true := by
  decide

def missing21528 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49648527130186743808
theorem maskCheck21528 :
    checkMaskFor missing21528 StrongPackedBucketN12A4Shard168.record21528 = true := by
  decide

def missing21529 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50837477431812554752
theorem maskCheck21529 :
    checkMaskFor missing21529 StrongPackedBucketN12A4Shard168.record21529 = true := by
  decide

def missing21530 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50909535025850482688
theorem maskCheck21530 :
    checkMaskFor missing21530 StrongPackedBucketN12A4Shard168.record21530 = true := by
  decide

def missing21531 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50945563822869446656
theorem maskCheck21531 :
    checkMaskFor missing21531 StrongPackedBucketN12A4Shard168.record21531 = true := by
  decide

def missing21532 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51053650213926338560
theorem maskCheck21532 :
    checkMaskFor missing21532 StrongPackedBucketN12A4Shard168.record21532 = true := by
  decide

def missing21533 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51918341342381473792
theorem maskCheck21533 :
    checkMaskFor missing21533 StrongPackedBucketN12A4Shard168.record21533 = true := by
  decide

def missing21534 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55593278638315798528
theorem maskCheck21534 :
    checkMaskFor missing21534 StrongPackedBucketN12A4Shard168.record21534 = true := by
  decide

def missing21535 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55737393826391654400
theorem maskCheck21535 :
    checkMaskFor missing21535 StrongPackedBucketN12A4Shard168.record21535 = true := by
  decide

def missing21536 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55809451420429582336
theorem maskCheck21536 :
    checkMaskFor missing21536 StrongPackedBucketN12A4Shard168.record21536 = true := by
  decide

def missing21537 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56241796984657149952
theorem maskCheck21537 :
    checkMaskFor missing21537 StrongPackedBucketN12A4Shard168.record21537 = true := by
  decide

def missing21538 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56602084954846789632
theorem maskCheck21538 :
    checkMaskFor missing21538 StrongPackedBucketN12A4Shard168.record21538 = true := by
  decide

def missing21539 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56674142548884717568
theorem maskCheck21539 :
    checkMaskFor missing21539 StrongPackedBucketN12A4Shard168.record21539 = true := by
  decide

def missing21540 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56818257736960573440
theorem maskCheck21540 :
    checkMaskFor missing21540 StrongPackedBucketN12A4Shard168.record21540 = true := by
  decide

def missing21541 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58835870370022555648
theorem maskCheck21541 :
    checkMaskFor missing21541 StrongPackedBucketN12A4Shard168.record21541 = true := by
  decide

def missing21542 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60060849468667330560
theorem maskCheck21542 :
    checkMaskFor missing21542 StrongPackedBucketN12A4Shard168.record21542 = true := by
  decide

def missing21543 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60132907062705258496
theorem maskCheck21543 :
    checkMaskFor missing21543 StrongPackedBucketN12A4Shard168.record21543 = true := by
  decide

def missing21544 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64672535487094718464
theorem maskCheck21544 :
    checkMaskFor missing21544 StrongPackedBucketN12A4Shard168.record21544 = true := by
  decide

def missing21545 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1121537457827872768
theorem maskCheck21545 :
    checkMaskFor missing21545 StrongPackedBucketN12A4Shard168.record21545 = true := by
  decide

def missing21546 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2130343774358863872
theorem maskCheck21546 :
    checkMaskFor missing21546 StrongPackedBucketN12A4Shard168.record21546 = true := by
  decide

def missing21547 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2202401368396791808
theorem maskCheck21547 :
    checkMaskFor missing21547 StrongPackedBucketN12A4Shard168.record21547 = true := by
  decide

def missing21548 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4364129189534629888
theorem maskCheck21548 :
    checkMaskFor missing21548 StrongPackedBucketN12A4Shard168.record21548 = true := by
  decide

def missing21549 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5156762723951837184
theorem maskCheck21549 :
    checkMaskFor missing21549 StrongPackedBucketN12A4Shard168.record21549 = true := by
  decide

def missing21550 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5589108288179404800
theorem maskCheck21550 :
    checkMaskFor missing21550 StrongPackedBucketN12A4Shard168.record21550 = true := by
  decide

def missing21551 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6669972198748323840
theorem maskCheck21551 :
    checkMaskFor missing21551 StrongPackedBucketN12A4Shard168.record21551 = true := by
  decide

def missing21552 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9768448742379225088
theorem maskCheck21552 :
    checkMaskFor missing21552 StrongPackedBucketN12A4Shard168.record21552 = true := by
  decide

def missing21553 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10200794306606792704
theorem maskCheck21553 :
    checkMaskFor missing21553 StrongPackedBucketN12A4Shard168.record21553 = true := by
  decide

def missing21554 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10272851900644720640
theorem maskCheck21554 :
    checkMaskFor missing21554 StrongPackedBucketN12A4Shard168.record21554 = true := by
  decide

def missing21555 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14091904384654901248
theorem maskCheck21555 :
    checkMaskFor missing21555 StrongPackedBucketN12A4Shard168.record21555 = true := by
  decide

def missing21556 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14236019572730757120
theorem maskCheck21556 :
    checkMaskFor missing21556 StrongPackedBucketN12A4Shard168.record21556 = true := by
  decide

def missing21557 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23315276421509677056
theorem maskCheck21557 :
    checkMaskFor missing21557 StrongPackedBucketN12A4Shard168.record21557 = true := by
  decide

def missing21558 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23459391609585532928
theorem maskCheck21558 :
    checkMaskFor missing21558 StrongPackedBucketN12A4Shard168.record21558 = true := by
  decide

def missing21559 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27926962439937064960
theorem maskCheck21559 :
    checkMaskFor missing21559 StrongPackedBucketN12A4Shard168.record21559 = true := by
  decide

def missing21560 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 540889765245878272
theorem maskCheck21560 :
    checkMaskFor missing21560 StrongPackedBucketN12A4Shard168.record21560 = true := by
  decide

def missing21561 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 973235329473445888
theorem maskCheck21561 :
    checkMaskFor missing21561 StrongPackedBucketN12A4Shard168.record21561 = true := by
  decide

def missing21562 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1045292923511373824
theorem maskCheck21562 :
    checkMaskFor missing21562 StrongPackedBucketN12A4Shard168.record21562 = true := by
  decide

def missing21563 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081321720530337792
theorem maskCheck21563 :
    checkMaskFor missing21563 StrongPackedBucketN12A4Shard168.record21563 = true := by
  decide

def missing21564 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1946012848985473024
theorem maskCheck21564 :
    checkMaskFor missing21564 StrongPackedBucketN12A4Shard168.record21564 = true := by
  decide

def missing21565 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2090128037061328896
theorem maskCheck21565 :
    checkMaskFor missing21565 StrongPackedBucketN12A4Shard168.record21565 = true := by
  decide

def missing21566 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2162185631099256832
theorem maskCheck21566 :
    checkMaskFor missing21566 StrongPackedBucketN12A4Shard168.record21566 = true := by
  decide

def missing21567 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4107740670123311104
theorem maskCheck21567 :
    checkMaskFor missing21567 StrongPackedBucketN12A4Shard168.record21567 = true := by
  decide

def missing21568 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4179798264161239040
theorem maskCheck21568 :
    checkMaskFor missing21568 StrongPackedBucketN12A4Shard168.record21568 = true := by
  decide

def missing21569 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4323913452237094912
theorem maskCheck21569 :
    checkMaskFor missing21569 StrongPackedBucketN12A4Shard168.record21569 = true := by
  decide

def missing21570 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5008460595597410304
theorem maskCheck21570 :
    checkMaskFor missing21570 StrongPackedBucketN12A4Shard168.record21570 = true := by
  decide

def missing21571 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5080518189635338240
theorem maskCheck21571 :
    checkMaskFor missing21571 StrongPackedBucketN12A4Shard168.record21571 = true := by
  decide

def missing21572 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5116546986654302208
theorem maskCheck21572 :
    checkMaskFor missing21572 StrongPackedBucketN12A4Shard168.record21572 = true := by
  decide

def missing21573 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5404777362806013952
theorem maskCheck21573 :
    checkMaskFor missing21573 StrongPackedBucketN12A4Shard168.record21573 = true := by
  decide

def missing21574 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5548892550881869824
theorem maskCheck21574 :
    checkMaskFor missing21574 StrongPackedBucketN12A4Shard168.record21574 = true := by
  decide

def missing21575 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5620950144919797760
theorem maskCheck21575 :
    checkMaskFor missing21575 StrongPackedBucketN12A4Shard168.record21575 = true := by
  decide

def missing21576 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6413583679337005056
theorem maskCheck21576 :
    checkMaskFor missing21576 StrongPackedBucketN12A4Shard168.record21576 = true := by
  decide

def missing21577 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6485641273374932992
theorem maskCheck21577 :
    checkMaskFor missing21577 StrongPackedBucketN12A4Shard168.record21577 = true := by
  decide

def missing21578 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6629756461450788864
theorem maskCheck21578 :
    checkMaskFor missing21578 StrongPackedBucketN12A4Shard168.record21578 = true := by
  decide

def missing21579 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9476031425948942336
theorem maskCheck21579 :
    checkMaskFor missing21579 StrongPackedBucketN12A4Shard168.record21579 = true := by
  decide

def missing21580 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9620146614024798208
theorem maskCheck21580 :
    checkMaskFor missing21580 StrongPackedBucketN12A4Shard168.record21580 = true := by
  decide

def missing21581 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9692204208062726144
theorem maskCheck21581 :
    checkMaskFor missing21581 StrongPackedBucketN12A4Shard168.record21581 = true := by
  decide

def missing21582 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9728233005081690112
theorem maskCheck21582 :
    checkMaskFor missing21582 StrongPackedBucketN12A4Shard168.record21582 = true := by
  decide

def missing21583 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9908376990176509952
theorem maskCheck21583 :
    checkMaskFor missing21583 StrongPackedBucketN12A4Shard168.record21583 = true := by
  decide

def missing21584 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9980434584214437888
theorem maskCheck21584 :
    checkMaskFor missing21584 StrongPackedBucketN12A4Shard168.record21584 = true := by
  decide

def missing21585 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10016463381233401856
theorem maskCheck21585 :
    checkMaskFor missing21585 StrongPackedBucketN12A4Shard168.record21585 = true := by
  decide

def missing21586 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10124549772290293760
theorem maskCheck21586 :
    checkMaskFor missing21586 StrongPackedBucketN12A4Shard168.record21586 = true := by
  decide

def missing21587 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10160578569309257728
theorem maskCheck21587 :
    checkMaskFor missing21587 StrongPackedBucketN12A4Shard168.record21587 = true := by
  decide

def missing21588 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10232636163347185664
theorem maskCheck21588 :
    checkMaskFor missing21588 StrongPackedBucketN12A4Shard168.record21588 = true := by
  decide

def missing21589 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11025269697764392960
theorem maskCheck21589 :
    checkMaskFor missing21589 StrongPackedBucketN12A4Shard168.record21589 = true := by
  decide

def missing21590 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11097327291802320896
theorem maskCheck21590 :
    checkMaskFor missing21590 StrongPackedBucketN12A4Shard168.record21590 = true := by
  decide

def missing21591 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13943602256300474368
theorem maskCheck21591 :
    checkMaskFor missing21591 StrongPackedBucketN12A4Shard168.record21591 = true := by
  decide

def missing21592 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14015659850338402304
theorem maskCheck21592 :
    checkMaskFor missing21592 StrongPackedBucketN12A4Shard168.record21592 = true := by
  decide

def missing21593 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14051688647357366272
theorem maskCheck21593 :
    checkMaskFor missing21593 StrongPackedBucketN12A4Shard168.record21593 = true := by
  decide

def missing21594 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14159775038414258176
theorem maskCheck21594 :
    checkMaskFor missing21594 StrongPackedBucketN12A4Shard168.record21594 = true := by
  decide

def missing21595 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14195803835433222144
theorem maskCheck21595 :
    checkMaskFor missing21595 StrongPackedBucketN12A4Shard168.record21595 = true := by
  decide

def missing21596 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14267861429471150080
theorem maskCheck21596 :
    checkMaskFor missing21596 StrongPackedBucketN12A4Shard168.record21596 = true := by
  decide

def missing21597 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14484034211584933888
theorem maskCheck21597 :
    checkMaskFor missing21597 StrongPackedBucketN12A4Shard168.record21597 = true := by
  decide

def missing21598 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18843518650879574016
theorem maskCheck21598 :
    checkMaskFor missing21598 StrongPackedBucketN12A4Shard168.record21598 = true := by
  decide

def missing21599 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18915576244917501952
theorem maskCheck21599 :
    checkMaskFor missing21599 StrongPackedBucketN12A4Shard168.record21599 = true := by
  decide

def missing21600 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18951605041936465920
theorem maskCheck21600 :
    checkMaskFor missing21600 StrongPackedBucketN12A4Shard168.record21600 = true := by
  decide

def missing21601 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19239835418088177664
theorem maskCheck21601 :
    checkMaskFor missing21601 StrongPackedBucketN12A4Shard168.record21601 = true := by
  decide

def missing21602 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19347921809145069568
theorem maskCheck21602 :
    checkMaskFor missing21602 StrongPackedBucketN12A4Shard168.record21602 = true := by
  decide

def missing21603 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19383950606164033536
theorem maskCheck21603 :
    checkMaskFor missing21603 StrongPackedBucketN12A4Shard168.record21603 = true := by
  decide

def missing21604 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20248641734619168768
theorem maskCheck21604 :
    checkMaskFor missing21604 StrongPackedBucketN12A4Shard168.record21604 = true := by
  decide

def missing21605 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23275060684212142080
theorem maskCheck21605 :
    checkMaskFor missing21605 StrongPackedBucketN12A4Shard168.record21605 = true := by
  decide

def missing21606 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23383147075269033984
theorem maskCheck21606 :
    checkMaskFor missing21606 StrongPackedBucketN12A4Shard168.record21606 = true := by
  decide

def missing21607 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23419175872287997952
theorem maskCheck21607 :
    checkMaskFor missing21607 StrongPackedBucketN12A4Shard168.record21607 = true := by
  decide

def missing21608 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27778660311582638080
theorem maskCheck21608 :
    checkMaskFor missing21608 StrongPackedBucketN12A4Shard168.record21608 = true := by
  decide

def missing21609 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27850717905620566016
theorem maskCheck21609 :
    checkMaskFor missing21609 StrongPackedBucketN12A4Shard168.record21609 = true := by
  decide

def missing21610 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27886746702639529984
theorem maskCheck21610 :
    checkMaskFor missing21610 StrongPackedBucketN12A4Shard168.record21610 = true := by
  decide

def missing21611 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27994833093696421888
theorem maskCheck21611 :
    checkMaskFor missing21611 StrongPackedBucketN12A4Shard168.record21611 = true := by
  decide

def missing21612 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28283063469848133632
theorem maskCheck21612 :
    checkMaskFor missing21612 StrongPackedBucketN12A4Shard168.record21612 = true := by
  decide

def missing21613 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32318288735972098048
theorem maskCheck21613 :
    checkMaskFor missing21613 StrongPackedBucketN12A4Shard168.record21613 = true := by
  decide

def missing21614 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37146147536513269760
theorem maskCheck21614 :
    checkMaskFor missing21614 StrongPackedBucketN12A4Shard168.record21614 = true := by
  decide

def missing21615 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37362320318627053568
theorem maskCheck21615 :
    checkMaskFor missing21615 StrongPackedBucketN12A4Shard168.record21615 = true := by
  decide

def missing21616 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46225404385292189696
theorem maskCheck21616 :
    checkMaskFor missing21616 StrongPackedBucketN12A4Shard168.record21616 = true := by
  decide

def missing21617 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46297461979330117632
theorem maskCheck21617 :
    checkMaskFor missing21617 StrongPackedBucketN12A4Shard168.record21617 = true := by
  decide

def missing21618 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 541417530827210752
theorem maskCheck21618 :
    checkMaskFor missing21618 StrongPackedBucketN12A4Shard168.record21618 = true := by
  decide

def missing21619 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 973763095054778368
theorem maskCheck21619 :
    checkMaskFor missing21619 StrongPackedBucketN12A4Shard168.record21619 = true := by
  decide

def missing21620 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1045820689092706304
theorem maskCheck21620 :
    checkMaskFor missing21620 StrongPackedBucketN12A4Shard168.record21620 = true := by
  decide

def missing21621 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081849486111670272
theorem maskCheck21621 :
    checkMaskFor missing21621 StrongPackedBucketN12A4Shard168.record21621 = true := by
  decide

def missing21622 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1406108659282345984
theorem maskCheck21622 :
    checkMaskFor missing21622 StrongPackedBucketN12A4Shard168.record21622 = true := by
  decide

def missing21623 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1550223847358201856
theorem maskCheck21623 :
    checkMaskFor missing21623 StrongPackedBucketN12A4Shard168.record21623 = true := by
  decide

def missing21624 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1622281441396129792
theorem maskCheck21624 :
    checkMaskFor missing21624 StrongPackedBucketN12A4Shard168.record21624 = true := by
  decide

def missing21625 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1658310238415093760
theorem maskCheck21625 :
    checkMaskFor missing21625 StrongPackedBucketN12A4Shard168.record21625 = true := by
  decide

def missing21626 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2054627005623697408
theorem maskCheck21626 :
    checkMaskFor missing21626 StrongPackedBucketN12A4Shard168.record21626 = true := by
  decide

def missing21627 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2090655802642661376
theorem maskCheck21627 :
    checkMaskFor missing21627 StrongPackedBucketN12A4Shard168.record21627 = true := by
  decide

def missing21628 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2162713396680589312
theorem maskCheck21628 :
    checkMaskFor missing21628 StrongPackedBucketN12A4Shard168.record21628 = true := by
  decide

def missing21629 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3567836480420184064
theorem maskCheck21629 :
    checkMaskFor missing21629 StrongPackedBucketN12A4Shard168.record21629 = true := by
  decide

def missing21630 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3639894074458112000
theorem maskCheck21630 :
    checkMaskFor missing21630 StrongPackedBucketN12A4Shard168.record21630 = true := by
  decide

def missing21631 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3675922871477075968
theorem maskCheck21631 :
    checkMaskFor missing21631 StrongPackedBucketN12A4Shard168.record21631 = true := by
  decide

def missing21504_21505 : List (BitVec (edgeCount 12)) :=
  [missing21504]
abbrev records21504_21505 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21504]
theorem aligned21504_21505 :
    AlignedValid 12 4 missing21504_21505 records21504_21505 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21504
    maskCheck21504 AlignedValid.nil

def missing21505_21506 : List (BitVec (edgeCount 12)) :=
  [missing21505]
abbrev records21505_21506 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21505]
theorem aligned21505_21506 :
    AlignedValid 12 4 missing21505_21506 records21505_21506 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21505
    maskCheck21505 AlignedValid.nil

def missing21504_21506 : List (BitVec (edgeCount 12)) :=
  missing21504_21505 ++ missing21505_21506
abbrev records21504_21506 : List Blob :=
  records21504_21505 ++ records21505_21506
theorem aligned21504_21506 :
    AlignedValid 12 4 missing21504_21506 records21504_21506 :=
  aligned21504_21505.append aligned21505_21506

def missing21506_21507 : List (BitVec (edgeCount 12)) :=
  [missing21506]
abbrev records21506_21507 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21506]
theorem aligned21506_21507 :
    AlignedValid 12 4 missing21506_21507 records21506_21507 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21506
    maskCheck21506 AlignedValid.nil

def missing21507_21508 : List (BitVec (edgeCount 12)) :=
  [missing21507]
abbrev records21507_21508 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21507]
theorem aligned21507_21508 :
    AlignedValid 12 4 missing21507_21508 records21507_21508 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21507
    maskCheck21507 AlignedValid.nil

def missing21506_21508 : List (BitVec (edgeCount 12)) :=
  missing21506_21507 ++ missing21507_21508
abbrev records21506_21508 : List Blob :=
  records21506_21507 ++ records21507_21508
theorem aligned21506_21508 :
    AlignedValid 12 4 missing21506_21508 records21506_21508 :=
  aligned21506_21507.append aligned21507_21508

def missing21504_21508 : List (BitVec (edgeCount 12)) :=
  missing21504_21506 ++ missing21506_21508
abbrev records21504_21508 : List Blob :=
  records21504_21506 ++ records21506_21508
theorem aligned21504_21508 :
    AlignedValid 12 4 missing21504_21508 records21504_21508 :=
  aligned21504_21506.append aligned21506_21508

def missing21508_21509 : List (BitVec (edgeCount 12)) :=
  [missing21508]
abbrev records21508_21509 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21508]
theorem aligned21508_21509 :
    AlignedValid 12 4 missing21508_21509 records21508_21509 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21508
    maskCheck21508 AlignedValid.nil

def missing21509_21510 : List (BitVec (edgeCount 12)) :=
  [missing21509]
abbrev records21509_21510 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21509]
theorem aligned21509_21510 :
    AlignedValid 12 4 missing21509_21510 records21509_21510 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21509
    maskCheck21509 AlignedValid.nil

def missing21508_21510 : List (BitVec (edgeCount 12)) :=
  missing21508_21509 ++ missing21509_21510
abbrev records21508_21510 : List Blob :=
  records21508_21509 ++ records21509_21510
theorem aligned21508_21510 :
    AlignedValid 12 4 missing21508_21510 records21508_21510 :=
  aligned21508_21509.append aligned21509_21510

def missing21510_21511 : List (BitVec (edgeCount 12)) :=
  [missing21510]
abbrev records21510_21511 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21510]
theorem aligned21510_21511 :
    AlignedValid 12 4 missing21510_21511 records21510_21511 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21510
    maskCheck21510 AlignedValid.nil

def missing21511_21512 : List (BitVec (edgeCount 12)) :=
  [missing21511]
abbrev records21511_21512 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21511]
theorem aligned21511_21512 :
    AlignedValid 12 4 missing21511_21512 records21511_21512 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21511
    maskCheck21511 AlignedValid.nil

def missing21510_21512 : List (BitVec (edgeCount 12)) :=
  missing21510_21511 ++ missing21511_21512
abbrev records21510_21512 : List Blob :=
  records21510_21511 ++ records21511_21512
theorem aligned21510_21512 :
    AlignedValid 12 4 missing21510_21512 records21510_21512 :=
  aligned21510_21511.append aligned21511_21512

def missing21508_21512 : List (BitVec (edgeCount 12)) :=
  missing21508_21510 ++ missing21510_21512
abbrev records21508_21512 : List Blob :=
  records21508_21510 ++ records21510_21512
theorem aligned21508_21512 :
    AlignedValid 12 4 missing21508_21512 records21508_21512 :=
  aligned21508_21510.append aligned21510_21512

def missing21504_21512 : List (BitVec (edgeCount 12)) :=
  missing21504_21508 ++ missing21508_21512
abbrev records21504_21512 : List Blob :=
  records21504_21508 ++ records21508_21512
theorem aligned21504_21512 :
    AlignedValid 12 4 missing21504_21512 records21504_21512 :=
  aligned21504_21508.append aligned21508_21512

def missing21512_21513 : List (BitVec (edgeCount 12)) :=
  [missing21512]
abbrev records21512_21513 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21512]
theorem aligned21512_21513 :
    AlignedValid 12 4 missing21512_21513 records21512_21513 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21512
    maskCheck21512 AlignedValid.nil

def missing21513_21514 : List (BitVec (edgeCount 12)) :=
  [missing21513]
abbrev records21513_21514 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21513]
theorem aligned21513_21514 :
    AlignedValid 12 4 missing21513_21514 records21513_21514 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21513
    maskCheck21513 AlignedValid.nil

def missing21512_21514 : List (BitVec (edgeCount 12)) :=
  missing21512_21513 ++ missing21513_21514
abbrev records21512_21514 : List Blob :=
  records21512_21513 ++ records21513_21514
theorem aligned21512_21514 :
    AlignedValid 12 4 missing21512_21514 records21512_21514 :=
  aligned21512_21513.append aligned21513_21514

def missing21514_21515 : List (BitVec (edgeCount 12)) :=
  [missing21514]
abbrev records21514_21515 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21514]
theorem aligned21514_21515 :
    AlignedValid 12 4 missing21514_21515 records21514_21515 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21514
    maskCheck21514 AlignedValid.nil

def missing21515_21516 : List (BitVec (edgeCount 12)) :=
  [missing21515]
abbrev records21515_21516 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21515]
theorem aligned21515_21516 :
    AlignedValid 12 4 missing21515_21516 records21515_21516 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21515
    maskCheck21515 AlignedValid.nil

def missing21514_21516 : List (BitVec (edgeCount 12)) :=
  missing21514_21515 ++ missing21515_21516
abbrev records21514_21516 : List Blob :=
  records21514_21515 ++ records21515_21516
theorem aligned21514_21516 :
    AlignedValid 12 4 missing21514_21516 records21514_21516 :=
  aligned21514_21515.append aligned21515_21516

def missing21512_21516 : List (BitVec (edgeCount 12)) :=
  missing21512_21514 ++ missing21514_21516
abbrev records21512_21516 : List Blob :=
  records21512_21514 ++ records21514_21516
theorem aligned21512_21516 :
    AlignedValid 12 4 missing21512_21516 records21512_21516 :=
  aligned21512_21514.append aligned21514_21516

def missing21516_21517 : List (BitVec (edgeCount 12)) :=
  [missing21516]
abbrev records21516_21517 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21516]
theorem aligned21516_21517 :
    AlignedValid 12 4 missing21516_21517 records21516_21517 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21516
    maskCheck21516 AlignedValid.nil

def missing21517_21518 : List (BitVec (edgeCount 12)) :=
  [missing21517]
abbrev records21517_21518 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21517]
theorem aligned21517_21518 :
    AlignedValid 12 4 missing21517_21518 records21517_21518 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21517
    maskCheck21517 AlignedValid.nil

def missing21516_21518 : List (BitVec (edgeCount 12)) :=
  missing21516_21517 ++ missing21517_21518
abbrev records21516_21518 : List Blob :=
  records21516_21517 ++ records21517_21518
theorem aligned21516_21518 :
    AlignedValid 12 4 missing21516_21518 records21516_21518 :=
  aligned21516_21517.append aligned21517_21518

def missing21518_21519 : List (BitVec (edgeCount 12)) :=
  [missing21518]
abbrev records21518_21519 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21518]
theorem aligned21518_21519 :
    AlignedValid 12 4 missing21518_21519 records21518_21519 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21518
    maskCheck21518 AlignedValid.nil

def missing21519_21520 : List (BitVec (edgeCount 12)) :=
  [missing21519]
abbrev records21519_21520 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21519]
theorem aligned21519_21520 :
    AlignedValid 12 4 missing21519_21520 records21519_21520 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21519
    maskCheck21519 AlignedValid.nil

def missing21518_21520 : List (BitVec (edgeCount 12)) :=
  missing21518_21519 ++ missing21519_21520
abbrev records21518_21520 : List Blob :=
  records21518_21519 ++ records21519_21520
theorem aligned21518_21520 :
    AlignedValid 12 4 missing21518_21520 records21518_21520 :=
  aligned21518_21519.append aligned21519_21520

def missing21516_21520 : List (BitVec (edgeCount 12)) :=
  missing21516_21518 ++ missing21518_21520
abbrev records21516_21520 : List Blob :=
  records21516_21518 ++ records21518_21520
theorem aligned21516_21520 :
    AlignedValid 12 4 missing21516_21520 records21516_21520 :=
  aligned21516_21518.append aligned21518_21520

def missing21512_21520 : List (BitVec (edgeCount 12)) :=
  missing21512_21516 ++ missing21516_21520
abbrev records21512_21520 : List Blob :=
  records21512_21516 ++ records21516_21520
theorem aligned21512_21520 :
    AlignedValid 12 4 missing21512_21520 records21512_21520 :=
  aligned21512_21516.append aligned21516_21520

def missing21504_21520 : List (BitVec (edgeCount 12)) :=
  missing21504_21512 ++ missing21512_21520
abbrev records21504_21520 : List Blob :=
  records21504_21512 ++ records21512_21520
theorem aligned21504_21520 :
    AlignedValid 12 4 missing21504_21520 records21504_21520 :=
  aligned21504_21512.append aligned21512_21520

def missing21520_21521 : List (BitVec (edgeCount 12)) :=
  [missing21520]
abbrev records21520_21521 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21520]
theorem aligned21520_21521 :
    AlignedValid 12 4 missing21520_21521 records21520_21521 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21520
    maskCheck21520 AlignedValid.nil

def missing21521_21522 : List (BitVec (edgeCount 12)) :=
  [missing21521]
abbrev records21521_21522 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21521]
theorem aligned21521_21522 :
    AlignedValid 12 4 missing21521_21522 records21521_21522 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21521
    maskCheck21521 AlignedValid.nil

def missing21520_21522 : List (BitVec (edgeCount 12)) :=
  missing21520_21521 ++ missing21521_21522
abbrev records21520_21522 : List Blob :=
  records21520_21521 ++ records21521_21522
theorem aligned21520_21522 :
    AlignedValid 12 4 missing21520_21522 records21520_21522 :=
  aligned21520_21521.append aligned21521_21522

def missing21522_21523 : List (BitVec (edgeCount 12)) :=
  [missing21522]
abbrev records21522_21523 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21522]
theorem aligned21522_21523 :
    AlignedValid 12 4 missing21522_21523 records21522_21523 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21522
    maskCheck21522 AlignedValid.nil

def missing21523_21524 : List (BitVec (edgeCount 12)) :=
  [missing21523]
abbrev records21523_21524 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21523]
theorem aligned21523_21524 :
    AlignedValid 12 4 missing21523_21524 records21523_21524 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21523
    maskCheck21523 AlignedValid.nil

def missing21522_21524 : List (BitVec (edgeCount 12)) :=
  missing21522_21523 ++ missing21523_21524
abbrev records21522_21524 : List Blob :=
  records21522_21523 ++ records21523_21524
theorem aligned21522_21524 :
    AlignedValid 12 4 missing21522_21524 records21522_21524 :=
  aligned21522_21523.append aligned21523_21524

def missing21520_21524 : List (BitVec (edgeCount 12)) :=
  missing21520_21522 ++ missing21522_21524
abbrev records21520_21524 : List Blob :=
  records21520_21522 ++ records21522_21524
theorem aligned21520_21524 :
    AlignedValid 12 4 missing21520_21524 records21520_21524 :=
  aligned21520_21522.append aligned21522_21524

def missing21524_21525 : List (BitVec (edgeCount 12)) :=
  [missing21524]
abbrev records21524_21525 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21524]
theorem aligned21524_21525 :
    AlignedValid 12 4 missing21524_21525 records21524_21525 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21524
    maskCheck21524 AlignedValid.nil

def missing21525_21526 : List (BitVec (edgeCount 12)) :=
  [missing21525]
abbrev records21525_21526 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21525]
theorem aligned21525_21526 :
    AlignedValid 12 4 missing21525_21526 records21525_21526 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21525
    maskCheck21525 AlignedValid.nil

def missing21524_21526 : List (BitVec (edgeCount 12)) :=
  missing21524_21525 ++ missing21525_21526
abbrev records21524_21526 : List Blob :=
  records21524_21525 ++ records21525_21526
theorem aligned21524_21526 :
    AlignedValid 12 4 missing21524_21526 records21524_21526 :=
  aligned21524_21525.append aligned21525_21526

def missing21526_21527 : List (BitVec (edgeCount 12)) :=
  [missing21526]
abbrev records21526_21527 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21526]
theorem aligned21526_21527 :
    AlignedValid 12 4 missing21526_21527 records21526_21527 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21526
    maskCheck21526 AlignedValid.nil

def missing21527_21528 : List (BitVec (edgeCount 12)) :=
  [missing21527]
abbrev records21527_21528 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21527]
theorem aligned21527_21528 :
    AlignedValid 12 4 missing21527_21528 records21527_21528 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21527
    maskCheck21527 AlignedValid.nil

def missing21526_21528 : List (BitVec (edgeCount 12)) :=
  missing21526_21527 ++ missing21527_21528
abbrev records21526_21528 : List Blob :=
  records21526_21527 ++ records21527_21528
theorem aligned21526_21528 :
    AlignedValid 12 4 missing21526_21528 records21526_21528 :=
  aligned21526_21527.append aligned21527_21528

def missing21524_21528 : List (BitVec (edgeCount 12)) :=
  missing21524_21526 ++ missing21526_21528
abbrev records21524_21528 : List Blob :=
  records21524_21526 ++ records21526_21528
theorem aligned21524_21528 :
    AlignedValid 12 4 missing21524_21528 records21524_21528 :=
  aligned21524_21526.append aligned21526_21528

def missing21520_21528 : List (BitVec (edgeCount 12)) :=
  missing21520_21524 ++ missing21524_21528
abbrev records21520_21528 : List Blob :=
  records21520_21524 ++ records21524_21528
theorem aligned21520_21528 :
    AlignedValid 12 4 missing21520_21528 records21520_21528 :=
  aligned21520_21524.append aligned21524_21528

def missing21528_21529 : List (BitVec (edgeCount 12)) :=
  [missing21528]
abbrev records21528_21529 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21528]
theorem aligned21528_21529 :
    AlignedValid 12 4 missing21528_21529 records21528_21529 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21528
    maskCheck21528 AlignedValid.nil

def missing21529_21530 : List (BitVec (edgeCount 12)) :=
  [missing21529]
abbrev records21529_21530 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21529]
theorem aligned21529_21530 :
    AlignedValid 12 4 missing21529_21530 records21529_21530 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21529
    maskCheck21529 AlignedValid.nil

def missing21528_21530 : List (BitVec (edgeCount 12)) :=
  missing21528_21529 ++ missing21529_21530
abbrev records21528_21530 : List Blob :=
  records21528_21529 ++ records21529_21530
theorem aligned21528_21530 :
    AlignedValid 12 4 missing21528_21530 records21528_21530 :=
  aligned21528_21529.append aligned21529_21530

def missing21530_21531 : List (BitVec (edgeCount 12)) :=
  [missing21530]
abbrev records21530_21531 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21530]
theorem aligned21530_21531 :
    AlignedValid 12 4 missing21530_21531 records21530_21531 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21530
    maskCheck21530 AlignedValid.nil

def missing21531_21532 : List (BitVec (edgeCount 12)) :=
  [missing21531]
abbrev records21531_21532 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21531]
theorem aligned21531_21532 :
    AlignedValid 12 4 missing21531_21532 records21531_21532 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21531
    maskCheck21531 AlignedValid.nil

def missing21530_21532 : List (BitVec (edgeCount 12)) :=
  missing21530_21531 ++ missing21531_21532
abbrev records21530_21532 : List Blob :=
  records21530_21531 ++ records21531_21532
theorem aligned21530_21532 :
    AlignedValid 12 4 missing21530_21532 records21530_21532 :=
  aligned21530_21531.append aligned21531_21532

def missing21528_21532 : List (BitVec (edgeCount 12)) :=
  missing21528_21530 ++ missing21530_21532
abbrev records21528_21532 : List Blob :=
  records21528_21530 ++ records21530_21532
theorem aligned21528_21532 :
    AlignedValid 12 4 missing21528_21532 records21528_21532 :=
  aligned21528_21530.append aligned21530_21532

def missing21532_21533 : List (BitVec (edgeCount 12)) :=
  [missing21532]
abbrev records21532_21533 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21532]
theorem aligned21532_21533 :
    AlignedValid 12 4 missing21532_21533 records21532_21533 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21532
    maskCheck21532 AlignedValid.nil

def missing21533_21534 : List (BitVec (edgeCount 12)) :=
  [missing21533]
abbrev records21533_21534 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21533]
theorem aligned21533_21534 :
    AlignedValid 12 4 missing21533_21534 records21533_21534 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21533
    maskCheck21533 AlignedValid.nil

def missing21532_21534 : List (BitVec (edgeCount 12)) :=
  missing21532_21533 ++ missing21533_21534
abbrev records21532_21534 : List Blob :=
  records21532_21533 ++ records21533_21534
theorem aligned21532_21534 :
    AlignedValid 12 4 missing21532_21534 records21532_21534 :=
  aligned21532_21533.append aligned21533_21534

def missing21534_21535 : List (BitVec (edgeCount 12)) :=
  [missing21534]
abbrev records21534_21535 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21534]
theorem aligned21534_21535 :
    AlignedValid 12 4 missing21534_21535 records21534_21535 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21534
    maskCheck21534 AlignedValid.nil

def missing21535_21536 : List (BitVec (edgeCount 12)) :=
  [missing21535]
abbrev records21535_21536 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21535]
theorem aligned21535_21536 :
    AlignedValid 12 4 missing21535_21536 records21535_21536 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21535
    maskCheck21535 AlignedValid.nil

def missing21534_21536 : List (BitVec (edgeCount 12)) :=
  missing21534_21535 ++ missing21535_21536
abbrev records21534_21536 : List Blob :=
  records21534_21535 ++ records21535_21536
theorem aligned21534_21536 :
    AlignedValid 12 4 missing21534_21536 records21534_21536 :=
  aligned21534_21535.append aligned21535_21536

def missing21532_21536 : List (BitVec (edgeCount 12)) :=
  missing21532_21534 ++ missing21534_21536
abbrev records21532_21536 : List Blob :=
  records21532_21534 ++ records21534_21536
theorem aligned21532_21536 :
    AlignedValid 12 4 missing21532_21536 records21532_21536 :=
  aligned21532_21534.append aligned21534_21536

def missing21528_21536 : List (BitVec (edgeCount 12)) :=
  missing21528_21532 ++ missing21532_21536
abbrev records21528_21536 : List Blob :=
  records21528_21532 ++ records21532_21536
theorem aligned21528_21536 :
    AlignedValid 12 4 missing21528_21536 records21528_21536 :=
  aligned21528_21532.append aligned21532_21536

def missing21520_21536 : List (BitVec (edgeCount 12)) :=
  missing21520_21528 ++ missing21528_21536
abbrev records21520_21536 : List Blob :=
  records21520_21528 ++ records21528_21536
theorem aligned21520_21536 :
    AlignedValid 12 4 missing21520_21536 records21520_21536 :=
  aligned21520_21528.append aligned21528_21536

def missing21504_21536 : List (BitVec (edgeCount 12)) :=
  missing21504_21520 ++ missing21520_21536
abbrev records21504_21536 : List Blob :=
  records21504_21520 ++ records21520_21536
theorem aligned21504_21536 :
    AlignedValid 12 4 missing21504_21536 records21504_21536 :=
  aligned21504_21520.append aligned21520_21536

def missing21536_21537 : List (BitVec (edgeCount 12)) :=
  [missing21536]
abbrev records21536_21537 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21536]
theorem aligned21536_21537 :
    AlignedValid 12 4 missing21536_21537 records21536_21537 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21536
    maskCheck21536 AlignedValid.nil

def missing21537_21538 : List (BitVec (edgeCount 12)) :=
  [missing21537]
abbrev records21537_21538 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21537]
theorem aligned21537_21538 :
    AlignedValid 12 4 missing21537_21538 records21537_21538 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21537
    maskCheck21537 AlignedValid.nil

def missing21536_21538 : List (BitVec (edgeCount 12)) :=
  missing21536_21537 ++ missing21537_21538
abbrev records21536_21538 : List Blob :=
  records21536_21537 ++ records21537_21538
theorem aligned21536_21538 :
    AlignedValid 12 4 missing21536_21538 records21536_21538 :=
  aligned21536_21537.append aligned21537_21538

def missing21538_21539 : List (BitVec (edgeCount 12)) :=
  [missing21538]
abbrev records21538_21539 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21538]
theorem aligned21538_21539 :
    AlignedValid 12 4 missing21538_21539 records21538_21539 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21538
    maskCheck21538 AlignedValid.nil

def missing21539_21540 : List (BitVec (edgeCount 12)) :=
  [missing21539]
abbrev records21539_21540 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21539]
theorem aligned21539_21540 :
    AlignedValid 12 4 missing21539_21540 records21539_21540 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21539
    maskCheck21539 AlignedValid.nil

def missing21538_21540 : List (BitVec (edgeCount 12)) :=
  missing21538_21539 ++ missing21539_21540
abbrev records21538_21540 : List Blob :=
  records21538_21539 ++ records21539_21540
theorem aligned21538_21540 :
    AlignedValid 12 4 missing21538_21540 records21538_21540 :=
  aligned21538_21539.append aligned21539_21540

def missing21536_21540 : List (BitVec (edgeCount 12)) :=
  missing21536_21538 ++ missing21538_21540
abbrev records21536_21540 : List Blob :=
  records21536_21538 ++ records21538_21540
theorem aligned21536_21540 :
    AlignedValid 12 4 missing21536_21540 records21536_21540 :=
  aligned21536_21538.append aligned21538_21540

def missing21540_21541 : List (BitVec (edgeCount 12)) :=
  [missing21540]
abbrev records21540_21541 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21540]
theorem aligned21540_21541 :
    AlignedValid 12 4 missing21540_21541 records21540_21541 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21540
    maskCheck21540 AlignedValid.nil

def missing21541_21542 : List (BitVec (edgeCount 12)) :=
  [missing21541]
abbrev records21541_21542 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21541]
theorem aligned21541_21542 :
    AlignedValid 12 4 missing21541_21542 records21541_21542 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21541
    maskCheck21541 AlignedValid.nil

def missing21540_21542 : List (BitVec (edgeCount 12)) :=
  missing21540_21541 ++ missing21541_21542
abbrev records21540_21542 : List Blob :=
  records21540_21541 ++ records21541_21542
theorem aligned21540_21542 :
    AlignedValid 12 4 missing21540_21542 records21540_21542 :=
  aligned21540_21541.append aligned21541_21542

def missing21542_21543 : List (BitVec (edgeCount 12)) :=
  [missing21542]
abbrev records21542_21543 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21542]
theorem aligned21542_21543 :
    AlignedValid 12 4 missing21542_21543 records21542_21543 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21542
    maskCheck21542 AlignedValid.nil

def missing21543_21544 : List (BitVec (edgeCount 12)) :=
  [missing21543]
abbrev records21543_21544 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21543]
theorem aligned21543_21544 :
    AlignedValid 12 4 missing21543_21544 records21543_21544 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21543
    maskCheck21543 AlignedValid.nil

def missing21542_21544 : List (BitVec (edgeCount 12)) :=
  missing21542_21543 ++ missing21543_21544
abbrev records21542_21544 : List Blob :=
  records21542_21543 ++ records21543_21544
theorem aligned21542_21544 :
    AlignedValid 12 4 missing21542_21544 records21542_21544 :=
  aligned21542_21543.append aligned21543_21544

def missing21540_21544 : List (BitVec (edgeCount 12)) :=
  missing21540_21542 ++ missing21542_21544
abbrev records21540_21544 : List Blob :=
  records21540_21542 ++ records21542_21544
theorem aligned21540_21544 :
    AlignedValid 12 4 missing21540_21544 records21540_21544 :=
  aligned21540_21542.append aligned21542_21544

def missing21536_21544 : List (BitVec (edgeCount 12)) :=
  missing21536_21540 ++ missing21540_21544
abbrev records21536_21544 : List Blob :=
  records21536_21540 ++ records21540_21544
theorem aligned21536_21544 :
    AlignedValid 12 4 missing21536_21544 records21536_21544 :=
  aligned21536_21540.append aligned21540_21544

def missing21544_21545 : List (BitVec (edgeCount 12)) :=
  [missing21544]
abbrev records21544_21545 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21544]
theorem aligned21544_21545 :
    AlignedValid 12 4 missing21544_21545 records21544_21545 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21544
    maskCheck21544 AlignedValid.nil

def missing21545_21546 : List (BitVec (edgeCount 12)) :=
  [missing21545]
abbrev records21545_21546 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21545]
theorem aligned21545_21546 :
    AlignedValid 12 4 missing21545_21546 records21545_21546 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21545
    maskCheck21545 AlignedValid.nil

def missing21544_21546 : List (BitVec (edgeCount 12)) :=
  missing21544_21545 ++ missing21545_21546
abbrev records21544_21546 : List Blob :=
  records21544_21545 ++ records21545_21546
theorem aligned21544_21546 :
    AlignedValid 12 4 missing21544_21546 records21544_21546 :=
  aligned21544_21545.append aligned21545_21546

def missing21546_21547 : List (BitVec (edgeCount 12)) :=
  [missing21546]
abbrev records21546_21547 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21546]
theorem aligned21546_21547 :
    AlignedValid 12 4 missing21546_21547 records21546_21547 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21546
    maskCheck21546 AlignedValid.nil

def missing21547_21548 : List (BitVec (edgeCount 12)) :=
  [missing21547]
abbrev records21547_21548 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21547]
theorem aligned21547_21548 :
    AlignedValid 12 4 missing21547_21548 records21547_21548 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21547
    maskCheck21547 AlignedValid.nil

def missing21546_21548 : List (BitVec (edgeCount 12)) :=
  missing21546_21547 ++ missing21547_21548
abbrev records21546_21548 : List Blob :=
  records21546_21547 ++ records21547_21548
theorem aligned21546_21548 :
    AlignedValid 12 4 missing21546_21548 records21546_21548 :=
  aligned21546_21547.append aligned21547_21548

def missing21544_21548 : List (BitVec (edgeCount 12)) :=
  missing21544_21546 ++ missing21546_21548
abbrev records21544_21548 : List Blob :=
  records21544_21546 ++ records21546_21548
theorem aligned21544_21548 :
    AlignedValid 12 4 missing21544_21548 records21544_21548 :=
  aligned21544_21546.append aligned21546_21548

def missing21548_21549 : List (BitVec (edgeCount 12)) :=
  [missing21548]
abbrev records21548_21549 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21548]
theorem aligned21548_21549 :
    AlignedValid 12 4 missing21548_21549 records21548_21549 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21548
    maskCheck21548 AlignedValid.nil

def missing21549_21550 : List (BitVec (edgeCount 12)) :=
  [missing21549]
abbrev records21549_21550 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21549]
theorem aligned21549_21550 :
    AlignedValid 12 4 missing21549_21550 records21549_21550 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21549
    maskCheck21549 AlignedValid.nil

def missing21548_21550 : List (BitVec (edgeCount 12)) :=
  missing21548_21549 ++ missing21549_21550
abbrev records21548_21550 : List Blob :=
  records21548_21549 ++ records21549_21550
theorem aligned21548_21550 :
    AlignedValid 12 4 missing21548_21550 records21548_21550 :=
  aligned21548_21549.append aligned21549_21550

def missing21550_21551 : List (BitVec (edgeCount 12)) :=
  [missing21550]
abbrev records21550_21551 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21550]
theorem aligned21550_21551 :
    AlignedValid 12 4 missing21550_21551 records21550_21551 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21550
    maskCheck21550 AlignedValid.nil

def missing21551_21552 : List (BitVec (edgeCount 12)) :=
  [missing21551]
abbrev records21551_21552 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21551]
theorem aligned21551_21552 :
    AlignedValid 12 4 missing21551_21552 records21551_21552 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21551
    maskCheck21551 AlignedValid.nil

def missing21550_21552 : List (BitVec (edgeCount 12)) :=
  missing21550_21551 ++ missing21551_21552
abbrev records21550_21552 : List Blob :=
  records21550_21551 ++ records21551_21552
theorem aligned21550_21552 :
    AlignedValid 12 4 missing21550_21552 records21550_21552 :=
  aligned21550_21551.append aligned21551_21552

def missing21548_21552 : List (BitVec (edgeCount 12)) :=
  missing21548_21550 ++ missing21550_21552
abbrev records21548_21552 : List Blob :=
  records21548_21550 ++ records21550_21552
theorem aligned21548_21552 :
    AlignedValid 12 4 missing21548_21552 records21548_21552 :=
  aligned21548_21550.append aligned21550_21552

def missing21544_21552 : List (BitVec (edgeCount 12)) :=
  missing21544_21548 ++ missing21548_21552
abbrev records21544_21552 : List Blob :=
  records21544_21548 ++ records21548_21552
theorem aligned21544_21552 :
    AlignedValid 12 4 missing21544_21552 records21544_21552 :=
  aligned21544_21548.append aligned21548_21552

def missing21536_21552 : List (BitVec (edgeCount 12)) :=
  missing21536_21544 ++ missing21544_21552
abbrev records21536_21552 : List Blob :=
  records21536_21544 ++ records21544_21552
theorem aligned21536_21552 :
    AlignedValid 12 4 missing21536_21552 records21536_21552 :=
  aligned21536_21544.append aligned21544_21552

def missing21552_21553 : List (BitVec (edgeCount 12)) :=
  [missing21552]
abbrev records21552_21553 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21552]
theorem aligned21552_21553 :
    AlignedValid 12 4 missing21552_21553 records21552_21553 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21552
    maskCheck21552 AlignedValid.nil

def missing21553_21554 : List (BitVec (edgeCount 12)) :=
  [missing21553]
abbrev records21553_21554 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21553]
theorem aligned21553_21554 :
    AlignedValid 12 4 missing21553_21554 records21553_21554 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21553
    maskCheck21553 AlignedValid.nil

def missing21552_21554 : List (BitVec (edgeCount 12)) :=
  missing21552_21553 ++ missing21553_21554
abbrev records21552_21554 : List Blob :=
  records21552_21553 ++ records21553_21554
theorem aligned21552_21554 :
    AlignedValid 12 4 missing21552_21554 records21552_21554 :=
  aligned21552_21553.append aligned21553_21554

def missing21554_21555 : List (BitVec (edgeCount 12)) :=
  [missing21554]
abbrev records21554_21555 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21554]
theorem aligned21554_21555 :
    AlignedValid 12 4 missing21554_21555 records21554_21555 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21554
    maskCheck21554 AlignedValid.nil

def missing21555_21556 : List (BitVec (edgeCount 12)) :=
  [missing21555]
abbrev records21555_21556 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21555]
theorem aligned21555_21556 :
    AlignedValid 12 4 missing21555_21556 records21555_21556 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21555
    maskCheck21555 AlignedValid.nil

def missing21554_21556 : List (BitVec (edgeCount 12)) :=
  missing21554_21555 ++ missing21555_21556
abbrev records21554_21556 : List Blob :=
  records21554_21555 ++ records21555_21556
theorem aligned21554_21556 :
    AlignedValid 12 4 missing21554_21556 records21554_21556 :=
  aligned21554_21555.append aligned21555_21556

def missing21552_21556 : List (BitVec (edgeCount 12)) :=
  missing21552_21554 ++ missing21554_21556
abbrev records21552_21556 : List Blob :=
  records21552_21554 ++ records21554_21556
theorem aligned21552_21556 :
    AlignedValid 12 4 missing21552_21556 records21552_21556 :=
  aligned21552_21554.append aligned21554_21556

def missing21556_21557 : List (BitVec (edgeCount 12)) :=
  [missing21556]
abbrev records21556_21557 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21556]
theorem aligned21556_21557 :
    AlignedValid 12 4 missing21556_21557 records21556_21557 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21556
    maskCheck21556 AlignedValid.nil

def missing21557_21558 : List (BitVec (edgeCount 12)) :=
  [missing21557]
abbrev records21557_21558 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21557]
theorem aligned21557_21558 :
    AlignedValid 12 4 missing21557_21558 records21557_21558 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21557
    maskCheck21557 AlignedValid.nil

def missing21556_21558 : List (BitVec (edgeCount 12)) :=
  missing21556_21557 ++ missing21557_21558
abbrev records21556_21558 : List Blob :=
  records21556_21557 ++ records21557_21558
theorem aligned21556_21558 :
    AlignedValid 12 4 missing21556_21558 records21556_21558 :=
  aligned21556_21557.append aligned21557_21558

def missing21558_21559 : List (BitVec (edgeCount 12)) :=
  [missing21558]
abbrev records21558_21559 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21558]
theorem aligned21558_21559 :
    AlignedValid 12 4 missing21558_21559 records21558_21559 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21558
    maskCheck21558 AlignedValid.nil

def missing21559_21560 : List (BitVec (edgeCount 12)) :=
  [missing21559]
abbrev records21559_21560 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21559]
theorem aligned21559_21560 :
    AlignedValid 12 4 missing21559_21560 records21559_21560 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21559
    maskCheck21559 AlignedValid.nil

def missing21558_21560 : List (BitVec (edgeCount 12)) :=
  missing21558_21559 ++ missing21559_21560
abbrev records21558_21560 : List Blob :=
  records21558_21559 ++ records21559_21560
theorem aligned21558_21560 :
    AlignedValid 12 4 missing21558_21560 records21558_21560 :=
  aligned21558_21559.append aligned21559_21560

def missing21556_21560 : List (BitVec (edgeCount 12)) :=
  missing21556_21558 ++ missing21558_21560
abbrev records21556_21560 : List Blob :=
  records21556_21558 ++ records21558_21560
theorem aligned21556_21560 :
    AlignedValid 12 4 missing21556_21560 records21556_21560 :=
  aligned21556_21558.append aligned21558_21560

def missing21552_21560 : List (BitVec (edgeCount 12)) :=
  missing21552_21556 ++ missing21556_21560
abbrev records21552_21560 : List Blob :=
  records21552_21556 ++ records21556_21560
theorem aligned21552_21560 :
    AlignedValid 12 4 missing21552_21560 records21552_21560 :=
  aligned21552_21556.append aligned21556_21560

def missing21560_21561 : List (BitVec (edgeCount 12)) :=
  [missing21560]
abbrev records21560_21561 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21560]
theorem aligned21560_21561 :
    AlignedValid 12 4 missing21560_21561 records21560_21561 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21560
    maskCheck21560 AlignedValid.nil

def missing21561_21562 : List (BitVec (edgeCount 12)) :=
  [missing21561]
abbrev records21561_21562 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21561]
theorem aligned21561_21562 :
    AlignedValid 12 4 missing21561_21562 records21561_21562 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21561
    maskCheck21561 AlignedValid.nil

def missing21560_21562 : List (BitVec (edgeCount 12)) :=
  missing21560_21561 ++ missing21561_21562
abbrev records21560_21562 : List Blob :=
  records21560_21561 ++ records21561_21562
theorem aligned21560_21562 :
    AlignedValid 12 4 missing21560_21562 records21560_21562 :=
  aligned21560_21561.append aligned21561_21562

def missing21562_21563 : List (BitVec (edgeCount 12)) :=
  [missing21562]
abbrev records21562_21563 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21562]
theorem aligned21562_21563 :
    AlignedValid 12 4 missing21562_21563 records21562_21563 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21562
    maskCheck21562 AlignedValid.nil

def missing21563_21564 : List (BitVec (edgeCount 12)) :=
  [missing21563]
abbrev records21563_21564 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21563]
theorem aligned21563_21564 :
    AlignedValid 12 4 missing21563_21564 records21563_21564 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21563
    maskCheck21563 AlignedValid.nil

def missing21562_21564 : List (BitVec (edgeCount 12)) :=
  missing21562_21563 ++ missing21563_21564
abbrev records21562_21564 : List Blob :=
  records21562_21563 ++ records21563_21564
theorem aligned21562_21564 :
    AlignedValid 12 4 missing21562_21564 records21562_21564 :=
  aligned21562_21563.append aligned21563_21564

def missing21560_21564 : List (BitVec (edgeCount 12)) :=
  missing21560_21562 ++ missing21562_21564
abbrev records21560_21564 : List Blob :=
  records21560_21562 ++ records21562_21564
theorem aligned21560_21564 :
    AlignedValid 12 4 missing21560_21564 records21560_21564 :=
  aligned21560_21562.append aligned21562_21564

def missing21564_21565 : List (BitVec (edgeCount 12)) :=
  [missing21564]
abbrev records21564_21565 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21564]
theorem aligned21564_21565 :
    AlignedValid 12 4 missing21564_21565 records21564_21565 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21564
    maskCheck21564 AlignedValid.nil

def missing21565_21566 : List (BitVec (edgeCount 12)) :=
  [missing21565]
abbrev records21565_21566 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21565]
theorem aligned21565_21566 :
    AlignedValid 12 4 missing21565_21566 records21565_21566 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21565
    maskCheck21565 AlignedValid.nil

def missing21564_21566 : List (BitVec (edgeCount 12)) :=
  missing21564_21565 ++ missing21565_21566
abbrev records21564_21566 : List Blob :=
  records21564_21565 ++ records21565_21566
theorem aligned21564_21566 :
    AlignedValid 12 4 missing21564_21566 records21564_21566 :=
  aligned21564_21565.append aligned21565_21566

def missing21566_21567 : List (BitVec (edgeCount 12)) :=
  [missing21566]
abbrev records21566_21567 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21566]
theorem aligned21566_21567 :
    AlignedValid 12 4 missing21566_21567 records21566_21567 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21566
    maskCheck21566 AlignedValid.nil

def missing21567_21568 : List (BitVec (edgeCount 12)) :=
  [missing21567]
abbrev records21567_21568 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21567]
theorem aligned21567_21568 :
    AlignedValid 12 4 missing21567_21568 records21567_21568 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21567
    maskCheck21567 AlignedValid.nil

def missing21566_21568 : List (BitVec (edgeCount 12)) :=
  missing21566_21567 ++ missing21567_21568
abbrev records21566_21568 : List Blob :=
  records21566_21567 ++ records21567_21568
theorem aligned21566_21568 :
    AlignedValid 12 4 missing21566_21568 records21566_21568 :=
  aligned21566_21567.append aligned21567_21568

def missing21564_21568 : List (BitVec (edgeCount 12)) :=
  missing21564_21566 ++ missing21566_21568
abbrev records21564_21568 : List Blob :=
  records21564_21566 ++ records21566_21568
theorem aligned21564_21568 :
    AlignedValid 12 4 missing21564_21568 records21564_21568 :=
  aligned21564_21566.append aligned21566_21568

def missing21560_21568 : List (BitVec (edgeCount 12)) :=
  missing21560_21564 ++ missing21564_21568
abbrev records21560_21568 : List Blob :=
  records21560_21564 ++ records21564_21568
theorem aligned21560_21568 :
    AlignedValid 12 4 missing21560_21568 records21560_21568 :=
  aligned21560_21564.append aligned21564_21568

def missing21552_21568 : List (BitVec (edgeCount 12)) :=
  missing21552_21560 ++ missing21560_21568
abbrev records21552_21568 : List Blob :=
  records21552_21560 ++ records21560_21568
theorem aligned21552_21568 :
    AlignedValid 12 4 missing21552_21568 records21552_21568 :=
  aligned21552_21560.append aligned21560_21568

def missing21536_21568 : List (BitVec (edgeCount 12)) :=
  missing21536_21552 ++ missing21552_21568
abbrev records21536_21568 : List Blob :=
  records21536_21552 ++ records21552_21568
theorem aligned21536_21568 :
    AlignedValid 12 4 missing21536_21568 records21536_21568 :=
  aligned21536_21552.append aligned21552_21568

def missing21504_21568 : List (BitVec (edgeCount 12)) :=
  missing21504_21536 ++ missing21536_21568
abbrev records21504_21568 : List Blob :=
  records21504_21536 ++ records21536_21568
theorem aligned21504_21568 :
    AlignedValid 12 4 missing21504_21568 records21504_21568 :=
  aligned21504_21536.append aligned21536_21568

def missing21568_21569 : List (BitVec (edgeCount 12)) :=
  [missing21568]
abbrev records21568_21569 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21568]
theorem aligned21568_21569 :
    AlignedValid 12 4 missing21568_21569 records21568_21569 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21568
    maskCheck21568 AlignedValid.nil

def missing21569_21570 : List (BitVec (edgeCount 12)) :=
  [missing21569]
abbrev records21569_21570 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21569]
theorem aligned21569_21570 :
    AlignedValid 12 4 missing21569_21570 records21569_21570 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21569
    maskCheck21569 AlignedValid.nil

def missing21568_21570 : List (BitVec (edgeCount 12)) :=
  missing21568_21569 ++ missing21569_21570
abbrev records21568_21570 : List Blob :=
  records21568_21569 ++ records21569_21570
theorem aligned21568_21570 :
    AlignedValid 12 4 missing21568_21570 records21568_21570 :=
  aligned21568_21569.append aligned21569_21570

def missing21570_21571 : List (BitVec (edgeCount 12)) :=
  [missing21570]
abbrev records21570_21571 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21570]
theorem aligned21570_21571 :
    AlignedValid 12 4 missing21570_21571 records21570_21571 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21570
    maskCheck21570 AlignedValid.nil

def missing21571_21572 : List (BitVec (edgeCount 12)) :=
  [missing21571]
abbrev records21571_21572 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21571]
theorem aligned21571_21572 :
    AlignedValid 12 4 missing21571_21572 records21571_21572 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21571
    maskCheck21571 AlignedValid.nil

def missing21570_21572 : List (BitVec (edgeCount 12)) :=
  missing21570_21571 ++ missing21571_21572
abbrev records21570_21572 : List Blob :=
  records21570_21571 ++ records21571_21572
theorem aligned21570_21572 :
    AlignedValid 12 4 missing21570_21572 records21570_21572 :=
  aligned21570_21571.append aligned21571_21572

def missing21568_21572 : List (BitVec (edgeCount 12)) :=
  missing21568_21570 ++ missing21570_21572
abbrev records21568_21572 : List Blob :=
  records21568_21570 ++ records21570_21572
theorem aligned21568_21572 :
    AlignedValid 12 4 missing21568_21572 records21568_21572 :=
  aligned21568_21570.append aligned21570_21572

def missing21572_21573 : List (BitVec (edgeCount 12)) :=
  [missing21572]
abbrev records21572_21573 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21572]
theorem aligned21572_21573 :
    AlignedValid 12 4 missing21572_21573 records21572_21573 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21572
    maskCheck21572 AlignedValid.nil

def missing21573_21574 : List (BitVec (edgeCount 12)) :=
  [missing21573]
abbrev records21573_21574 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21573]
theorem aligned21573_21574 :
    AlignedValid 12 4 missing21573_21574 records21573_21574 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21573
    maskCheck21573 AlignedValid.nil

def missing21572_21574 : List (BitVec (edgeCount 12)) :=
  missing21572_21573 ++ missing21573_21574
abbrev records21572_21574 : List Blob :=
  records21572_21573 ++ records21573_21574
theorem aligned21572_21574 :
    AlignedValid 12 4 missing21572_21574 records21572_21574 :=
  aligned21572_21573.append aligned21573_21574

def missing21574_21575 : List (BitVec (edgeCount 12)) :=
  [missing21574]
abbrev records21574_21575 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21574]
theorem aligned21574_21575 :
    AlignedValid 12 4 missing21574_21575 records21574_21575 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21574
    maskCheck21574 AlignedValid.nil

def missing21575_21576 : List (BitVec (edgeCount 12)) :=
  [missing21575]
abbrev records21575_21576 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21575]
theorem aligned21575_21576 :
    AlignedValid 12 4 missing21575_21576 records21575_21576 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21575
    maskCheck21575 AlignedValid.nil

def missing21574_21576 : List (BitVec (edgeCount 12)) :=
  missing21574_21575 ++ missing21575_21576
abbrev records21574_21576 : List Blob :=
  records21574_21575 ++ records21575_21576
theorem aligned21574_21576 :
    AlignedValid 12 4 missing21574_21576 records21574_21576 :=
  aligned21574_21575.append aligned21575_21576

def missing21572_21576 : List (BitVec (edgeCount 12)) :=
  missing21572_21574 ++ missing21574_21576
abbrev records21572_21576 : List Blob :=
  records21572_21574 ++ records21574_21576
theorem aligned21572_21576 :
    AlignedValid 12 4 missing21572_21576 records21572_21576 :=
  aligned21572_21574.append aligned21574_21576

def missing21568_21576 : List (BitVec (edgeCount 12)) :=
  missing21568_21572 ++ missing21572_21576
abbrev records21568_21576 : List Blob :=
  records21568_21572 ++ records21572_21576
theorem aligned21568_21576 :
    AlignedValid 12 4 missing21568_21576 records21568_21576 :=
  aligned21568_21572.append aligned21572_21576

def missing21576_21577 : List (BitVec (edgeCount 12)) :=
  [missing21576]
abbrev records21576_21577 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21576]
theorem aligned21576_21577 :
    AlignedValid 12 4 missing21576_21577 records21576_21577 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21576
    maskCheck21576 AlignedValid.nil

def missing21577_21578 : List (BitVec (edgeCount 12)) :=
  [missing21577]
abbrev records21577_21578 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21577]
theorem aligned21577_21578 :
    AlignedValid 12 4 missing21577_21578 records21577_21578 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21577
    maskCheck21577 AlignedValid.nil

def missing21576_21578 : List (BitVec (edgeCount 12)) :=
  missing21576_21577 ++ missing21577_21578
abbrev records21576_21578 : List Blob :=
  records21576_21577 ++ records21577_21578
theorem aligned21576_21578 :
    AlignedValid 12 4 missing21576_21578 records21576_21578 :=
  aligned21576_21577.append aligned21577_21578

def missing21578_21579 : List (BitVec (edgeCount 12)) :=
  [missing21578]
abbrev records21578_21579 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21578]
theorem aligned21578_21579 :
    AlignedValid 12 4 missing21578_21579 records21578_21579 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21578
    maskCheck21578 AlignedValid.nil

def missing21579_21580 : List (BitVec (edgeCount 12)) :=
  [missing21579]
abbrev records21579_21580 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21579]
theorem aligned21579_21580 :
    AlignedValid 12 4 missing21579_21580 records21579_21580 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21579
    maskCheck21579 AlignedValid.nil

def missing21578_21580 : List (BitVec (edgeCount 12)) :=
  missing21578_21579 ++ missing21579_21580
abbrev records21578_21580 : List Blob :=
  records21578_21579 ++ records21579_21580
theorem aligned21578_21580 :
    AlignedValid 12 4 missing21578_21580 records21578_21580 :=
  aligned21578_21579.append aligned21579_21580

def missing21576_21580 : List (BitVec (edgeCount 12)) :=
  missing21576_21578 ++ missing21578_21580
abbrev records21576_21580 : List Blob :=
  records21576_21578 ++ records21578_21580
theorem aligned21576_21580 :
    AlignedValid 12 4 missing21576_21580 records21576_21580 :=
  aligned21576_21578.append aligned21578_21580

def missing21580_21581 : List (BitVec (edgeCount 12)) :=
  [missing21580]
abbrev records21580_21581 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21580]
theorem aligned21580_21581 :
    AlignedValid 12 4 missing21580_21581 records21580_21581 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21580
    maskCheck21580 AlignedValid.nil

def missing21581_21582 : List (BitVec (edgeCount 12)) :=
  [missing21581]
abbrev records21581_21582 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21581]
theorem aligned21581_21582 :
    AlignedValid 12 4 missing21581_21582 records21581_21582 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21581
    maskCheck21581 AlignedValid.nil

def missing21580_21582 : List (BitVec (edgeCount 12)) :=
  missing21580_21581 ++ missing21581_21582
abbrev records21580_21582 : List Blob :=
  records21580_21581 ++ records21581_21582
theorem aligned21580_21582 :
    AlignedValid 12 4 missing21580_21582 records21580_21582 :=
  aligned21580_21581.append aligned21581_21582

def missing21582_21583 : List (BitVec (edgeCount 12)) :=
  [missing21582]
abbrev records21582_21583 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21582]
theorem aligned21582_21583 :
    AlignedValid 12 4 missing21582_21583 records21582_21583 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21582
    maskCheck21582 AlignedValid.nil

def missing21583_21584 : List (BitVec (edgeCount 12)) :=
  [missing21583]
abbrev records21583_21584 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21583]
theorem aligned21583_21584 :
    AlignedValid 12 4 missing21583_21584 records21583_21584 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21583
    maskCheck21583 AlignedValid.nil

def missing21582_21584 : List (BitVec (edgeCount 12)) :=
  missing21582_21583 ++ missing21583_21584
abbrev records21582_21584 : List Blob :=
  records21582_21583 ++ records21583_21584
theorem aligned21582_21584 :
    AlignedValid 12 4 missing21582_21584 records21582_21584 :=
  aligned21582_21583.append aligned21583_21584

def missing21580_21584 : List (BitVec (edgeCount 12)) :=
  missing21580_21582 ++ missing21582_21584
abbrev records21580_21584 : List Blob :=
  records21580_21582 ++ records21582_21584
theorem aligned21580_21584 :
    AlignedValid 12 4 missing21580_21584 records21580_21584 :=
  aligned21580_21582.append aligned21582_21584

def missing21576_21584 : List (BitVec (edgeCount 12)) :=
  missing21576_21580 ++ missing21580_21584
abbrev records21576_21584 : List Blob :=
  records21576_21580 ++ records21580_21584
theorem aligned21576_21584 :
    AlignedValid 12 4 missing21576_21584 records21576_21584 :=
  aligned21576_21580.append aligned21580_21584

def missing21568_21584 : List (BitVec (edgeCount 12)) :=
  missing21568_21576 ++ missing21576_21584
abbrev records21568_21584 : List Blob :=
  records21568_21576 ++ records21576_21584
theorem aligned21568_21584 :
    AlignedValid 12 4 missing21568_21584 records21568_21584 :=
  aligned21568_21576.append aligned21576_21584

def missing21584_21585 : List (BitVec (edgeCount 12)) :=
  [missing21584]
abbrev records21584_21585 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21584]
theorem aligned21584_21585 :
    AlignedValid 12 4 missing21584_21585 records21584_21585 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21584
    maskCheck21584 AlignedValid.nil

def missing21585_21586 : List (BitVec (edgeCount 12)) :=
  [missing21585]
abbrev records21585_21586 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21585]
theorem aligned21585_21586 :
    AlignedValid 12 4 missing21585_21586 records21585_21586 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21585
    maskCheck21585 AlignedValid.nil

def missing21584_21586 : List (BitVec (edgeCount 12)) :=
  missing21584_21585 ++ missing21585_21586
abbrev records21584_21586 : List Blob :=
  records21584_21585 ++ records21585_21586
theorem aligned21584_21586 :
    AlignedValid 12 4 missing21584_21586 records21584_21586 :=
  aligned21584_21585.append aligned21585_21586

def missing21586_21587 : List (BitVec (edgeCount 12)) :=
  [missing21586]
abbrev records21586_21587 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21586]
theorem aligned21586_21587 :
    AlignedValid 12 4 missing21586_21587 records21586_21587 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21586
    maskCheck21586 AlignedValid.nil

def missing21587_21588 : List (BitVec (edgeCount 12)) :=
  [missing21587]
abbrev records21587_21588 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21587]
theorem aligned21587_21588 :
    AlignedValid 12 4 missing21587_21588 records21587_21588 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21587
    maskCheck21587 AlignedValid.nil

def missing21586_21588 : List (BitVec (edgeCount 12)) :=
  missing21586_21587 ++ missing21587_21588
abbrev records21586_21588 : List Blob :=
  records21586_21587 ++ records21587_21588
theorem aligned21586_21588 :
    AlignedValid 12 4 missing21586_21588 records21586_21588 :=
  aligned21586_21587.append aligned21587_21588

def missing21584_21588 : List (BitVec (edgeCount 12)) :=
  missing21584_21586 ++ missing21586_21588
abbrev records21584_21588 : List Blob :=
  records21584_21586 ++ records21586_21588
theorem aligned21584_21588 :
    AlignedValid 12 4 missing21584_21588 records21584_21588 :=
  aligned21584_21586.append aligned21586_21588

def missing21588_21589 : List (BitVec (edgeCount 12)) :=
  [missing21588]
abbrev records21588_21589 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21588]
theorem aligned21588_21589 :
    AlignedValid 12 4 missing21588_21589 records21588_21589 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21588
    maskCheck21588 AlignedValid.nil

def missing21589_21590 : List (BitVec (edgeCount 12)) :=
  [missing21589]
abbrev records21589_21590 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21589]
theorem aligned21589_21590 :
    AlignedValid 12 4 missing21589_21590 records21589_21590 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21589
    maskCheck21589 AlignedValid.nil

def missing21588_21590 : List (BitVec (edgeCount 12)) :=
  missing21588_21589 ++ missing21589_21590
abbrev records21588_21590 : List Blob :=
  records21588_21589 ++ records21589_21590
theorem aligned21588_21590 :
    AlignedValid 12 4 missing21588_21590 records21588_21590 :=
  aligned21588_21589.append aligned21589_21590

def missing21590_21591 : List (BitVec (edgeCount 12)) :=
  [missing21590]
abbrev records21590_21591 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21590]
theorem aligned21590_21591 :
    AlignedValid 12 4 missing21590_21591 records21590_21591 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21590
    maskCheck21590 AlignedValid.nil

def missing21591_21592 : List (BitVec (edgeCount 12)) :=
  [missing21591]
abbrev records21591_21592 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21591]
theorem aligned21591_21592 :
    AlignedValid 12 4 missing21591_21592 records21591_21592 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21591
    maskCheck21591 AlignedValid.nil

def missing21590_21592 : List (BitVec (edgeCount 12)) :=
  missing21590_21591 ++ missing21591_21592
abbrev records21590_21592 : List Blob :=
  records21590_21591 ++ records21591_21592
theorem aligned21590_21592 :
    AlignedValid 12 4 missing21590_21592 records21590_21592 :=
  aligned21590_21591.append aligned21591_21592

def missing21588_21592 : List (BitVec (edgeCount 12)) :=
  missing21588_21590 ++ missing21590_21592
abbrev records21588_21592 : List Blob :=
  records21588_21590 ++ records21590_21592
theorem aligned21588_21592 :
    AlignedValid 12 4 missing21588_21592 records21588_21592 :=
  aligned21588_21590.append aligned21590_21592

def missing21584_21592 : List (BitVec (edgeCount 12)) :=
  missing21584_21588 ++ missing21588_21592
abbrev records21584_21592 : List Blob :=
  records21584_21588 ++ records21588_21592
theorem aligned21584_21592 :
    AlignedValid 12 4 missing21584_21592 records21584_21592 :=
  aligned21584_21588.append aligned21588_21592

def missing21592_21593 : List (BitVec (edgeCount 12)) :=
  [missing21592]
abbrev records21592_21593 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21592]
theorem aligned21592_21593 :
    AlignedValid 12 4 missing21592_21593 records21592_21593 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21592
    maskCheck21592 AlignedValid.nil

def missing21593_21594 : List (BitVec (edgeCount 12)) :=
  [missing21593]
abbrev records21593_21594 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21593]
theorem aligned21593_21594 :
    AlignedValid 12 4 missing21593_21594 records21593_21594 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21593
    maskCheck21593 AlignedValid.nil

def missing21592_21594 : List (BitVec (edgeCount 12)) :=
  missing21592_21593 ++ missing21593_21594
abbrev records21592_21594 : List Blob :=
  records21592_21593 ++ records21593_21594
theorem aligned21592_21594 :
    AlignedValid 12 4 missing21592_21594 records21592_21594 :=
  aligned21592_21593.append aligned21593_21594

def missing21594_21595 : List (BitVec (edgeCount 12)) :=
  [missing21594]
abbrev records21594_21595 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21594]
theorem aligned21594_21595 :
    AlignedValid 12 4 missing21594_21595 records21594_21595 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21594
    maskCheck21594 AlignedValid.nil

def missing21595_21596 : List (BitVec (edgeCount 12)) :=
  [missing21595]
abbrev records21595_21596 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21595]
theorem aligned21595_21596 :
    AlignedValid 12 4 missing21595_21596 records21595_21596 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21595
    maskCheck21595 AlignedValid.nil

def missing21594_21596 : List (BitVec (edgeCount 12)) :=
  missing21594_21595 ++ missing21595_21596
abbrev records21594_21596 : List Blob :=
  records21594_21595 ++ records21595_21596
theorem aligned21594_21596 :
    AlignedValid 12 4 missing21594_21596 records21594_21596 :=
  aligned21594_21595.append aligned21595_21596

def missing21592_21596 : List (BitVec (edgeCount 12)) :=
  missing21592_21594 ++ missing21594_21596
abbrev records21592_21596 : List Blob :=
  records21592_21594 ++ records21594_21596
theorem aligned21592_21596 :
    AlignedValid 12 4 missing21592_21596 records21592_21596 :=
  aligned21592_21594.append aligned21594_21596

def missing21596_21597 : List (BitVec (edgeCount 12)) :=
  [missing21596]
abbrev records21596_21597 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21596]
theorem aligned21596_21597 :
    AlignedValid 12 4 missing21596_21597 records21596_21597 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21596
    maskCheck21596 AlignedValid.nil

def missing21597_21598 : List (BitVec (edgeCount 12)) :=
  [missing21597]
abbrev records21597_21598 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21597]
theorem aligned21597_21598 :
    AlignedValid 12 4 missing21597_21598 records21597_21598 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21597
    maskCheck21597 AlignedValid.nil

def missing21596_21598 : List (BitVec (edgeCount 12)) :=
  missing21596_21597 ++ missing21597_21598
abbrev records21596_21598 : List Blob :=
  records21596_21597 ++ records21597_21598
theorem aligned21596_21598 :
    AlignedValid 12 4 missing21596_21598 records21596_21598 :=
  aligned21596_21597.append aligned21597_21598

def missing21598_21599 : List (BitVec (edgeCount 12)) :=
  [missing21598]
abbrev records21598_21599 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21598]
theorem aligned21598_21599 :
    AlignedValid 12 4 missing21598_21599 records21598_21599 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21598
    maskCheck21598 AlignedValid.nil

def missing21599_21600 : List (BitVec (edgeCount 12)) :=
  [missing21599]
abbrev records21599_21600 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21599]
theorem aligned21599_21600 :
    AlignedValid 12 4 missing21599_21600 records21599_21600 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21599
    maskCheck21599 AlignedValid.nil

def missing21598_21600 : List (BitVec (edgeCount 12)) :=
  missing21598_21599 ++ missing21599_21600
abbrev records21598_21600 : List Blob :=
  records21598_21599 ++ records21599_21600
theorem aligned21598_21600 :
    AlignedValid 12 4 missing21598_21600 records21598_21600 :=
  aligned21598_21599.append aligned21599_21600

def missing21596_21600 : List (BitVec (edgeCount 12)) :=
  missing21596_21598 ++ missing21598_21600
abbrev records21596_21600 : List Blob :=
  records21596_21598 ++ records21598_21600
theorem aligned21596_21600 :
    AlignedValid 12 4 missing21596_21600 records21596_21600 :=
  aligned21596_21598.append aligned21598_21600

def missing21592_21600 : List (BitVec (edgeCount 12)) :=
  missing21592_21596 ++ missing21596_21600
abbrev records21592_21600 : List Blob :=
  records21592_21596 ++ records21596_21600
theorem aligned21592_21600 :
    AlignedValid 12 4 missing21592_21600 records21592_21600 :=
  aligned21592_21596.append aligned21596_21600

def missing21584_21600 : List (BitVec (edgeCount 12)) :=
  missing21584_21592 ++ missing21592_21600
abbrev records21584_21600 : List Blob :=
  records21584_21592 ++ records21592_21600
theorem aligned21584_21600 :
    AlignedValid 12 4 missing21584_21600 records21584_21600 :=
  aligned21584_21592.append aligned21592_21600

def missing21568_21600 : List (BitVec (edgeCount 12)) :=
  missing21568_21584 ++ missing21584_21600
abbrev records21568_21600 : List Blob :=
  records21568_21584 ++ records21584_21600
theorem aligned21568_21600 :
    AlignedValid 12 4 missing21568_21600 records21568_21600 :=
  aligned21568_21584.append aligned21584_21600

def missing21600_21601 : List (BitVec (edgeCount 12)) :=
  [missing21600]
abbrev records21600_21601 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21600]
theorem aligned21600_21601 :
    AlignedValid 12 4 missing21600_21601 records21600_21601 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21600
    maskCheck21600 AlignedValid.nil

def missing21601_21602 : List (BitVec (edgeCount 12)) :=
  [missing21601]
abbrev records21601_21602 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21601]
theorem aligned21601_21602 :
    AlignedValid 12 4 missing21601_21602 records21601_21602 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21601
    maskCheck21601 AlignedValid.nil

def missing21600_21602 : List (BitVec (edgeCount 12)) :=
  missing21600_21601 ++ missing21601_21602
abbrev records21600_21602 : List Blob :=
  records21600_21601 ++ records21601_21602
theorem aligned21600_21602 :
    AlignedValid 12 4 missing21600_21602 records21600_21602 :=
  aligned21600_21601.append aligned21601_21602

def missing21602_21603 : List (BitVec (edgeCount 12)) :=
  [missing21602]
abbrev records21602_21603 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21602]
theorem aligned21602_21603 :
    AlignedValid 12 4 missing21602_21603 records21602_21603 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21602
    maskCheck21602 AlignedValid.nil

def missing21603_21604 : List (BitVec (edgeCount 12)) :=
  [missing21603]
abbrev records21603_21604 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21603]
theorem aligned21603_21604 :
    AlignedValid 12 4 missing21603_21604 records21603_21604 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21603
    maskCheck21603 AlignedValid.nil

def missing21602_21604 : List (BitVec (edgeCount 12)) :=
  missing21602_21603 ++ missing21603_21604
abbrev records21602_21604 : List Blob :=
  records21602_21603 ++ records21603_21604
theorem aligned21602_21604 :
    AlignedValid 12 4 missing21602_21604 records21602_21604 :=
  aligned21602_21603.append aligned21603_21604

def missing21600_21604 : List (BitVec (edgeCount 12)) :=
  missing21600_21602 ++ missing21602_21604
abbrev records21600_21604 : List Blob :=
  records21600_21602 ++ records21602_21604
theorem aligned21600_21604 :
    AlignedValid 12 4 missing21600_21604 records21600_21604 :=
  aligned21600_21602.append aligned21602_21604

def missing21604_21605 : List (BitVec (edgeCount 12)) :=
  [missing21604]
abbrev records21604_21605 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21604]
theorem aligned21604_21605 :
    AlignedValid 12 4 missing21604_21605 records21604_21605 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21604
    maskCheck21604 AlignedValid.nil

def missing21605_21606 : List (BitVec (edgeCount 12)) :=
  [missing21605]
abbrev records21605_21606 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21605]
theorem aligned21605_21606 :
    AlignedValid 12 4 missing21605_21606 records21605_21606 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21605
    maskCheck21605 AlignedValid.nil

def missing21604_21606 : List (BitVec (edgeCount 12)) :=
  missing21604_21605 ++ missing21605_21606
abbrev records21604_21606 : List Blob :=
  records21604_21605 ++ records21605_21606
theorem aligned21604_21606 :
    AlignedValid 12 4 missing21604_21606 records21604_21606 :=
  aligned21604_21605.append aligned21605_21606

def missing21606_21607 : List (BitVec (edgeCount 12)) :=
  [missing21606]
abbrev records21606_21607 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21606]
theorem aligned21606_21607 :
    AlignedValid 12 4 missing21606_21607 records21606_21607 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21606
    maskCheck21606 AlignedValid.nil

def missing21607_21608 : List (BitVec (edgeCount 12)) :=
  [missing21607]
abbrev records21607_21608 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21607]
theorem aligned21607_21608 :
    AlignedValid 12 4 missing21607_21608 records21607_21608 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21607
    maskCheck21607 AlignedValid.nil

def missing21606_21608 : List (BitVec (edgeCount 12)) :=
  missing21606_21607 ++ missing21607_21608
abbrev records21606_21608 : List Blob :=
  records21606_21607 ++ records21607_21608
theorem aligned21606_21608 :
    AlignedValid 12 4 missing21606_21608 records21606_21608 :=
  aligned21606_21607.append aligned21607_21608

def missing21604_21608 : List (BitVec (edgeCount 12)) :=
  missing21604_21606 ++ missing21606_21608
abbrev records21604_21608 : List Blob :=
  records21604_21606 ++ records21606_21608
theorem aligned21604_21608 :
    AlignedValid 12 4 missing21604_21608 records21604_21608 :=
  aligned21604_21606.append aligned21606_21608

def missing21600_21608 : List (BitVec (edgeCount 12)) :=
  missing21600_21604 ++ missing21604_21608
abbrev records21600_21608 : List Blob :=
  records21600_21604 ++ records21604_21608
theorem aligned21600_21608 :
    AlignedValid 12 4 missing21600_21608 records21600_21608 :=
  aligned21600_21604.append aligned21604_21608

def missing21608_21609 : List (BitVec (edgeCount 12)) :=
  [missing21608]
abbrev records21608_21609 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21608]
theorem aligned21608_21609 :
    AlignedValid 12 4 missing21608_21609 records21608_21609 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21608
    maskCheck21608 AlignedValid.nil

def missing21609_21610 : List (BitVec (edgeCount 12)) :=
  [missing21609]
abbrev records21609_21610 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21609]
theorem aligned21609_21610 :
    AlignedValid 12 4 missing21609_21610 records21609_21610 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21609
    maskCheck21609 AlignedValid.nil

def missing21608_21610 : List (BitVec (edgeCount 12)) :=
  missing21608_21609 ++ missing21609_21610
abbrev records21608_21610 : List Blob :=
  records21608_21609 ++ records21609_21610
theorem aligned21608_21610 :
    AlignedValid 12 4 missing21608_21610 records21608_21610 :=
  aligned21608_21609.append aligned21609_21610

def missing21610_21611 : List (BitVec (edgeCount 12)) :=
  [missing21610]
abbrev records21610_21611 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21610]
theorem aligned21610_21611 :
    AlignedValid 12 4 missing21610_21611 records21610_21611 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21610
    maskCheck21610 AlignedValid.nil

def missing21611_21612 : List (BitVec (edgeCount 12)) :=
  [missing21611]
abbrev records21611_21612 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21611]
theorem aligned21611_21612 :
    AlignedValid 12 4 missing21611_21612 records21611_21612 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21611
    maskCheck21611 AlignedValid.nil

def missing21610_21612 : List (BitVec (edgeCount 12)) :=
  missing21610_21611 ++ missing21611_21612
abbrev records21610_21612 : List Blob :=
  records21610_21611 ++ records21611_21612
theorem aligned21610_21612 :
    AlignedValid 12 4 missing21610_21612 records21610_21612 :=
  aligned21610_21611.append aligned21611_21612

def missing21608_21612 : List (BitVec (edgeCount 12)) :=
  missing21608_21610 ++ missing21610_21612
abbrev records21608_21612 : List Blob :=
  records21608_21610 ++ records21610_21612
theorem aligned21608_21612 :
    AlignedValid 12 4 missing21608_21612 records21608_21612 :=
  aligned21608_21610.append aligned21610_21612

def missing21612_21613 : List (BitVec (edgeCount 12)) :=
  [missing21612]
abbrev records21612_21613 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21612]
theorem aligned21612_21613 :
    AlignedValid 12 4 missing21612_21613 records21612_21613 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21612
    maskCheck21612 AlignedValid.nil

def missing21613_21614 : List (BitVec (edgeCount 12)) :=
  [missing21613]
abbrev records21613_21614 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21613]
theorem aligned21613_21614 :
    AlignedValid 12 4 missing21613_21614 records21613_21614 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21613
    maskCheck21613 AlignedValid.nil

def missing21612_21614 : List (BitVec (edgeCount 12)) :=
  missing21612_21613 ++ missing21613_21614
abbrev records21612_21614 : List Blob :=
  records21612_21613 ++ records21613_21614
theorem aligned21612_21614 :
    AlignedValid 12 4 missing21612_21614 records21612_21614 :=
  aligned21612_21613.append aligned21613_21614

def missing21614_21615 : List (BitVec (edgeCount 12)) :=
  [missing21614]
abbrev records21614_21615 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21614]
theorem aligned21614_21615 :
    AlignedValid 12 4 missing21614_21615 records21614_21615 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21614
    maskCheck21614 AlignedValid.nil

def missing21615_21616 : List (BitVec (edgeCount 12)) :=
  [missing21615]
abbrev records21615_21616 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21615]
theorem aligned21615_21616 :
    AlignedValid 12 4 missing21615_21616 records21615_21616 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21615
    maskCheck21615 AlignedValid.nil

def missing21614_21616 : List (BitVec (edgeCount 12)) :=
  missing21614_21615 ++ missing21615_21616
abbrev records21614_21616 : List Blob :=
  records21614_21615 ++ records21615_21616
theorem aligned21614_21616 :
    AlignedValid 12 4 missing21614_21616 records21614_21616 :=
  aligned21614_21615.append aligned21615_21616

def missing21612_21616 : List (BitVec (edgeCount 12)) :=
  missing21612_21614 ++ missing21614_21616
abbrev records21612_21616 : List Blob :=
  records21612_21614 ++ records21614_21616
theorem aligned21612_21616 :
    AlignedValid 12 4 missing21612_21616 records21612_21616 :=
  aligned21612_21614.append aligned21614_21616

def missing21608_21616 : List (BitVec (edgeCount 12)) :=
  missing21608_21612 ++ missing21612_21616
abbrev records21608_21616 : List Blob :=
  records21608_21612 ++ records21612_21616
theorem aligned21608_21616 :
    AlignedValid 12 4 missing21608_21616 records21608_21616 :=
  aligned21608_21612.append aligned21612_21616

def missing21600_21616 : List (BitVec (edgeCount 12)) :=
  missing21600_21608 ++ missing21608_21616
abbrev records21600_21616 : List Blob :=
  records21600_21608 ++ records21608_21616
theorem aligned21600_21616 :
    AlignedValid 12 4 missing21600_21616 records21600_21616 :=
  aligned21600_21608.append aligned21608_21616

def missing21616_21617 : List (BitVec (edgeCount 12)) :=
  [missing21616]
abbrev records21616_21617 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21616]
theorem aligned21616_21617 :
    AlignedValid 12 4 missing21616_21617 records21616_21617 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21616
    maskCheck21616 AlignedValid.nil

def missing21617_21618 : List (BitVec (edgeCount 12)) :=
  [missing21617]
abbrev records21617_21618 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21617]
theorem aligned21617_21618 :
    AlignedValid 12 4 missing21617_21618 records21617_21618 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21617
    maskCheck21617 AlignedValid.nil

def missing21616_21618 : List (BitVec (edgeCount 12)) :=
  missing21616_21617 ++ missing21617_21618
abbrev records21616_21618 : List Blob :=
  records21616_21617 ++ records21617_21618
theorem aligned21616_21618 :
    AlignedValid 12 4 missing21616_21618 records21616_21618 :=
  aligned21616_21617.append aligned21617_21618

def missing21618_21619 : List (BitVec (edgeCount 12)) :=
  [missing21618]
abbrev records21618_21619 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21618]
theorem aligned21618_21619 :
    AlignedValid 12 4 missing21618_21619 records21618_21619 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21618
    maskCheck21618 AlignedValid.nil

def missing21619_21620 : List (BitVec (edgeCount 12)) :=
  [missing21619]
abbrev records21619_21620 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21619]
theorem aligned21619_21620 :
    AlignedValid 12 4 missing21619_21620 records21619_21620 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21619
    maskCheck21619 AlignedValid.nil

def missing21618_21620 : List (BitVec (edgeCount 12)) :=
  missing21618_21619 ++ missing21619_21620
abbrev records21618_21620 : List Blob :=
  records21618_21619 ++ records21619_21620
theorem aligned21618_21620 :
    AlignedValid 12 4 missing21618_21620 records21618_21620 :=
  aligned21618_21619.append aligned21619_21620

def missing21616_21620 : List (BitVec (edgeCount 12)) :=
  missing21616_21618 ++ missing21618_21620
abbrev records21616_21620 : List Blob :=
  records21616_21618 ++ records21618_21620
theorem aligned21616_21620 :
    AlignedValid 12 4 missing21616_21620 records21616_21620 :=
  aligned21616_21618.append aligned21618_21620

def missing21620_21621 : List (BitVec (edgeCount 12)) :=
  [missing21620]
abbrev records21620_21621 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21620]
theorem aligned21620_21621 :
    AlignedValid 12 4 missing21620_21621 records21620_21621 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21620
    maskCheck21620 AlignedValid.nil

def missing21621_21622 : List (BitVec (edgeCount 12)) :=
  [missing21621]
abbrev records21621_21622 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21621]
theorem aligned21621_21622 :
    AlignedValid 12 4 missing21621_21622 records21621_21622 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21621
    maskCheck21621 AlignedValid.nil

def missing21620_21622 : List (BitVec (edgeCount 12)) :=
  missing21620_21621 ++ missing21621_21622
abbrev records21620_21622 : List Blob :=
  records21620_21621 ++ records21621_21622
theorem aligned21620_21622 :
    AlignedValid 12 4 missing21620_21622 records21620_21622 :=
  aligned21620_21621.append aligned21621_21622

def missing21622_21623 : List (BitVec (edgeCount 12)) :=
  [missing21622]
abbrev records21622_21623 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21622]
theorem aligned21622_21623 :
    AlignedValid 12 4 missing21622_21623 records21622_21623 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21622
    maskCheck21622 AlignedValid.nil

def missing21623_21624 : List (BitVec (edgeCount 12)) :=
  [missing21623]
abbrev records21623_21624 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21623]
theorem aligned21623_21624 :
    AlignedValid 12 4 missing21623_21624 records21623_21624 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21623
    maskCheck21623 AlignedValid.nil

def missing21622_21624 : List (BitVec (edgeCount 12)) :=
  missing21622_21623 ++ missing21623_21624
abbrev records21622_21624 : List Blob :=
  records21622_21623 ++ records21623_21624
theorem aligned21622_21624 :
    AlignedValid 12 4 missing21622_21624 records21622_21624 :=
  aligned21622_21623.append aligned21623_21624

def missing21620_21624 : List (BitVec (edgeCount 12)) :=
  missing21620_21622 ++ missing21622_21624
abbrev records21620_21624 : List Blob :=
  records21620_21622 ++ records21622_21624
theorem aligned21620_21624 :
    AlignedValid 12 4 missing21620_21624 records21620_21624 :=
  aligned21620_21622.append aligned21622_21624

def missing21616_21624 : List (BitVec (edgeCount 12)) :=
  missing21616_21620 ++ missing21620_21624
abbrev records21616_21624 : List Blob :=
  records21616_21620 ++ records21620_21624
theorem aligned21616_21624 :
    AlignedValid 12 4 missing21616_21624 records21616_21624 :=
  aligned21616_21620.append aligned21620_21624

def missing21624_21625 : List (BitVec (edgeCount 12)) :=
  [missing21624]
abbrev records21624_21625 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21624]
theorem aligned21624_21625 :
    AlignedValid 12 4 missing21624_21625 records21624_21625 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21624
    maskCheck21624 AlignedValid.nil

def missing21625_21626 : List (BitVec (edgeCount 12)) :=
  [missing21625]
abbrev records21625_21626 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21625]
theorem aligned21625_21626 :
    AlignedValid 12 4 missing21625_21626 records21625_21626 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21625
    maskCheck21625 AlignedValid.nil

def missing21624_21626 : List (BitVec (edgeCount 12)) :=
  missing21624_21625 ++ missing21625_21626
abbrev records21624_21626 : List Blob :=
  records21624_21625 ++ records21625_21626
theorem aligned21624_21626 :
    AlignedValid 12 4 missing21624_21626 records21624_21626 :=
  aligned21624_21625.append aligned21625_21626

def missing21626_21627 : List (BitVec (edgeCount 12)) :=
  [missing21626]
abbrev records21626_21627 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21626]
theorem aligned21626_21627 :
    AlignedValid 12 4 missing21626_21627 records21626_21627 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21626
    maskCheck21626 AlignedValid.nil

def missing21627_21628 : List (BitVec (edgeCount 12)) :=
  [missing21627]
abbrev records21627_21628 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21627]
theorem aligned21627_21628 :
    AlignedValid 12 4 missing21627_21628 records21627_21628 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21627
    maskCheck21627 AlignedValid.nil

def missing21626_21628 : List (BitVec (edgeCount 12)) :=
  missing21626_21627 ++ missing21627_21628
abbrev records21626_21628 : List Blob :=
  records21626_21627 ++ records21627_21628
theorem aligned21626_21628 :
    AlignedValid 12 4 missing21626_21628 records21626_21628 :=
  aligned21626_21627.append aligned21627_21628

def missing21624_21628 : List (BitVec (edgeCount 12)) :=
  missing21624_21626 ++ missing21626_21628
abbrev records21624_21628 : List Blob :=
  records21624_21626 ++ records21626_21628
theorem aligned21624_21628 :
    AlignedValid 12 4 missing21624_21628 records21624_21628 :=
  aligned21624_21626.append aligned21626_21628

def missing21628_21629 : List (BitVec (edgeCount 12)) :=
  [missing21628]
abbrev records21628_21629 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21628]
theorem aligned21628_21629 :
    AlignedValid 12 4 missing21628_21629 records21628_21629 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21628
    maskCheck21628 AlignedValid.nil

def missing21629_21630 : List (BitVec (edgeCount 12)) :=
  [missing21629]
abbrev records21629_21630 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21629]
theorem aligned21629_21630 :
    AlignedValid 12 4 missing21629_21630 records21629_21630 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21629
    maskCheck21629 AlignedValid.nil

def missing21628_21630 : List (BitVec (edgeCount 12)) :=
  missing21628_21629 ++ missing21629_21630
abbrev records21628_21630 : List Blob :=
  records21628_21629 ++ records21629_21630
theorem aligned21628_21630 :
    AlignedValid 12 4 missing21628_21630 records21628_21630 :=
  aligned21628_21629.append aligned21629_21630

def missing21630_21631 : List (BitVec (edgeCount 12)) :=
  [missing21630]
abbrev records21630_21631 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21630]
theorem aligned21630_21631 :
    AlignedValid 12 4 missing21630_21631 records21630_21631 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21630
    maskCheck21630 AlignedValid.nil

def missing21631_21632 : List (BitVec (edgeCount 12)) :=
  [missing21631]
abbrev records21631_21632 : List Blob :=
  [StrongPackedBucketN12A4Shard168.record21631]
theorem aligned21631_21632 :
    AlignedValid 12 4 missing21631_21632 records21631_21632 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard168.check21631
    maskCheck21631 AlignedValid.nil

def missing21630_21632 : List (BitVec (edgeCount 12)) :=
  missing21630_21631 ++ missing21631_21632
abbrev records21630_21632 : List Blob :=
  records21630_21631 ++ records21631_21632
theorem aligned21630_21632 :
    AlignedValid 12 4 missing21630_21632 records21630_21632 :=
  aligned21630_21631.append aligned21631_21632

def missing21628_21632 : List (BitVec (edgeCount 12)) :=
  missing21628_21630 ++ missing21630_21632
abbrev records21628_21632 : List Blob :=
  records21628_21630 ++ records21630_21632
theorem aligned21628_21632 :
    AlignedValid 12 4 missing21628_21632 records21628_21632 :=
  aligned21628_21630.append aligned21630_21632

def missing21624_21632 : List (BitVec (edgeCount 12)) :=
  missing21624_21628 ++ missing21628_21632
abbrev records21624_21632 : List Blob :=
  records21624_21628 ++ records21628_21632
theorem aligned21624_21632 :
    AlignedValid 12 4 missing21624_21632 records21624_21632 :=
  aligned21624_21628.append aligned21628_21632

def missing21616_21632 : List (BitVec (edgeCount 12)) :=
  missing21616_21624 ++ missing21624_21632
abbrev records21616_21632 : List Blob :=
  records21616_21624 ++ records21624_21632
theorem aligned21616_21632 :
    AlignedValid 12 4 missing21616_21632 records21616_21632 :=
  aligned21616_21624.append aligned21624_21632

def missing21600_21632 : List (BitVec (edgeCount 12)) :=
  missing21600_21616 ++ missing21616_21632
abbrev records21600_21632 : List Blob :=
  records21600_21616 ++ records21616_21632
theorem aligned21600_21632 :
    AlignedValid 12 4 missing21600_21632 records21600_21632 :=
  aligned21600_21616.append aligned21616_21632

def missing21568_21632 : List (BitVec (edgeCount 12)) :=
  missing21568_21600 ++ missing21600_21632
abbrev records21568_21632 : List Blob :=
  records21568_21600 ++ records21600_21632
theorem aligned21568_21632 :
    AlignedValid 12 4 missing21568_21632 records21568_21632 :=
  aligned21568_21600.append aligned21600_21632

def missing21504_21632 : List (BitVec (edgeCount 12)) :=
  missing21504_21568 ++ missing21568_21632
abbrev records21504_21632 : List Blob :=
  records21504_21568 ++ records21568_21632
theorem aligned21504_21632 :
    AlignedValid 12 4 missing21504_21632 records21504_21632 :=
  aligned21504_21568.append aligned21568_21632

abbrev missing : List (BitVec (edgeCount 12)) := missing21504_21632
abbrev records : List Blob := records21504_21632
theorem aligned : AlignedValid 12 4 missing records := aligned21504_21632

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard168
