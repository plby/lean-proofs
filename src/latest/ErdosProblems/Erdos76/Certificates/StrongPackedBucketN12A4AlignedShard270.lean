/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard270

/-! Decode-only alignment checks for n=12, a=4, records 34560--34687. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard270

open PackedBucketCertificate

def missing34560 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5010364606409900032
theorem maskCheck34560 :
    checkMaskFor missing34560 StrongPackedBucketN12A4Shard270.record34560 = true := by
  decide

def missing34561 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5082422200447827968
theorem maskCheck34561 :
    checkMaskFor missing34561 StrongPackedBucketN12A4Shard270.record34561 = true := by
  decide

def missing34562 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5118450997466791936
theorem maskCheck34562 :
    checkMaskFor missing34562 StrongPackedBucketN12A4Shard270.record34562 = true := by
  decide

def missing34563 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5514767764675395584
theorem maskCheck34563 :
    checkMaskFor missing34563 StrongPackedBucketN12A4Shard270.record34563 = true := by
  decide

def missing34564 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5550796561694359552
theorem maskCheck34564 :
    checkMaskFor missing34564 StrongPackedBucketN12A4Shard270.record34564 = true := by
  decide

def missing34565 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5622854155732287488
theorem maskCheck34565 :
    checkMaskFor missing34565 StrongPackedBucketN12A4Shard270.record34565 = true := by
  decide

def missing34566 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6631660472263278592
theorem maskCheck34566 :
    checkMaskFor missing34566 StrongPackedBucketN12A4Shard270.record34566 = true := by
  decide

def missing34567 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7100034833509810176
theorem maskCheck34567 :
    checkMaskFor missing34567 StrongPackedBucketN12A4Shard270.record34567 = true := by
  decide

def missing34568 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9477935436761432064
theorem maskCheck34568 :
    checkMaskFor missing34568 StrongPackedBucketN12A4Shard270.record34568 = true := by
  decide

def missing34569 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9694108218875215872
theorem maskCheck34569 :
    checkMaskFor missing34569 StrongPackedBucketN12A4Shard270.record34569 = true := by
  decide

def missing34570 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9730137015894179840
theorem maskCheck34570 :
    checkMaskFor missing34570 StrongPackedBucketN12A4Shard270.record34570 = true := by
  decide

def missing34571 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10234540174159675392
theorem maskCheck34571 :
    checkMaskFor missing34571 StrongPackedBucketN12A4Shard270.record34571 = true := by
  decide

def missing34572 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11711720851937198080
theorem maskCheck34572 :
    checkMaskFor missing34572 StrongPackedBucketN12A4Shard270.record34572 = true := by
  decide

def missing34573 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14017563861150892032
theorem maskCheck34573 :
    checkMaskFor missing34573 StrongPackedBucketN12A4Shard270.record34573 = true := by
  decide

def missing34574 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14053592658169856000
theorem maskCheck34574 :
    checkMaskFor missing34574 StrongPackedBucketN12A4Shard270.record34574 = true := by
  decide

def missing34575 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14269765440283639808
theorem maskCheck34575 :
    checkMaskFor missing34575 StrongPackedBucketN12A4Shard270.record34575 = true := by
  decide

def missing34576 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18701307473616207872
theorem maskCheck34576 :
    checkMaskFor missing34576 StrongPackedBucketN12A4Shard270.record34576 = true := by
  decide

def missing34577 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18845422661692063744
theorem maskCheck34577 :
    checkMaskFor missing34577 StrongPackedBucketN12A4Shard270.record34577 = true := by
  decide

def missing34578 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18917480255729991680
theorem maskCheck34578 :
    checkMaskFor missing34578 StrongPackedBucketN12A4Shard270.record34578 = true := by
  decide

def missing34579 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18953509052748955648
theorem maskCheck34579 :
    checkMaskFor missing34579 StrongPackedBucketN12A4Shard270.record34579 = true := by
  decide

def missing34580 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19349825819957559296
theorem maskCheck34580 :
    checkMaskFor missing34580 StrongPackedBucketN12A4Shard270.record34580 = true := by
  decide

def missing34581 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19385854616976523264
theorem maskCheck34581 :
    checkMaskFor missing34581 StrongPackedBucketN12A4Shard270.record34581 = true := by
  decide

def missing34582 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19457912211014451200
theorem maskCheck34582 :
    checkMaskFor missing34582 StrongPackedBucketN12A4Shard270.record34582 = true := by
  decide

def missing34583 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20466718527545442304
theorem maskCheck34583 :
    checkMaskFor missing34583 StrongPackedBucketN12A4Shard270.record34583 = true := by
  decide

def missing34584 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20935092888791973888
theorem maskCheck34584 :
    checkMaskFor missing34584 StrongPackedBucketN12A4Shard270.record34584 = true := by
  decide

def missing34585 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23168878303967739904
theorem maskCheck34585 :
    checkMaskFor missing34585 StrongPackedBucketN12A4Shard270.record34585 = true := by
  decide

def missing34586 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23240935898005667840
theorem maskCheck34586 :
    checkMaskFor missing34586 StrongPackedBucketN12A4Shard270.record34586 = true := by
  decide

def missing34587 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23276964695024631808
theorem maskCheck34587 :
    checkMaskFor missing34587 StrongPackedBucketN12A4Shard270.record34587 = true := by
  decide

def missing34588 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23385051086081523712
theorem maskCheck34588 :
    checkMaskFor missing34588 StrongPackedBucketN12A4Shard270.record34588 = true := by
  decide

def missing34589 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23421079883100487680
theorem maskCheck34589 :
    checkMaskFor missing34589 StrongPackedBucketN12A4Shard270.record34589 = true := by
  decide

def missing34590 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23493137477138415616
theorem maskCheck34590 :
    checkMaskFor missing34590 StrongPackedBucketN12A4Shard270.record34590 = true := by
  decide

def missing34591 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23925483041365983232
theorem maskCheck34591 :
    checkMaskFor missing34591 StrongPackedBucketN12A4Shard270.record34591 = true := by
  decide

def missing34592 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25402663719143505920
theorem maskCheck34592 :
    checkMaskFor missing34592 StrongPackedBucketN12A4Shard270.record34592 = true := by
  decide

def missing34593 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27852621916433055744
theorem maskCheck34593 :
    checkMaskFor missing34593 StrongPackedBucketN12A4Shard270.record34593 = true := by
  decide

def missing34594 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27888650713452019712
theorem maskCheck34594 :
    checkMaskFor missing34594 StrongPackedBucketN12A4Shard270.record34594 = true := by
  decide

def missing34595 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28104823495565803520
theorem maskCheck34595 :
    checkMaskFor missing34595 StrongPackedBucketN12A4Shard270.record34595 = true := by
  decide

def missing34596 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32428279137841479680
theorem maskCheck34596 :
    checkMaskFor missing34596 StrongPackedBucketN12A4Shard270.record34596 = true := by
  decide

def missing34597 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37148051547325759488
theorem maskCheck34597 :
    checkMaskFor missing34597 StrongPackedBucketN12A4Shard270.record34597 = true := by
  decide

def missing34598 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37400253126458507264
theorem maskCheck34598 :
    checkMaskFor missing34598 StrongPackedBucketN12A4Shard270.record34598 = true := by
  decide

def missing34599 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39309779368463597568
theorem maskCheck34599 :
    checkMaskFor missing34599 StrongPackedBucketN12A4Shard270.record34599 = true := by
  decide

def missing34600 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39381836962501525504
theorem maskCheck34600 :
    checkMaskFor missing34600 StrongPackedBucketN12A4Shard270.record34600 = true := by
  decide

def missing34601 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41615622377677291520
theorem maskCheck34601 :
    checkMaskFor missing34601 StrongPackedBucketN12A4Shard270.record34601 = true := by
  decide

def missing34602 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41687679971715219456
theorem maskCheck34602 :
    checkMaskFor missing34602 StrongPackedBucketN12A4Shard270.record34602 = true := by
  decide

def missing34603 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41723708768734183424
theorem maskCheck34603 :
    checkMaskFor missing34603 StrongPackedBucketN12A4Shard270.record34603 = true := by
  decide

def missing34604 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41867823956810039296
theorem maskCheck34604 :
    checkMaskFor missing34604 StrongPackedBucketN12A4Shard270.record34604 = true := by
  decide

def missing34605 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41939881550847967232
theorem maskCheck34605 :
    checkMaskFor missing34605 StrongPackedBucketN12A4Shard270.record34605 = true := by
  decide

def missing34606 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43849407792853057536
theorem maskCheck34606 :
    checkMaskFor missing34606 StrongPackedBucketN12A4Shard270.record34606 = true := by
  decide

def missing34607 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46299365990142607360
theorem maskCheck34607 :
    checkMaskFor missing34607 StrongPackedBucketN12A4Shard270.record34607 = true := by
  decide

def missing34608 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46335394787161571328
theorem maskCheck34608 :
    checkMaskFor missing34608 StrongPackedBucketN12A4Shard270.record34608 = true := by
  decide

def missing34609 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46551567569275355136
theorem maskCheck34609 :
    checkMaskFor missing34609 StrongPackedBucketN12A4Shard270.record34609 = true := by
  decide

def missing34610 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50875023211551031296
theorem maskCheck34610 :
    checkMaskFor missing34610 StrongPackedBucketN12A4Shard270.record34610 = true := by
  decide

def missing34611 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55522738026997383168
theorem maskCheck34611 :
    checkMaskFor missing34611 StrongPackedBucketN12A4Shard270.record34611 = true := by
  decide

def missing34612 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55558766824016347136
theorem maskCheck34612 :
    checkMaskFor missing34612 StrongPackedBucketN12A4Shard270.record34612 = true := by
  decide

def missing34613 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59990308857348915200
theorem maskCheck34613 :
    checkMaskFor missing34613 StrongPackedBucketN12A4Shard270.record34613 = true := by
  decide

def missing34614 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60026337654367879168
theorem maskCheck34614 :
    checkMaskFor missing34614 StrongPackedBucketN12A4Shard270.record34614 = true := by
  decide

def missing34615 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60098395248405807104
theorem maskCheck34615 :
    checkMaskFor missing34615 StrongPackedBucketN12A4Shard270.record34615 = true := by
  decide

def missing34616 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64710081266833195008
theorem maskCheck34616 :
    checkMaskFor missing34616 StrongPackedBucketN12A4Shard270.record34616 = true := by
  decide

def missing34617 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1085477531156512768
theorem maskCheck34617 :
    checkMaskFor missing34617 StrongPackedBucketN12A4Shard270.record34617 = true := by
  decide

def missing34618 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2094283847687503872
theorem maskCheck34618 :
    checkMaskFor missing34618 StrongPackedBucketN12A4Shard270.record34618 = true := by
  decide

def missing34619 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2166341441725431808
theorem maskCheck34619 :
    checkMaskFor missing34619 StrongPackedBucketN12A4Shard270.record34619 = true := by
  decide

def missing34620 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2814859788066783232
theorem maskCheck34620 :
    checkMaskFor missing34620 StrongPackedBucketN12A4Shard270.record34620 = true := by
  decide

def missing34621 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3247205352294350848
theorem maskCheck34621 :
    checkMaskFor missing34621 StrongPackedBucketN12A4Shard270.record34621 = true := by
  decide

def missing34622 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5120702797280477184
theorem maskCheck34622 :
    checkMaskFor missing34622 StrongPackedBucketN12A4Shard270.record34622 = true := by
  decide

def missing34623 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5553048361508044800
theorem maskCheck34623 :
    checkMaskFor missing34623 StrongPackedBucketN12A4Shard270.record34623 = true := by
  decide

def missing34624 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7138315430342459392
theorem maskCheck34624 :
    checkMaskFor missing34624 StrongPackedBucketN12A4Shard270.record34624 = true := by
  decide

def missing34625 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7282430618418315264
theorem maskCheck34625 :
    checkMaskFor missing34625 StrongPackedBucketN12A4Shard270.record34625 = true := by
  decide

def missing34626 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9480187236575117312
theorem maskCheck34626 :
    checkMaskFor missing34626 StrongPackedBucketN12A4Shard270.record34626 = true := by
  decide

def missing34627 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9732388815707865088
theorem maskCheck34627 :
    checkMaskFor missing34627 StrongPackedBucketN12A4Shard270.record34627 = true := by
  decide

def missing34628 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10236791973973360640
theorem maskCheck34628 :
    checkMaskFor missing34628 StrongPackedBucketN12A4Shard270.record34628 = true := by
  decide

def missing34629 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11713972651750883328
theorem maskCheck34629 :
    checkMaskFor missing34629 StrongPackedBucketN12A4Shard270.record34629 = true := by
  decide

def missing34630 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11750001448769847296
theorem maskCheck34630 :
    checkMaskFor missing34630 StrongPackedBucketN12A4Shard270.record34630 = true := by
  decide

def missing34631 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14055844457983541248
theorem maskCheck34631 :
    checkMaskFor missing34631 StrongPackedBucketN12A4Shard270.record34631 = true := by
  decide

def missing34632 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20865287094567731200
theorem maskCheck34632 :
    checkMaskFor missing34632 StrongPackedBucketN12A4Shard270.record34632 = true := by
  decide

def missing34633 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20937344688605659136
theorem maskCheck34633 :
    checkMaskFor missing34633 StrongPackedBucketN12A4Shard270.record34633 = true := by
  decide

def missing34634 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25440944315976155136
theorem maskCheck34634 :
    checkMaskFor missing34634 StrongPackedBucketN12A4Shard270.record34634 = true := by
  decide

def missing34635 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46301617789956292608
theorem maskCheck34635 :
    checkMaskFor missing34635 StrongPackedBucketN12A4Shard270.record34635 = true := by
  decide

def missing34636 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 545151128988319744
theorem maskCheck34636 :
    checkMaskFor missing34636 StrongPackedBucketN12A4Shard270.record34636 = true := by
  decide

def missing34637 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 977496693215887360
theorem maskCheck34637 :
    checkMaskFor missing34637 StrongPackedBucketN12A4Shard270.record34637 = true := by
  decide

def missing34638 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1049554287253815296
theorem maskCheck34638 :
    checkMaskFor missing34638 StrongPackedBucketN12A4Shard270.record34638 = true := by
  decide

def missing34639 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1085583084272779264
theorem maskCheck34639 :
    checkMaskFor missing34639 StrongPackedBucketN12A4Shard270.record34639 = true := by
  decide

def missing34640 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2058360603784806400
theorem maskCheck34640 :
    checkMaskFor missing34640 StrongPackedBucketN12A4Shard270.record34640 = true := by
  decide

def missing34641 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2094389400803770368
theorem maskCheck34641 :
    checkMaskFor missing34641 StrongPackedBucketN12A4Shard270.record34641 = true := by
  decide

def missing34642 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2166446994841698304
theorem maskCheck34642 :
    checkMaskFor missing34642 StrongPackedBucketN12A4Shard270.record34642 = true := by
  decide

def missing34643 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2562763762050301952
theorem maskCheck34643 :
    checkMaskFor missing34643 StrongPackedBucketN12A4Shard270.record34643 = true := by
  decide

def missing34644 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2706878950126157824
theorem maskCheck34644 :
    checkMaskFor missing34644 StrongPackedBucketN12A4Shard270.record34644 = true := by
  decide

def missing34645 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2778936544164085760
theorem maskCheck34645 :
    checkMaskFor missing34645 StrongPackedBucketN12A4Shard270.record34645 = true := by
  decide

def missing34646 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3211282108391653376
theorem maskCheck34646 :
    checkMaskFor missing34646 StrongPackedBucketN12A4Shard270.record34646 = true := by
  decide

def missing34647 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4868606771263995904
theorem maskCheck34647 :
    checkMaskFor missing34647 StrongPackedBucketN12A4Shard270.record34647 = true := by
  decide

def missing34648 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5012721959339851776
theorem maskCheck34648 :
    checkMaskFor missing34648 StrongPackedBucketN12A4Shard270.record34648 = true := by
  decide

def missing34649 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5120808350396743680
theorem maskCheck34649 :
    checkMaskFor missing34649 StrongPackedBucketN12A4Shard270.record34649 = true := by
  decide

def missing34650 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5553153914624311296
theorem maskCheck34650 :
    checkMaskFor missing34650 StrongPackedBucketN12A4Shard270.record34650 = true := by
  decide

def missing34651 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7030334592401833984
theorem maskCheck34651 :
    checkMaskFor missing34651 StrongPackedBucketN12A4Shard270.record34651 = true := by
  decide

def missing34652 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9480292789691383808
theorem maskCheck34652 :
    checkMaskFor missing34652 StrongPackedBucketN12A4Shard270.record34652 = true := by
  decide

def missing34653 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9624407977767239680
theorem maskCheck34653 :
    checkMaskFor missing34653 StrongPackedBucketN12A4Shard270.record34653 = true := by
  decide

def missing34654 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9696465571805167616
theorem maskCheck34654 :
    checkMaskFor missing34654 StrongPackedBucketN12A4Shard270.record34654 = true := by
  decide

def missing34655 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9732494368824131584
theorem maskCheck34655 :
    checkMaskFor missing34655 StrongPackedBucketN12A4Shard270.record34655 = true := by
  decide

def missing34656 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10128811136032735232
theorem maskCheck34656 :
    checkMaskFor missing34656 StrongPackedBucketN12A4Shard270.record34656 = true := by
  decide

def missing34657 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10164839933051699200
theorem maskCheck34657 :
    checkMaskFor missing34657 StrongPackedBucketN12A4Shard270.record34657 = true := by
  decide

def missing34658 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10236897527089627136
theorem maskCheck34658 :
    checkMaskFor missing34658 StrongPackedBucketN12A4Shard270.record34658 = true := by
  decide

def missing34659 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11245703843620618240
theorem maskCheck34659 :
    checkMaskFor missing34659 StrongPackedBucketN12A4Shard270.record34659 = true := by
  decide

def missing34660 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11642020610829221888
theorem maskCheck34660 :
    checkMaskFor missing34660 StrongPackedBucketN12A4Shard270.record34660 = true := by
  decide

def missing34661 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11714078204867149824
theorem maskCheck34661 :
    checkMaskFor missing34661 StrongPackedBucketN12A4Shard270.record34661 = true := by
  decide

def missing34662 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11858193392943005696
theorem maskCheck34662 :
    checkMaskFor missing34662 StrongPackedBucketN12A4Shard270.record34662 = true := by
  decide

def missing34663 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13947863620042915840
theorem maskCheck34663 :
    checkMaskFor missing34663 StrongPackedBucketN12A4Shard270.record34663 = true := by
  decide

def missing34664 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14055950011099807744
theorem maskCheck34664 :
    checkMaskFor missing34664 StrongPackedBucketN12A4Shard270.record34664 = true := by
  decide

def missing34665 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14200065199175663616
theorem maskCheck34665 :
    checkMaskFor missing34665 StrongPackedBucketN12A4Shard270.record34665 = true := by
  decide

def missing34666 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20865392647683997696
theorem maskCheck34666 :
    checkMaskFor missing34666 StrongPackedBucketN12A4Shard270.record34666 = true := by
  decide

def missing34667 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20937450241721925632
theorem maskCheck34667 :
    checkMaskFor missing34667 StrongPackedBucketN12A4Shard270.record34667 = true := by
  decide

def missing34668 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21081565429797781504
theorem maskCheck34668 :
    checkMaskFor missing34668 StrongPackedBucketN12A4Shard270.record34668 = true := by
  decide

def missing34669 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30016707090500845568
theorem maskCheck34669 :
    checkMaskFor missing34669 StrongPackedBucketN12A4Shard270.record34669 = true := by
  decide

def missing34670 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41726066121664135168
theorem maskCheck34670 :
    checkMaskFor missing34670 StrongPackedBucketN12A4Shard270.record34670 = true := by
  decide

def missing34671 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46337752140091523072
theorem maskCheck34671 :
    checkMaskFor missing34671 StrongPackedBucketN12A4Shard270.record34671 = true := by
  decide

def missing34672 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50805322970443055104
theorem maskCheck34672 :
    checkMaskFor missing34672 StrongPackedBucketN12A4Shard270.record34672 = true := by
  decide

def missing34673 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 545291866476675072
theorem maskCheck34673 :
    checkMaskFor missing34673 StrongPackedBucketN12A4Shard270.record34673 = true := by
  decide

def missing34674 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 833522242628386816
theorem maskCheck34674 :
    checkMaskFor missing34674 StrongPackedBucketN12A4Shard270.record34674 = true := by
  decide

def missing34675 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 977637430704242688
theorem maskCheck34675 :
    checkMaskFor missing34675 StrongPackedBucketN12A4Shard270.record34675 = true := by
  decide

def missing34676 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1049695024742170624
theorem maskCheck34676 :
    checkMaskFor missing34676 StrongPackedBucketN12A4Shard270.record34676 = true := by
  decide

def missing34677 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1085723821761134592
theorem maskCheck34677 :
    checkMaskFor missing34677 StrongPackedBucketN12A4Shard270.record34677 = true := by
  decide

def missing34678 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1842328559159377920
theorem maskCheck34678 :
    checkMaskFor missing34678 StrongPackedBucketN12A4Shard270.record34678 = true := by
  decide

def missing34679 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1914386153197305856
theorem maskCheck34679 :
    checkMaskFor missing34679 StrongPackedBucketN12A4Shard270.record34679 = true := by
  decide

def missing34680 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1950414950216269824
theorem maskCheck34680 :
    checkMaskFor missing34680 StrongPackedBucketN12A4Shard270.record34680 = true := by
  decide

def missing34681 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2058501341273161728
theorem maskCheck34681 :
    checkMaskFor missing34681 StrongPackedBucketN12A4Shard270.record34681 = true := by
  decide

def missing34682 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2094530138292125696
theorem maskCheck34682 :
    checkMaskFor missing34682 StrongPackedBucketN12A4Shard270.record34682 = true := by
  decide

def missing34683 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2166587732330053632
theorem maskCheck34683 :
    checkMaskFor missing34683 StrongPackedBucketN12A4Shard270.record34683 = true := by
  decide

def missing34684 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2562904499538657280
theorem maskCheck34684 :
    checkMaskFor missing34684 StrongPackedBucketN12A4Shard270.record34684 = true := by
  decide

def missing34685 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2707019687614513152
theorem maskCheck34685 :
    checkMaskFor missing34685 StrongPackedBucketN12A4Shard270.record34685 = true := by
  decide

def missing34686 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2779077281652441088
theorem maskCheck34686 :
    checkMaskFor missing34686 StrongPackedBucketN12A4Shard270.record34686 = true := by
  decide

def missing34687 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2995250063766224896
theorem maskCheck34687 :
    checkMaskFor missing34687 StrongPackedBucketN12A4Shard270.record34687 = true := by
  decide

def missing34560_34561 : List (BitVec (edgeCount 12)) :=
  [missing34560]
abbrev records34560_34561 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34560]
theorem aligned34560_34561 :
    AlignedValid 12 4 missing34560_34561 records34560_34561 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34560
    maskCheck34560 AlignedValid.nil

def missing34561_34562 : List (BitVec (edgeCount 12)) :=
  [missing34561]
abbrev records34561_34562 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34561]
theorem aligned34561_34562 :
    AlignedValid 12 4 missing34561_34562 records34561_34562 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34561
    maskCheck34561 AlignedValid.nil

def missing34560_34562 : List (BitVec (edgeCount 12)) :=
  missing34560_34561 ++ missing34561_34562
abbrev records34560_34562 : List Blob :=
  records34560_34561 ++ records34561_34562
theorem aligned34560_34562 :
    AlignedValid 12 4 missing34560_34562 records34560_34562 :=
  aligned34560_34561.append aligned34561_34562

def missing34562_34563 : List (BitVec (edgeCount 12)) :=
  [missing34562]
abbrev records34562_34563 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34562]
theorem aligned34562_34563 :
    AlignedValid 12 4 missing34562_34563 records34562_34563 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34562
    maskCheck34562 AlignedValid.nil

def missing34563_34564 : List (BitVec (edgeCount 12)) :=
  [missing34563]
abbrev records34563_34564 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34563]
theorem aligned34563_34564 :
    AlignedValid 12 4 missing34563_34564 records34563_34564 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34563
    maskCheck34563 AlignedValid.nil

def missing34562_34564 : List (BitVec (edgeCount 12)) :=
  missing34562_34563 ++ missing34563_34564
abbrev records34562_34564 : List Blob :=
  records34562_34563 ++ records34563_34564
theorem aligned34562_34564 :
    AlignedValid 12 4 missing34562_34564 records34562_34564 :=
  aligned34562_34563.append aligned34563_34564

def missing34560_34564 : List (BitVec (edgeCount 12)) :=
  missing34560_34562 ++ missing34562_34564
abbrev records34560_34564 : List Blob :=
  records34560_34562 ++ records34562_34564
theorem aligned34560_34564 :
    AlignedValid 12 4 missing34560_34564 records34560_34564 :=
  aligned34560_34562.append aligned34562_34564

def missing34564_34565 : List (BitVec (edgeCount 12)) :=
  [missing34564]
abbrev records34564_34565 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34564]
theorem aligned34564_34565 :
    AlignedValid 12 4 missing34564_34565 records34564_34565 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34564
    maskCheck34564 AlignedValid.nil

def missing34565_34566 : List (BitVec (edgeCount 12)) :=
  [missing34565]
abbrev records34565_34566 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34565]
theorem aligned34565_34566 :
    AlignedValid 12 4 missing34565_34566 records34565_34566 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34565
    maskCheck34565 AlignedValid.nil

def missing34564_34566 : List (BitVec (edgeCount 12)) :=
  missing34564_34565 ++ missing34565_34566
abbrev records34564_34566 : List Blob :=
  records34564_34565 ++ records34565_34566
theorem aligned34564_34566 :
    AlignedValid 12 4 missing34564_34566 records34564_34566 :=
  aligned34564_34565.append aligned34565_34566

def missing34566_34567 : List (BitVec (edgeCount 12)) :=
  [missing34566]
abbrev records34566_34567 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34566]
theorem aligned34566_34567 :
    AlignedValid 12 4 missing34566_34567 records34566_34567 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34566
    maskCheck34566 AlignedValid.nil

def missing34567_34568 : List (BitVec (edgeCount 12)) :=
  [missing34567]
abbrev records34567_34568 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34567]
theorem aligned34567_34568 :
    AlignedValid 12 4 missing34567_34568 records34567_34568 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34567
    maskCheck34567 AlignedValid.nil

def missing34566_34568 : List (BitVec (edgeCount 12)) :=
  missing34566_34567 ++ missing34567_34568
abbrev records34566_34568 : List Blob :=
  records34566_34567 ++ records34567_34568
theorem aligned34566_34568 :
    AlignedValid 12 4 missing34566_34568 records34566_34568 :=
  aligned34566_34567.append aligned34567_34568

def missing34564_34568 : List (BitVec (edgeCount 12)) :=
  missing34564_34566 ++ missing34566_34568
abbrev records34564_34568 : List Blob :=
  records34564_34566 ++ records34566_34568
theorem aligned34564_34568 :
    AlignedValid 12 4 missing34564_34568 records34564_34568 :=
  aligned34564_34566.append aligned34566_34568

def missing34560_34568 : List (BitVec (edgeCount 12)) :=
  missing34560_34564 ++ missing34564_34568
abbrev records34560_34568 : List Blob :=
  records34560_34564 ++ records34564_34568
theorem aligned34560_34568 :
    AlignedValid 12 4 missing34560_34568 records34560_34568 :=
  aligned34560_34564.append aligned34564_34568

def missing34568_34569 : List (BitVec (edgeCount 12)) :=
  [missing34568]
abbrev records34568_34569 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34568]
theorem aligned34568_34569 :
    AlignedValid 12 4 missing34568_34569 records34568_34569 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34568
    maskCheck34568 AlignedValid.nil

def missing34569_34570 : List (BitVec (edgeCount 12)) :=
  [missing34569]
abbrev records34569_34570 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34569]
theorem aligned34569_34570 :
    AlignedValid 12 4 missing34569_34570 records34569_34570 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34569
    maskCheck34569 AlignedValid.nil

def missing34568_34570 : List (BitVec (edgeCount 12)) :=
  missing34568_34569 ++ missing34569_34570
abbrev records34568_34570 : List Blob :=
  records34568_34569 ++ records34569_34570
theorem aligned34568_34570 :
    AlignedValid 12 4 missing34568_34570 records34568_34570 :=
  aligned34568_34569.append aligned34569_34570

def missing34570_34571 : List (BitVec (edgeCount 12)) :=
  [missing34570]
abbrev records34570_34571 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34570]
theorem aligned34570_34571 :
    AlignedValid 12 4 missing34570_34571 records34570_34571 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34570
    maskCheck34570 AlignedValid.nil

def missing34571_34572 : List (BitVec (edgeCount 12)) :=
  [missing34571]
abbrev records34571_34572 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34571]
theorem aligned34571_34572 :
    AlignedValid 12 4 missing34571_34572 records34571_34572 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34571
    maskCheck34571 AlignedValid.nil

def missing34570_34572 : List (BitVec (edgeCount 12)) :=
  missing34570_34571 ++ missing34571_34572
abbrev records34570_34572 : List Blob :=
  records34570_34571 ++ records34571_34572
theorem aligned34570_34572 :
    AlignedValid 12 4 missing34570_34572 records34570_34572 :=
  aligned34570_34571.append aligned34571_34572

def missing34568_34572 : List (BitVec (edgeCount 12)) :=
  missing34568_34570 ++ missing34570_34572
abbrev records34568_34572 : List Blob :=
  records34568_34570 ++ records34570_34572
theorem aligned34568_34572 :
    AlignedValid 12 4 missing34568_34572 records34568_34572 :=
  aligned34568_34570.append aligned34570_34572

def missing34572_34573 : List (BitVec (edgeCount 12)) :=
  [missing34572]
abbrev records34572_34573 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34572]
theorem aligned34572_34573 :
    AlignedValid 12 4 missing34572_34573 records34572_34573 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34572
    maskCheck34572 AlignedValid.nil

def missing34573_34574 : List (BitVec (edgeCount 12)) :=
  [missing34573]
abbrev records34573_34574 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34573]
theorem aligned34573_34574 :
    AlignedValid 12 4 missing34573_34574 records34573_34574 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34573
    maskCheck34573 AlignedValid.nil

def missing34572_34574 : List (BitVec (edgeCount 12)) :=
  missing34572_34573 ++ missing34573_34574
abbrev records34572_34574 : List Blob :=
  records34572_34573 ++ records34573_34574
theorem aligned34572_34574 :
    AlignedValid 12 4 missing34572_34574 records34572_34574 :=
  aligned34572_34573.append aligned34573_34574

def missing34574_34575 : List (BitVec (edgeCount 12)) :=
  [missing34574]
abbrev records34574_34575 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34574]
theorem aligned34574_34575 :
    AlignedValid 12 4 missing34574_34575 records34574_34575 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34574
    maskCheck34574 AlignedValid.nil

def missing34575_34576 : List (BitVec (edgeCount 12)) :=
  [missing34575]
abbrev records34575_34576 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34575]
theorem aligned34575_34576 :
    AlignedValid 12 4 missing34575_34576 records34575_34576 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34575
    maskCheck34575 AlignedValid.nil

def missing34574_34576 : List (BitVec (edgeCount 12)) :=
  missing34574_34575 ++ missing34575_34576
abbrev records34574_34576 : List Blob :=
  records34574_34575 ++ records34575_34576
theorem aligned34574_34576 :
    AlignedValid 12 4 missing34574_34576 records34574_34576 :=
  aligned34574_34575.append aligned34575_34576

def missing34572_34576 : List (BitVec (edgeCount 12)) :=
  missing34572_34574 ++ missing34574_34576
abbrev records34572_34576 : List Blob :=
  records34572_34574 ++ records34574_34576
theorem aligned34572_34576 :
    AlignedValid 12 4 missing34572_34576 records34572_34576 :=
  aligned34572_34574.append aligned34574_34576

def missing34568_34576 : List (BitVec (edgeCount 12)) :=
  missing34568_34572 ++ missing34572_34576
abbrev records34568_34576 : List Blob :=
  records34568_34572 ++ records34572_34576
theorem aligned34568_34576 :
    AlignedValid 12 4 missing34568_34576 records34568_34576 :=
  aligned34568_34572.append aligned34572_34576

def missing34560_34576 : List (BitVec (edgeCount 12)) :=
  missing34560_34568 ++ missing34568_34576
abbrev records34560_34576 : List Blob :=
  records34560_34568 ++ records34568_34576
theorem aligned34560_34576 :
    AlignedValid 12 4 missing34560_34576 records34560_34576 :=
  aligned34560_34568.append aligned34568_34576

def missing34576_34577 : List (BitVec (edgeCount 12)) :=
  [missing34576]
abbrev records34576_34577 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34576]
theorem aligned34576_34577 :
    AlignedValid 12 4 missing34576_34577 records34576_34577 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34576
    maskCheck34576 AlignedValid.nil

def missing34577_34578 : List (BitVec (edgeCount 12)) :=
  [missing34577]
abbrev records34577_34578 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34577]
theorem aligned34577_34578 :
    AlignedValid 12 4 missing34577_34578 records34577_34578 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34577
    maskCheck34577 AlignedValid.nil

def missing34576_34578 : List (BitVec (edgeCount 12)) :=
  missing34576_34577 ++ missing34577_34578
abbrev records34576_34578 : List Blob :=
  records34576_34577 ++ records34577_34578
theorem aligned34576_34578 :
    AlignedValid 12 4 missing34576_34578 records34576_34578 :=
  aligned34576_34577.append aligned34577_34578

def missing34578_34579 : List (BitVec (edgeCount 12)) :=
  [missing34578]
abbrev records34578_34579 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34578]
theorem aligned34578_34579 :
    AlignedValid 12 4 missing34578_34579 records34578_34579 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34578
    maskCheck34578 AlignedValid.nil

def missing34579_34580 : List (BitVec (edgeCount 12)) :=
  [missing34579]
abbrev records34579_34580 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34579]
theorem aligned34579_34580 :
    AlignedValid 12 4 missing34579_34580 records34579_34580 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34579
    maskCheck34579 AlignedValid.nil

def missing34578_34580 : List (BitVec (edgeCount 12)) :=
  missing34578_34579 ++ missing34579_34580
abbrev records34578_34580 : List Blob :=
  records34578_34579 ++ records34579_34580
theorem aligned34578_34580 :
    AlignedValid 12 4 missing34578_34580 records34578_34580 :=
  aligned34578_34579.append aligned34579_34580

def missing34576_34580 : List (BitVec (edgeCount 12)) :=
  missing34576_34578 ++ missing34578_34580
abbrev records34576_34580 : List Blob :=
  records34576_34578 ++ records34578_34580
theorem aligned34576_34580 :
    AlignedValid 12 4 missing34576_34580 records34576_34580 :=
  aligned34576_34578.append aligned34578_34580

def missing34580_34581 : List (BitVec (edgeCount 12)) :=
  [missing34580]
abbrev records34580_34581 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34580]
theorem aligned34580_34581 :
    AlignedValid 12 4 missing34580_34581 records34580_34581 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34580
    maskCheck34580 AlignedValid.nil

def missing34581_34582 : List (BitVec (edgeCount 12)) :=
  [missing34581]
abbrev records34581_34582 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34581]
theorem aligned34581_34582 :
    AlignedValid 12 4 missing34581_34582 records34581_34582 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34581
    maskCheck34581 AlignedValid.nil

def missing34580_34582 : List (BitVec (edgeCount 12)) :=
  missing34580_34581 ++ missing34581_34582
abbrev records34580_34582 : List Blob :=
  records34580_34581 ++ records34581_34582
theorem aligned34580_34582 :
    AlignedValid 12 4 missing34580_34582 records34580_34582 :=
  aligned34580_34581.append aligned34581_34582

def missing34582_34583 : List (BitVec (edgeCount 12)) :=
  [missing34582]
abbrev records34582_34583 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34582]
theorem aligned34582_34583 :
    AlignedValid 12 4 missing34582_34583 records34582_34583 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34582
    maskCheck34582 AlignedValid.nil

def missing34583_34584 : List (BitVec (edgeCount 12)) :=
  [missing34583]
abbrev records34583_34584 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34583]
theorem aligned34583_34584 :
    AlignedValid 12 4 missing34583_34584 records34583_34584 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34583
    maskCheck34583 AlignedValid.nil

def missing34582_34584 : List (BitVec (edgeCount 12)) :=
  missing34582_34583 ++ missing34583_34584
abbrev records34582_34584 : List Blob :=
  records34582_34583 ++ records34583_34584
theorem aligned34582_34584 :
    AlignedValid 12 4 missing34582_34584 records34582_34584 :=
  aligned34582_34583.append aligned34583_34584

def missing34580_34584 : List (BitVec (edgeCount 12)) :=
  missing34580_34582 ++ missing34582_34584
abbrev records34580_34584 : List Blob :=
  records34580_34582 ++ records34582_34584
theorem aligned34580_34584 :
    AlignedValid 12 4 missing34580_34584 records34580_34584 :=
  aligned34580_34582.append aligned34582_34584

def missing34576_34584 : List (BitVec (edgeCount 12)) :=
  missing34576_34580 ++ missing34580_34584
abbrev records34576_34584 : List Blob :=
  records34576_34580 ++ records34580_34584
theorem aligned34576_34584 :
    AlignedValid 12 4 missing34576_34584 records34576_34584 :=
  aligned34576_34580.append aligned34580_34584

def missing34584_34585 : List (BitVec (edgeCount 12)) :=
  [missing34584]
abbrev records34584_34585 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34584]
theorem aligned34584_34585 :
    AlignedValid 12 4 missing34584_34585 records34584_34585 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34584
    maskCheck34584 AlignedValid.nil

def missing34585_34586 : List (BitVec (edgeCount 12)) :=
  [missing34585]
abbrev records34585_34586 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34585]
theorem aligned34585_34586 :
    AlignedValid 12 4 missing34585_34586 records34585_34586 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34585
    maskCheck34585 AlignedValid.nil

def missing34584_34586 : List (BitVec (edgeCount 12)) :=
  missing34584_34585 ++ missing34585_34586
abbrev records34584_34586 : List Blob :=
  records34584_34585 ++ records34585_34586
theorem aligned34584_34586 :
    AlignedValid 12 4 missing34584_34586 records34584_34586 :=
  aligned34584_34585.append aligned34585_34586

def missing34586_34587 : List (BitVec (edgeCount 12)) :=
  [missing34586]
abbrev records34586_34587 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34586]
theorem aligned34586_34587 :
    AlignedValid 12 4 missing34586_34587 records34586_34587 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34586
    maskCheck34586 AlignedValid.nil

def missing34587_34588 : List (BitVec (edgeCount 12)) :=
  [missing34587]
abbrev records34587_34588 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34587]
theorem aligned34587_34588 :
    AlignedValid 12 4 missing34587_34588 records34587_34588 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34587
    maskCheck34587 AlignedValid.nil

def missing34586_34588 : List (BitVec (edgeCount 12)) :=
  missing34586_34587 ++ missing34587_34588
abbrev records34586_34588 : List Blob :=
  records34586_34587 ++ records34587_34588
theorem aligned34586_34588 :
    AlignedValid 12 4 missing34586_34588 records34586_34588 :=
  aligned34586_34587.append aligned34587_34588

def missing34584_34588 : List (BitVec (edgeCount 12)) :=
  missing34584_34586 ++ missing34586_34588
abbrev records34584_34588 : List Blob :=
  records34584_34586 ++ records34586_34588
theorem aligned34584_34588 :
    AlignedValid 12 4 missing34584_34588 records34584_34588 :=
  aligned34584_34586.append aligned34586_34588

def missing34588_34589 : List (BitVec (edgeCount 12)) :=
  [missing34588]
abbrev records34588_34589 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34588]
theorem aligned34588_34589 :
    AlignedValid 12 4 missing34588_34589 records34588_34589 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34588
    maskCheck34588 AlignedValid.nil

def missing34589_34590 : List (BitVec (edgeCount 12)) :=
  [missing34589]
abbrev records34589_34590 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34589]
theorem aligned34589_34590 :
    AlignedValid 12 4 missing34589_34590 records34589_34590 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34589
    maskCheck34589 AlignedValid.nil

def missing34588_34590 : List (BitVec (edgeCount 12)) :=
  missing34588_34589 ++ missing34589_34590
abbrev records34588_34590 : List Blob :=
  records34588_34589 ++ records34589_34590
theorem aligned34588_34590 :
    AlignedValid 12 4 missing34588_34590 records34588_34590 :=
  aligned34588_34589.append aligned34589_34590

def missing34590_34591 : List (BitVec (edgeCount 12)) :=
  [missing34590]
abbrev records34590_34591 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34590]
theorem aligned34590_34591 :
    AlignedValid 12 4 missing34590_34591 records34590_34591 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34590
    maskCheck34590 AlignedValid.nil

def missing34591_34592 : List (BitVec (edgeCount 12)) :=
  [missing34591]
abbrev records34591_34592 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34591]
theorem aligned34591_34592 :
    AlignedValid 12 4 missing34591_34592 records34591_34592 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34591
    maskCheck34591 AlignedValid.nil

def missing34590_34592 : List (BitVec (edgeCount 12)) :=
  missing34590_34591 ++ missing34591_34592
abbrev records34590_34592 : List Blob :=
  records34590_34591 ++ records34591_34592
theorem aligned34590_34592 :
    AlignedValid 12 4 missing34590_34592 records34590_34592 :=
  aligned34590_34591.append aligned34591_34592

def missing34588_34592 : List (BitVec (edgeCount 12)) :=
  missing34588_34590 ++ missing34590_34592
abbrev records34588_34592 : List Blob :=
  records34588_34590 ++ records34590_34592
theorem aligned34588_34592 :
    AlignedValid 12 4 missing34588_34592 records34588_34592 :=
  aligned34588_34590.append aligned34590_34592

def missing34584_34592 : List (BitVec (edgeCount 12)) :=
  missing34584_34588 ++ missing34588_34592
abbrev records34584_34592 : List Blob :=
  records34584_34588 ++ records34588_34592
theorem aligned34584_34592 :
    AlignedValid 12 4 missing34584_34592 records34584_34592 :=
  aligned34584_34588.append aligned34588_34592

def missing34576_34592 : List (BitVec (edgeCount 12)) :=
  missing34576_34584 ++ missing34584_34592
abbrev records34576_34592 : List Blob :=
  records34576_34584 ++ records34584_34592
theorem aligned34576_34592 :
    AlignedValid 12 4 missing34576_34592 records34576_34592 :=
  aligned34576_34584.append aligned34584_34592

def missing34560_34592 : List (BitVec (edgeCount 12)) :=
  missing34560_34576 ++ missing34576_34592
abbrev records34560_34592 : List Blob :=
  records34560_34576 ++ records34576_34592
theorem aligned34560_34592 :
    AlignedValid 12 4 missing34560_34592 records34560_34592 :=
  aligned34560_34576.append aligned34576_34592

def missing34592_34593 : List (BitVec (edgeCount 12)) :=
  [missing34592]
abbrev records34592_34593 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34592]
theorem aligned34592_34593 :
    AlignedValid 12 4 missing34592_34593 records34592_34593 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34592
    maskCheck34592 AlignedValid.nil

def missing34593_34594 : List (BitVec (edgeCount 12)) :=
  [missing34593]
abbrev records34593_34594 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34593]
theorem aligned34593_34594 :
    AlignedValid 12 4 missing34593_34594 records34593_34594 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34593
    maskCheck34593 AlignedValid.nil

def missing34592_34594 : List (BitVec (edgeCount 12)) :=
  missing34592_34593 ++ missing34593_34594
abbrev records34592_34594 : List Blob :=
  records34592_34593 ++ records34593_34594
theorem aligned34592_34594 :
    AlignedValid 12 4 missing34592_34594 records34592_34594 :=
  aligned34592_34593.append aligned34593_34594

def missing34594_34595 : List (BitVec (edgeCount 12)) :=
  [missing34594]
abbrev records34594_34595 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34594]
theorem aligned34594_34595 :
    AlignedValid 12 4 missing34594_34595 records34594_34595 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34594
    maskCheck34594 AlignedValid.nil

def missing34595_34596 : List (BitVec (edgeCount 12)) :=
  [missing34595]
abbrev records34595_34596 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34595]
theorem aligned34595_34596 :
    AlignedValid 12 4 missing34595_34596 records34595_34596 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34595
    maskCheck34595 AlignedValid.nil

def missing34594_34596 : List (BitVec (edgeCount 12)) :=
  missing34594_34595 ++ missing34595_34596
abbrev records34594_34596 : List Blob :=
  records34594_34595 ++ records34595_34596
theorem aligned34594_34596 :
    AlignedValid 12 4 missing34594_34596 records34594_34596 :=
  aligned34594_34595.append aligned34595_34596

def missing34592_34596 : List (BitVec (edgeCount 12)) :=
  missing34592_34594 ++ missing34594_34596
abbrev records34592_34596 : List Blob :=
  records34592_34594 ++ records34594_34596
theorem aligned34592_34596 :
    AlignedValid 12 4 missing34592_34596 records34592_34596 :=
  aligned34592_34594.append aligned34594_34596

def missing34596_34597 : List (BitVec (edgeCount 12)) :=
  [missing34596]
abbrev records34596_34597 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34596]
theorem aligned34596_34597 :
    AlignedValid 12 4 missing34596_34597 records34596_34597 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34596
    maskCheck34596 AlignedValid.nil

def missing34597_34598 : List (BitVec (edgeCount 12)) :=
  [missing34597]
abbrev records34597_34598 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34597]
theorem aligned34597_34598 :
    AlignedValid 12 4 missing34597_34598 records34597_34598 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34597
    maskCheck34597 AlignedValid.nil

def missing34596_34598 : List (BitVec (edgeCount 12)) :=
  missing34596_34597 ++ missing34597_34598
abbrev records34596_34598 : List Blob :=
  records34596_34597 ++ records34597_34598
theorem aligned34596_34598 :
    AlignedValid 12 4 missing34596_34598 records34596_34598 :=
  aligned34596_34597.append aligned34597_34598

def missing34598_34599 : List (BitVec (edgeCount 12)) :=
  [missing34598]
abbrev records34598_34599 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34598]
theorem aligned34598_34599 :
    AlignedValid 12 4 missing34598_34599 records34598_34599 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34598
    maskCheck34598 AlignedValid.nil

def missing34599_34600 : List (BitVec (edgeCount 12)) :=
  [missing34599]
abbrev records34599_34600 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34599]
theorem aligned34599_34600 :
    AlignedValid 12 4 missing34599_34600 records34599_34600 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34599
    maskCheck34599 AlignedValid.nil

def missing34598_34600 : List (BitVec (edgeCount 12)) :=
  missing34598_34599 ++ missing34599_34600
abbrev records34598_34600 : List Blob :=
  records34598_34599 ++ records34599_34600
theorem aligned34598_34600 :
    AlignedValid 12 4 missing34598_34600 records34598_34600 :=
  aligned34598_34599.append aligned34599_34600

def missing34596_34600 : List (BitVec (edgeCount 12)) :=
  missing34596_34598 ++ missing34598_34600
abbrev records34596_34600 : List Blob :=
  records34596_34598 ++ records34598_34600
theorem aligned34596_34600 :
    AlignedValid 12 4 missing34596_34600 records34596_34600 :=
  aligned34596_34598.append aligned34598_34600

def missing34592_34600 : List (BitVec (edgeCount 12)) :=
  missing34592_34596 ++ missing34596_34600
abbrev records34592_34600 : List Blob :=
  records34592_34596 ++ records34596_34600
theorem aligned34592_34600 :
    AlignedValid 12 4 missing34592_34600 records34592_34600 :=
  aligned34592_34596.append aligned34596_34600

def missing34600_34601 : List (BitVec (edgeCount 12)) :=
  [missing34600]
abbrev records34600_34601 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34600]
theorem aligned34600_34601 :
    AlignedValid 12 4 missing34600_34601 records34600_34601 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34600
    maskCheck34600 AlignedValid.nil

def missing34601_34602 : List (BitVec (edgeCount 12)) :=
  [missing34601]
abbrev records34601_34602 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34601]
theorem aligned34601_34602 :
    AlignedValid 12 4 missing34601_34602 records34601_34602 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34601
    maskCheck34601 AlignedValid.nil

def missing34600_34602 : List (BitVec (edgeCount 12)) :=
  missing34600_34601 ++ missing34601_34602
abbrev records34600_34602 : List Blob :=
  records34600_34601 ++ records34601_34602
theorem aligned34600_34602 :
    AlignedValid 12 4 missing34600_34602 records34600_34602 :=
  aligned34600_34601.append aligned34601_34602

def missing34602_34603 : List (BitVec (edgeCount 12)) :=
  [missing34602]
abbrev records34602_34603 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34602]
theorem aligned34602_34603 :
    AlignedValid 12 4 missing34602_34603 records34602_34603 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34602
    maskCheck34602 AlignedValid.nil

def missing34603_34604 : List (BitVec (edgeCount 12)) :=
  [missing34603]
abbrev records34603_34604 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34603]
theorem aligned34603_34604 :
    AlignedValid 12 4 missing34603_34604 records34603_34604 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34603
    maskCheck34603 AlignedValid.nil

def missing34602_34604 : List (BitVec (edgeCount 12)) :=
  missing34602_34603 ++ missing34603_34604
abbrev records34602_34604 : List Blob :=
  records34602_34603 ++ records34603_34604
theorem aligned34602_34604 :
    AlignedValid 12 4 missing34602_34604 records34602_34604 :=
  aligned34602_34603.append aligned34603_34604

def missing34600_34604 : List (BitVec (edgeCount 12)) :=
  missing34600_34602 ++ missing34602_34604
abbrev records34600_34604 : List Blob :=
  records34600_34602 ++ records34602_34604
theorem aligned34600_34604 :
    AlignedValid 12 4 missing34600_34604 records34600_34604 :=
  aligned34600_34602.append aligned34602_34604

def missing34604_34605 : List (BitVec (edgeCount 12)) :=
  [missing34604]
abbrev records34604_34605 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34604]
theorem aligned34604_34605 :
    AlignedValid 12 4 missing34604_34605 records34604_34605 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34604
    maskCheck34604 AlignedValid.nil

def missing34605_34606 : List (BitVec (edgeCount 12)) :=
  [missing34605]
abbrev records34605_34606 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34605]
theorem aligned34605_34606 :
    AlignedValid 12 4 missing34605_34606 records34605_34606 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34605
    maskCheck34605 AlignedValid.nil

def missing34604_34606 : List (BitVec (edgeCount 12)) :=
  missing34604_34605 ++ missing34605_34606
abbrev records34604_34606 : List Blob :=
  records34604_34605 ++ records34605_34606
theorem aligned34604_34606 :
    AlignedValid 12 4 missing34604_34606 records34604_34606 :=
  aligned34604_34605.append aligned34605_34606

def missing34606_34607 : List (BitVec (edgeCount 12)) :=
  [missing34606]
abbrev records34606_34607 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34606]
theorem aligned34606_34607 :
    AlignedValid 12 4 missing34606_34607 records34606_34607 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34606
    maskCheck34606 AlignedValid.nil

def missing34607_34608 : List (BitVec (edgeCount 12)) :=
  [missing34607]
abbrev records34607_34608 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34607]
theorem aligned34607_34608 :
    AlignedValid 12 4 missing34607_34608 records34607_34608 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34607
    maskCheck34607 AlignedValid.nil

def missing34606_34608 : List (BitVec (edgeCount 12)) :=
  missing34606_34607 ++ missing34607_34608
abbrev records34606_34608 : List Blob :=
  records34606_34607 ++ records34607_34608
theorem aligned34606_34608 :
    AlignedValid 12 4 missing34606_34608 records34606_34608 :=
  aligned34606_34607.append aligned34607_34608

def missing34604_34608 : List (BitVec (edgeCount 12)) :=
  missing34604_34606 ++ missing34606_34608
abbrev records34604_34608 : List Blob :=
  records34604_34606 ++ records34606_34608
theorem aligned34604_34608 :
    AlignedValid 12 4 missing34604_34608 records34604_34608 :=
  aligned34604_34606.append aligned34606_34608

def missing34600_34608 : List (BitVec (edgeCount 12)) :=
  missing34600_34604 ++ missing34604_34608
abbrev records34600_34608 : List Blob :=
  records34600_34604 ++ records34604_34608
theorem aligned34600_34608 :
    AlignedValid 12 4 missing34600_34608 records34600_34608 :=
  aligned34600_34604.append aligned34604_34608

def missing34592_34608 : List (BitVec (edgeCount 12)) :=
  missing34592_34600 ++ missing34600_34608
abbrev records34592_34608 : List Blob :=
  records34592_34600 ++ records34600_34608
theorem aligned34592_34608 :
    AlignedValid 12 4 missing34592_34608 records34592_34608 :=
  aligned34592_34600.append aligned34600_34608

def missing34608_34609 : List (BitVec (edgeCount 12)) :=
  [missing34608]
abbrev records34608_34609 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34608]
theorem aligned34608_34609 :
    AlignedValid 12 4 missing34608_34609 records34608_34609 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34608
    maskCheck34608 AlignedValid.nil

def missing34609_34610 : List (BitVec (edgeCount 12)) :=
  [missing34609]
abbrev records34609_34610 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34609]
theorem aligned34609_34610 :
    AlignedValid 12 4 missing34609_34610 records34609_34610 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34609
    maskCheck34609 AlignedValid.nil

def missing34608_34610 : List (BitVec (edgeCount 12)) :=
  missing34608_34609 ++ missing34609_34610
abbrev records34608_34610 : List Blob :=
  records34608_34609 ++ records34609_34610
theorem aligned34608_34610 :
    AlignedValid 12 4 missing34608_34610 records34608_34610 :=
  aligned34608_34609.append aligned34609_34610

def missing34610_34611 : List (BitVec (edgeCount 12)) :=
  [missing34610]
abbrev records34610_34611 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34610]
theorem aligned34610_34611 :
    AlignedValid 12 4 missing34610_34611 records34610_34611 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34610
    maskCheck34610 AlignedValid.nil

def missing34611_34612 : List (BitVec (edgeCount 12)) :=
  [missing34611]
abbrev records34611_34612 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34611]
theorem aligned34611_34612 :
    AlignedValid 12 4 missing34611_34612 records34611_34612 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34611
    maskCheck34611 AlignedValid.nil

def missing34610_34612 : List (BitVec (edgeCount 12)) :=
  missing34610_34611 ++ missing34611_34612
abbrev records34610_34612 : List Blob :=
  records34610_34611 ++ records34611_34612
theorem aligned34610_34612 :
    AlignedValid 12 4 missing34610_34612 records34610_34612 :=
  aligned34610_34611.append aligned34611_34612

def missing34608_34612 : List (BitVec (edgeCount 12)) :=
  missing34608_34610 ++ missing34610_34612
abbrev records34608_34612 : List Blob :=
  records34608_34610 ++ records34610_34612
theorem aligned34608_34612 :
    AlignedValid 12 4 missing34608_34612 records34608_34612 :=
  aligned34608_34610.append aligned34610_34612

def missing34612_34613 : List (BitVec (edgeCount 12)) :=
  [missing34612]
abbrev records34612_34613 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34612]
theorem aligned34612_34613 :
    AlignedValid 12 4 missing34612_34613 records34612_34613 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34612
    maskCheck34612 AlignedValid.nil

def missing34613_34614 : List (BitVec (edgeCount 12)) :=
  [missing34613]
abbrev records34613_34614 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34613]
theorem aligned34613_34614 :
    AlignedValid 12 4 missing34613_34614 records34613_34614 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34613
    maskCheck34613 AlignedValid.nil

def missing34612_34614 : List (BitVec (edgeCount 12)) :=
  missing34612_34613 ++ missing34613_34614
abbrev records34612_34614 : List Blob :=
  records34612_34613 ++ records34613_34614
theorem aligned34612_34614 :
    AlignedValid 12 4 missing34612_34614 records34612_34614 :=
  aligned34612_34613.append aligned34613_34614

def missing34614_34615 : List (BitVec (edgeCount 12)) :=
  [missing34614]
abbrev records34614_34615 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34614]
theorem aligned34614_34615 :
    AlignedValid 12 4 missing34614_34615 records34614_34615 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34614
    maskCheck34614 AlignedValid.nil

def missing34615_34616 : List (BitVec (edgeCount 12)) :=
  [missing34615]
abbrev records34615_34616 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34615]
theorem aligned34615_34616 :
    AlignedValid 12 4 missing34615_34616 records34615_34616 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34615
    maskCheck34615 AlignedValid.nil

def missing34614_34616 : List (BitVec (edgeCount 12)) :=
  missing34614_34615 ++ missing34615_34616
abbrev records34614_34616 : List Blob :=
  records34614_34615 ++ records34615_34616
theorem aligned34614_34616 :
    AlignedValid 12 4 missing34614_34616 records34614_34616 :=
  aligned34614_34615.append aligned34615_34616

def missing34612_34616 : List (BitVec (edgeCount 12)) :=
  missing34612_34614 ++ missing34614_34616
abbrev records34612_34616 : List Blob :=
  records34612_34614 ++ records34614_34616
theorem aligned34612_34616 :
    AlignedValid 12 4 missing34612_34616 records34612_34616 :=
  aligned34612_34614.append aligned34614_34616

def missing34608_34616 : List (BitVec (edgeCount 12)) :=
  missing34608_34612 ++ missing34612_34616
abbrev records34608_34616 : List Blob :=
  records34608_34612 ++ records34612_34616
theorem aligned34608_34616 :
    AlignedValid 12 4 missing34608_34616 records34608_34616 :=
  aligned34608_34612.append aligned34612_34616

def missing34616_34617 : List (BitVec (edgeCount 12)) :=
  [missing34616]
abbrev records34616_34617 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34616]
theorem aligned34616_34617 :
    AlignedValid 12 4 missing34616_34617 records34616_34617 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34616
    maskCheck34616 AlignedValid.nil

def missing34617_34618 : List (BitVec (edgeCount 12)) :=
  [missing34617]
abbrev records34617_34618 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34617]
theorem aligned34617_34618 :
    AlignedValid 12 4 missing34617_34618 records34617_34618 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34617
    maskCheck34617 AlignedValid.nil

def missing34616_34618 : List (BitVec (edgeCount 12)) :=
  missing34616_34617 ++ missing34617_34618
abbrev records34616_34618 : List Blob :=
  records34616_34617 ++ records34617_34618
theorem aligned34616_34618 :
    AlignedValid 12 4 missing34616_34618 records34616_34618 :=
  aligned34616_34617.append aligned34617_34618

def missing34618_34619 : List (BitVec (edgeCount 12)) :=
  [missing34618]
abbrev records34618_34619 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34618]
theorem aligned34618_34619 :
    AlignedValid 12 4 missing34618_34619 records34618_34619 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34618
    maskCheck34618 AlignedValid.nil

def missing34619_34620 : List (BitVec (edgeCount 12)) :=
  [missing34619]
abbrev records34619_34620 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34619]
theorem aligned34619_34620 :
    AlignedValid 12 4 missing34619_34620 records34619_34620 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34619
    maskCheck34619 AlignedValid.nil

def missing34618_34620 : List (BitVec (edgeCount 12)) :=
  missing34618_34619 ++ missing34619_34620
abbrev records34618_34620 : List Blob :=
  records34618_34619 ++ records34619_34620
theorem aligned34618_34620 :
    AlignedValid 12 4 missing34618_34620 records34618_34620 :=
  aligned34618_34619.append aligned34619_34620

def missing34616_34620 : List (BitVec (edgeCount 12)) :=
  missing34616_34618 ++ missing34618_34620
abbrev records34616_34620 : List Blob :=
  records34616_34618 ++ records34618_34620
theorem aligned34616_34620 :
    AlignedValid 12 4 missing34616_34620 records34616_34620 :=
  aligned34616_34618.append aligned34618_34620

def missing34620_34621 : List (BitVec (edgeCount 12)) :=
  [missing34620]
abbrev records34620_34621 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34620]
theorem aligned34620_34621 :
    AlignedValid 12 4 missing34620_34621 records34620_34621 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34620
    maskCheck34620 AlignedValid.nil

def missing34621_34622 : List (BitVec (edgeCount 12)) :=
  [missing34621]
abbrev records34621_34622 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34621]
theorem aligned34621_34622 :
    AlignedValid 12 4 missing34621_34622 records34621_34622 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34621
    maskCheck34621 AlignedValid.nil

def missing34620_34622 : List (BitVec (edgeCount 12)) :=
  missing34620_34621 ++ missing34621_34622
abbrev records34620_34622 : List Blob :=
  records34620_34621 ++ records34621_34622
theorem aligned34620_34622 :
    AlignedValid 12 4 missing34620_34622 records34620_34622 :=
  aligned34620_34621.append aligned34621_34622

def missing34622_34623 : List (BitVec (edgeCount 12)) :=
  [missing34622]
abbrev records34622_34623 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34622]
theorem aligned34622_34623 :
    AlignedValid 12 4 missing34622_34623 records34622_34623 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34622
    maskCheck34622 AlignedValid.nil

def missing34623_34624 : List (BitVec (edgeCount 12)) :=
  [missing34623]
abbrev records34623_34624 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34623]
theorem aligned34623_34624 :
    AlignedValid 12 4 missing34623_34624 records34623_34624 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34623
    maskCheck34623 AlignedValid.nil

def missing34622_34624 : List (BitVec (edgeCount 12)) :=
  missing34622_34623 ++ missing34623_34624
abbrev records34622_34624 : List Blob :=
  records34622_34623 ++ records34623_34624
theorem aligned34622_34624 :
    AlignedValid 12 4 missing34622_34624 records34622_34624 :=
  aligned34622_34623.append aligned34623_34624

def missing34620_34624 : List (BitVec (edgeCount 12)) :=
  missing34620_34622 ++ missing34622_34624
abbrev records34620_34624 : List Blob :=
  records34620_34622 ++ records34622_34624
theorem aligned34620_34624 :
    AlignedValid 12 4 missing34620_34624 records34620_34624 :=
  aligned34620_34622.append aligned34622_34624

def missing34616_34624 : List (BitVec (edgeCount 12)) :=
  missing34616_34620 ++ missing34620_34624
abbrev records34616_34624 : List Blob :=
  records34616_34620 ++ records34620_34624
theorem aligned34616_34624 :
    AlignedValid 12 4 missing34616_34624 records34616_34624 :=
  aligned34616_34620.append aligned34620_34624

def missing34608_34624 : List (BitVec (edgeCount 12)) :=
  missing34608_34616 ++ missing34616_34624
abbrev records34608_34624 : List Blob :=
  records34608_34616 ++ records34616_34624
theorem aligned34608_34624 :
    AlignedValid 12 4 missing34608_34624 records34608_34624 :=
  aligned34608_34616.append aligned34616_34624

def missing34592_34624 : List (BitVec (edgeCount 12)) :=
  missing34592_34608 ++ missing34608_34624
abbrev records34592_34624 : List Blob :=
  records34592_34608 ++ records34608_34624
theorem aligned34592_34624 :
    AlignedValid 12 4 missing34592_34624 records34592_34624 :=
  aligned34592_34608.append aligned34608_34624

def missing34560_34624 : List (BitVec (edgeCount 12)) :=
  missing34560_34592 ++ missing34592_34624
abbrev records34560_34624 : List Blob :=
  records34560_34592 ++ records34592_34624
theorem aligned34560_34624 :
    AlignedValid 12 4 missing34560_34624 records34560_34624 :=
  aligned34560_34592.append aligned34592_34624

def missing34624_34625 : List (BitVec (edgeCount 12)) :=
  [missing34624]
abbrev records34624_34625 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34624]
theorem aligned34624_34625 :
    AlignedValid 12 4 missing34624_34625 records34624_34625 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34624
    maskCheck34624 AlignedValid.nil

def missing34625_34626 : List (BitVec (edgeCount 12)) :=
  [missing34625]
abbrev records34625_34626 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34625]
theorem aligned34625_34626 :
    AlignedValid 12 4 missing34625_34626 records34625_34626 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34625
    maskCheck34625 AlignedValid.nil

def missing34624_34626 : List (BitVec (edgeCount 12)) :=
  missing34624_34625 ++ missing34625_34626
abbrev records34624_34626 : List Blob :=
  records34624_34625 ++ records34625_34626
theorem aligned34624_34626 :
    AlignedValid 12 4 missing34624_34626 records34624_34626 :=
  aligned34624_34625.append aligned34625_34626

def missing34626_34627 : List (BitVec (edgeCount 12)) :=
  [missing34626]
abbrev records34626_34627 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34626]
theorem aligned34626_34627 :
    AlignedValid 12 4 missing34626_34627 records34626_34627 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34626
    maskCheck34626 AlignedValid.nil

def missing34627_34628 : List (BitVec (edgeCount 12)) :=
  [missing34627]
abbrev records34627_34628 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34627]
theorem aligned34627_34628 :
    AlignedValid 12 4 missing34627_34628 records34627_34628 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34627
    maskCheck34627 AlignedValid.nil

def missing34626_34628 : List (BitVec (edgeCount 12)) :=
  missing34626_34627 ++ missing34627_34628
abbrev records34626_34628 : List Blob :=
  records34626_34627 ++ records34627_34628
theorem aligned34626_34628 :
    AlignedValid 12 4 missing34626_34628 records34626_34628 :=
  aligned34626_34627.append aligned34627_34628

def missing34624_34628 : List (BitVec (edgeCount 12)) :=
  missing34624_34626 ++ missing34626_34628
abbrev records34624_34628 : List Blob :=
  records34624_34626 ++ records34626_34628
theorem aligned34624_34628 :
    AlignedValid 12 4 missing34624_34628 records34624_34628 :=
  aligned34624_34626.append aligned34626_34628

def missing34628_34629 : List (BitVec (edgeCount 12)) :=
  [missing34628]
abbrev records34628_34629 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34628]
theorem aligned34628_34629 :
    AlignedValid 12 4 missing34628_34629 records34628_34629 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34628
    maskCheck34628 AlignedValid.nil

def missing34629_34630 : List (BitVec (edgeCount 12)) :=
  [missing34629]
abbrev records34629_34630 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34629]
theorem aligned34629_34630 :
    AlignedValid 12 4 missing34629_34630 records34629_34630 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34629
    maskCheck34629 AlignedValid.nil

def missing34628_34630 : List (BitVec (edgeCount 12)) :=
  missing34628_34629 ++ missing34629_34630
abbrev records34628_34630 : List Blob :=
  records34628_34629 ++ records34629_34630
theorem aligned34628_34630 :
    AlignedValid 12 4 missing34628_34630 records34628_34630 :=
  aligned34628_34629.append aligned34629_34630

def missing34630_34631 : List (BitVec (edgeCount 12)) :=
  [missing34630]
abbrev records34630_34631 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34630]
theorem aligned34630_34631 :
    AlignedValid 12 4 missing34630_34631 records34630_34631 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34630
    maskCheck34630 AlignedValid.nil

def missing34631_34632 : List (BitVec (edgeCount 12)) :=
  [missing34631]
abbrev records34631_34632 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34631]
theorem aligned34631_34632 :
    AlignedValid 12 4 missing34631_34632 records34631_34632 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34631
    maskCheck34631 AlignedValid.nil

def missing34630_34632 : List (BitVec (edgeCount 12)) :=
  missing34630_34631 ++ missing34631_34632
abbrev records34630_34632 : List Blob :=
  records34630_34631 ++ records34631_34632
theorem aligned34630_34632 :
    AlignedValid 12 4 missing34630_34632 records34630_34632 :=
  aligned34630_34631.append aligned34631_34632

def missing34628_34632 : List (BitVec (edgeCount 12)) :=
  missing34628_34630 ++ missing34630_34632
abbrev records34628_34632 : List Blob :=
  records34628_34630 ++ records34630_34632
theorem aligned34628_34632 :
    AlignedValid 12 4 missing34628_34632 records34628_34632 :=
  aligned34628_34630.append aligned34630_34632

def missing34624_34632 : List (BitVec (edgeCount 12)) :=
  missing34624_34628 ++ missing34628_34632
abbrev records34624_34632 : List Blob :=
  records34624_34628 ++ records34628_34632
theorem aligned34624_34632 :
    AlignedValid 12 4 missing34624_34632 records34624_34632 :=
  aligned34624_34628.append aligned34628_34632

def missing34632_34633 : List (BitVec (edgeCount 12)) :=
  [missing34632]
abbrev records34632_34633 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34632]
theorem aligned34632_34633 :
    AlignedValid 12 4 missing34632_34633 records34632_34633 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34632
    maskCheck34632 AlignedValid.nil

def missing34633_34634 : List (BitVec (edgeCount 12)) :=
  [missing34633]
abbrev records34633_34634 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34633]
theorem aligned34633_34634 :
    AlignedValid 12 4 missing34633_34634 records34633_34634 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34633
    maskCheck34633 AlignedValid.nil

def missing34632_34634 : List (BitVec (edgeCount 12)) :=
  missing34632_34633 ++ missing34633_34634
abbrev records34632_34634 : List Blob :=
  records34632_34633 ++ records34633_34634
theorem aligned34632_34634 :
    AlignedValid 12 4 missing34632_34634 records34632_34634 :=
  aligned34632_34633.append aligned34633_34634

def missing34634_34635 : List (BitVec (edgeCount 12)) :=
  [missing34634]
abbrev records34634_34635 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34634]
theorem aligned34634_34635 :
    AlignedValid 12 4 missing34634_34635 records34634_34635 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34634
    maskCheck34634 AlignedValid.nil

def missing34635_34636 : List (BitVec (edgeCount 12)) :=
  [missing34635]
abbrev records34635_34636 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34635]
theorem aligned34635_34636 :
    AlignedValid 12 4 missing34635_34636 records34635_34636 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34635
    maskCheck34635 AlignedValid.nil

def missing34634_34636 : List (BitVec (edgeCount 12)) :=
  missing34634_34635 ++ missing34635_34636
abbrev records34634_34636 : List Blob :=
  records34634_34635 ++ records34635_34636
theorem aligned34634_34636 :
    AlignedValid 12 4 missing34634_34636 records34634_34636 :=
  aligned34634_34635.append aligned34635_34636

def missing34632_34636 : List (BitVec (edgeCount 12)) :=
  missing34632_34634 ++ missing34634_34636
abbrev records34632_34636 : List Blob :=
  records34632_34634 ++ records34634_34636
theorem aligned34632_34636 :
    AlignedValid 12 4 missing34632_34636 records34632_34636 :=
  aligned34632_34634.append aligned34634_34636

def missing34636_34637 : List (BitVec (edgeCount 12)) :=
  [missing34636]
abbrev records34636_34637 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34636]
theorem aligned34636_34637 :
    AlignedValid 12 4 missing34636_34637 records34636_34637 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34636
    maskCheck34636 AlignedValid.nil

def missing34637_34638 : List (BitVec (edgeCount 12)) :=
  [missing34637]
abbrev records34637_34638 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34637]
theorem aligned34637_34638 :
    AlignedValid 12 4 missing34637_34638 records34637_34638 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34637
    maskCheck34637 AlignedValid.nil

def missing34636_34638 : List (BitVec (edgeCount 12)) :=
  missing34636_34637 ++ missing34637_34638
abbrev records34636_34638 : List Blob :=
  records34636_34637 ++ records34637_34638
theorem aligned34636_34638 :
    AlignedValid 12 4 missing34636_34638 records34636_34638 :=
  aligned34636_34637.append aligned34637_34638

def missing34638_34639 : List (BitVec (edgeCount 12)) :=
  [missing34638]
abbrev records34638_34639 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34638]
theorem aligned34638_34639 :
    AlignedValid 12 4 missing34638_34639 records34638_34639 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34638
    maskCheck34638 AlignedValid.nil

def missing34639_34640 : List (BitVec (edgeCount 12)) :=
  [missing34639]
abbrev records34639_34640 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34639]
theorem aligned34639_34640 :
    AlignedValid 12 4 missing34639_34640 records34639_34640 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34639
    maskCheck34639 AlignedValid.nil

def missing34638_34640 : List (BitVec (edgeCount 12)) :=
  missing34638_34639 ++ missing34639_34640
abbrev records34638_34640 : List Blob :=
  records34638_34639 ++ records34639_34640
theorem aligned34638_34640 :
    AlignedValid 12 4 missing34638_34640 records34638_34640 :=
  aligned34638_34639.append aligned34639_34640

def missing34636_34640 : List (BitVec (edgeCount 12)) :=
  missing34636_34638 ++ missing34638_34640
abbrev records34636_34640 : List Blob :=
  records34636_34638 ++ records34638_34640
theorem aligned34636_34640 :
    AlignedValid 12 4 missing34636_34640 records34636_34640 :=
  aligned34636_34638.append aligned34638_34640

def missing34632_34640 : List (BitVec (edgeCount 12)) :=
  missing34632_34636 ++ missing34636_34640
abbrev records34632_34640 : List Blob :=
  records34632_34636 ++ records34636_34640
theorem aligned34632_34640 :
    AlignedValid 12 4 missing34632_34640 records34632_34640 :=
  aligned34632_34636.append aligned34636_34640

def missing34624_34640 : List (BitVec (edgeCount 12)) :=
  missing34624_34632 ++ missing34632_34640
abbrev records34624_34640 : List Blob :=
  records34624_34632 ++ records34632_34640
theorem aligned34624_34640 :
    AlignedValid 12 4 missing34624_34640 records34624_34640 :=
  aligned34624_34632.append aligned34632_34640

def missing34640_34641 : List (BitVec (edgeCount 12)) :=
  [missing34640]
abbrev records34640_34641 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34640]
theorem aligned34640_34641 :
    AlignedValid 12 4 missing34640_34641 records34640_34641 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34640
    maskCheck34640 AlignedValid.nil

def missing34641_34642 : List (BitVec (edgeCount 12)) :=
  [missing34641]
abbrev records34641_34642 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34641]
theorem aligned34641_34642 :
    AlignedValid 12 4 missing34641_34642 records34641_34642 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34641
    maskCheck34641 AlignedValid.nil

def missing34640_34642 : List (BitVec (edgeCount 12)) :=
  missing34640_34641 ++ missing34641_34642
abbrev records34640_34642 : List Blob :=
  records34640_34641 ++ records34641_34642
theorem aligned34640_34642 :
    AlignedValid 12 4 missing34640_34642 records34640_34642 :=
  aligned34640_34641.append aligned34641_34642

def missing34642_34643 : List (BitVec (edgeCount 12)) :=
  [missing34642]
abbrev records34642_34643 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34642]
theorem aligned34642_34643 :
    AlignedValid 12 4 missing34642_34643 records34642_34643 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34642
    maskCheck34642 AlignedValid.nil

def missing34643_34644 : List (BitVec (edgeCount 12)) :=
  [missing34643]
abbrev records34643_34644 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34643]
theorem aligned34643_34644 :
    AlignedValid 12 4 missing34643_34644 records34643_34644 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34643
    maskCheck34643 AlignedValid.nil

def missing34642_34644 : List (BitVec (edgeCount 12)) :=
  missing34642_34643 ++ missing34643_34644
abbrev records34642_34644 : List Blob :=
  records34642_34643 ++ records34643_34644
theorem aligned34642_34644 :
    AlignedValid 12 4 missing34642_34644 records34642_34644 :=
  aligned34642_34643.append aligned34643_34644

def missing34640_34644 : List (BitVec (edgeCount 12)) :=
  missing34640_34642 ++ missing34642_34644
abbrev records34640_34644 : List Blob :=
  records34640_34642 ++ records34642_34644
theorem aligned34640_34644 :
    AlignedValid 12 4 missing34640_34644 records34640_34644 :=
  aligned34640_34642.append aligned34642_34644

def missing34644_34645 : List (BitVec (edgeCount 12)) :=
  [missing34644]
abbrev records34644_34645 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34644]
theorem aligned34644_34645 :
    AlignedValid 12 4 missing34644_34645 records34644_34645 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34644
    maskCheck34644 AlignedValid.nil

def missing34645_34646 : List (BitVec (edgeCount 12)) :=
  [missing34645]
abbrev records34645_34646 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34645]
theorem aligned34645_34646 :
    AlignedValid 12 4 missing34645_34646 records34645_34646 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34645
    maskCheck34645 AlignedValid.nil

def missing34644_34646 : List (BitVec (edgeCount 12)) :=
  missing34644_34645 ++ missing34645_34646
abbrev records34644_34646 : List Blob :=
  records34644_34645 ++ records34645_34646
theorem aligned34644_34646 :
    AlignedValid 12 4 missing34644_34646 records34644_34646 :=
  aligned34644_34645.append aligned34645_34646

def missing34646_34647 : List (BitVec (edgeCount 12)) :=
  [missing34646]
abbrev records34646_34647 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34646]
theorem aligned34646_34647 :
    AlignedValid 12 4 missing34646_34647 records34646_34647 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34646
    maskCheck34646 AlignedValid.nil

def missing34647_34648 : List (BitVec (edgeCount 12)) :=
  [missing34647]
abbrev records34647_34648 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34647]
theorem aligned34647_34648 :
    AlignedValid 12 4 missing34647_34648 records34647_34648 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34647
    maskCheck34647 AlignedValid.nil

def missing34646_34648 : List (BitVec (edgeCount 12)) :=
  missing34646_34647 ++ missing34647_34648
abbrev records34646_34648 : List Blob :=
  records34646_34647 ++ records34647_34648
theorem aligned34646_34648 :
    AlignedValid 12 4 missing34646_34648 records34646_34648 :=
  aligned34646_34647.append aligned34647_34648

def missing34644_34648 : List (BitVec (edgeCount 12)) :=
  missing34644_34646 ++ missing34646_34648
abbrev records34644_34648 : List Blob :=
  records34644_34646 ++ records34646_34648
theorem aligned34644_34648 :
    AlignedValid 12 4 missing34644_34648 records34644_34648 :=
  aligned34644_34646.append aligned34646_34648

def missing34640_34648 : List (BitVec (edgeCount 12)) :=
  missing34640_34644 ++ missing34644_34648
abbrev records34640_34648 : List Blob :=
  records34640_34644 ++ records34644_34648
theorem aligned34640_34648 :
    AlignedValid 12 4 missing34640_34648 records34640_34648 :=
  aligned34640_34644.append aligned34644_34648

def missing34648_34649 : List (BitVec (edgeCount 12)) :=
  [missing34648]
abbrev records34648_34649 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34648]
theorem aligned34648_34649 :
    AlignedValid 12 4 missing34648_34649 records34648_34649 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34648
    maskCheck34648 AlignedValid.nil

def missing34649_34650 : List (BitVec (edgeCount 12)) :=
  [missing34649]
abbrev records34649_34650 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34649]
theorem aligned34649_34650 :
    AlignedValid 12 4 missing34649_34650 records34649_34650 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34649
    maskCheck34649 AlignedValid.nil

def missing34648_34650 : List (BitVec (edgeCount 12)) :=
  missing34648_34649 ++ missing34649_34650
abbrev records34648_34650 : List Blob :=
  records34648_34649 ++ records34649_34650
theorem aligned34648_34650 :
    AlignedValid 12 4 missing34648_34650 records34648_34650 :=
  aligned34648_34649.append aligned34649_34650

def missing34650_34651 : List (BitVec (edgeCount 12)) :=
  [missing34650]
abbrev records34650_34651 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34650]
theorem aligned34650_34651 :
    AlignedValid 12 4 missing34650_34651 records34650_34651 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34650
    maskCheck34650 AlignedValid.nil

def missing34651_34652 : List (BitVec (edgeCount 12)) :=
  [missing34651]
abbrev records34651_34652 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34651]
theorem aligned34651_34652 :
    AlignedValid 12 4 missing34651_34652 records34651_34652 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34651
    maskCheck34651 AlignedValid.nil

def missing34650_34652 : List (BitVec (edgeCount 12)) :=
  missing34650_34651 ++ missing34651_34652
abbrev records34650_34652 : List Blob :=
  records34650_34651 ++ records34651_34652
theorem aligned34650_34652 :
    AlignedValid 12 4 missing34650_34652 records34650_34652 :=
  aligned34650_34651.append aligned34651_34652

def missing34648_34652 : List (BitVec (edgeCount 12)) :=
  missing34648_34650 ++ missing34650_34652
abbrev records34648_34652 : List Blob :=
  records34648_34650 ++ records34650_34652
theorem aligned34648_34652 :
    AlignedValid 12 4 missing34648_34652 records34648_34652 :=
  aligned34648_34650.append aligned34650_34652

def missing34652_34653 : List (BitVec (edgeCount 12)) :=
  [missing34652]
abbrev records34652_34653 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34652]
theorem aligned34652_34653 :
    AlignedValid 12 4 missing34652_34653 records34652_34653 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34652
    maskCheck34652 AlignedValid.nil

def missing34653_34654 : List (BitVec (edgeCount 12)) :=
  [missing34653]
abbrev records34653_34654 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34653]
theorem aligned34653_34654 :
    AlignedValid 12 4 missing34653_34654 records34653_34654 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34653
    maskCheck34653 AlignedValid.nil

def missing34652_34654 : List (BitVec (edgeCount 12)) :=
  missing34652_34653 ++ missing34653_34654
abbrev records34652_34654 : List Blob :=
  records34652_34653 ++ records34653_34654
theorem aligned34652_34654 :
    AlignedValid 12 4 missing34652_34654 records34652_34654 :=
  aligned34652_34653.append aligned34653_34654

def missing34654_34655 : List (BitVec (edgeCount 12)) :=
  [missing34654]
abbrev records34654_34655 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34654]
theorem aligned34654_34655 :
    AlignedValid 12 4 missing34654_34655 records34654_34655 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34654
    maskCheck34654 AlignedValid.nil

def missing34655_34656 : List (BitVec (edgeCount 12)) :=
  [missing34655]
abbrev records34655_34656 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34655]
theorem aligned34655_34656 :
    AlignedValid 12 4 missing34655_34656 records34655_34656 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34655
    maskCheck34655 AlignedValid.nil

def missing34654_34656 : List (BitVec (edgeCount 12)) :=
  missing34654_34655 ++ missing34655_34656
abbrev records34654_34656 : List Blob :=
  records34654_34655 ++ records34655_34656
theorem aligned34654_34656 :
    AlignedValid 12 4 missing34654_34656 records34654_34656 :=
  aligned34654_34655.append aligned34655_34656

def missing34652_34656 : List (BitVec (edgeCount 12)) :=
  missing34652_34654 ++ missing34654_34656
abbrev records34652_34656 : List Blob :=
  records34652_34654 ++ records34654_34656
theorem aligned34652_34656 :
    AlignedValid 12 4 missing34652_34656 records34652_34656 :=
  aligned34652_34654.append aligned34654_34656

def missing34648_34656 : List (BitVec (edgeCount 12)) :=
  missing34648_34652 ++ missing34652_34656
abbrev records34648_34656 : List Blob :=
  records34648_34652 ++ records34652_34656
theorem aligned34648_34656 :
    AlignedValid 12 4 missing34648_34656 records34648_34656 :=
  aligned34648_34652.append aligned34652_34656

def missing34640_34656 : List (BitVec (edgeCount 12)) :=
  missing34640_34648 ++ missing34648_34656
abbrev records34640_34656 : List Blob :=
  records34640_34648 ++ records34648_34656
theorem aligned34640_34656 :
    AlignedValid 12 4 missing34640_34656 records34640_34656 :=
  aligned34640_34648.append aligned34648_34656

def missing34624_34656 : List (BitVec (edgeCount 12)) :=
  missing34624_34640 ++ missing34640_34656
abbrev records34624_34656 : List Blob :=
  records34624_34640 ++ records34640_34656
theorem aligned34624_34656 :
    AlignedValid 12 4 missing34624_34656 records34624_34656 :=
  aligned34624_34640.append aligned34640_34656

def missing34656_34657 : List (BitVec (edgeCount 12)) :=
  [missing34656]
abbrev records34656_34657 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34656]
theorem aligned34656_34657 :
    AlignedValid 12 4 missing34656_34657 records34656_34657 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34656
    maskCheck34656 AlignedValid.nil

def missing34657_34658 : List (BitVec (edgeCount 12)) :=
  [missing34657]
abbrev records34657_34658 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34657]
theorem aligned34657_34658 :
    AlignedValid 12 4 missing34657_34658 records34657_34658 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34657
    maskCheck34657 AlignedValid.nil

def missing34656_34658 : List (BitVec (edgeCount 12)) :=
  missing34656_34657 ++ missing34657_34658
abbrev records34656_34658 : List Blob :=
  records34656_34657 ++ records34657_34658
theorem aligned34656_34658 :
    AlignedValid 12 4 missing34656_34658 records34656_34658 :=
  aligned34656_34657.append aligned34657_34658

def missing34658_34659 : List (BitVec (edgeCount 12)) :=
  [missing34658]
abbrev records34658_34659 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34658]
theorem aligned34658_34659 :
    AlignedValid 12 4 missing34658_34659 records34658_34659 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34658
    maskCheck34658 AlignedValid.nil

def missing34659_34660 : List (BitVec (edgeCount 12)) :=
  [missing34659]
abbrev records34659_34660 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34659]
theorem aligned34659_34660 :
    AlignedValid 12 4 missing34659_34660 records34659_34660 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34659
    maskCheck34659 AlignedValid.nil

def missing34658_34660 : List (BitVec (edgeCount 12)) :=
  missing34658_34659 ++ missing34659_34660
abbrev records34658_34660 : List Blob :=
  records34658_34659 ++ records34659_34660
theorem aligned34658_34660 :
    AlignedValid 12 4 missing34658_34660 records34658_34660 :=
  aligned34658_34659.append aligned34659_34660

def missing34656_34660 : List (BitVec (edgeCount 12)) :=
  missing34656_34658 ++ missing34658_34660
abbrev records34656_34660 : List Blob :=
  records34656_34658 ++ records34658_34660
theorem aligned34656_34660 :
    AlignedValid 12 4 missing34656_34660 records34656_34660 :=
  aligned34656_34658.append aligned34658_34660

def missing34660_34661 : List (BitVec (edgeCount 12)) :=
  [missing34660]
abbrev records34660_34661 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34660]
theorem aligned34660_34661 :
    AlignedValid 12 4 missing34660_34661 records34660_34661 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34660
    maskCheck34660 AlignedValid.nil

def missing34661_34662 : List (BitVec (edgeCount 12)) :=
  [missing34661]
abbrev records34661_34662 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34661]
theorem aligned34661_34662 :
    AlignedValid 12 4 missing34661_34662 records34661_34662 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34661
    maskCheck34661 AlignedValid.nil

def missing34660_34662 : List (BitVec (edgeCount 12)) :=
  missing34660_34661 ++ missing34661_34662
abbrev records34660_34662 : List Blob :=
  records34660_34661 ++ records34661_34662
theorem aligned34660_34662 :
    AlignedValid 12 4 missing34660_34662 records34660_34662 :=
  aligned34660_34661.append aligned34661_34662

def missing34662_34663 : List (BitVec (edgeCount 12)) :=
  [missing34662]
abbrev records34662_34663 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34662]
theorem aligned34662_34663 :
    AlignedValid 12 4 missing34662_34663 records34662_34663 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34662
    maskCheck34662 AlignedValid.nil

def missing34663_34664 : List (BitVec (edgeCount 12)) :=
  [missing34663]
abbrev records34663_34664 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34663]
theorem aligned34663_34664 :
    AlignedValid 12 4 missing34663_34664 records34663_34664 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34663
    maskCheck34663 AlignedValid.nil

def missing34662_34664 : List (BitVec (edgeCount 12)) :=
  missing34662_34663 ++ missing34663_34664
abbrev records34662_34664 : List Blob :=
  records34662_34663 ++ records34663_34664
theorem aligned34662_34664 :
    AlignedValid 12 4 missing34662_34664 records34662_34664 :=
  aligned34662_34663.append aligned34663_34664

def missing34660_34664 : List (BitVec (edgeCount 12)) :=
  missing34660_34662 ++ missing34662_34664
abbrev records34660_34664 : List Blob :=
  records34660_34662 ++ records34662_34664
theorem aligned34660_34664 :
    AlignedValid 12 4 missing34660_34664 records34660_34664 :=
  aligned34660_34662.append aligned34662_34664

def missing34656_34664 : List (BitVec (edgeCount 12)) :=
  missing34656_34660 ++ missing34660_34664
abbrev records34656_34664 : List Blob :=
  records34656_34660 ++ records34660_34664
theorem aligned34656_34664 :
    AlignedValid 12 4 missing34656_34664 records34656_34664 :=
  aligned34656_34660.append aligned34660_34664

def missing34664_34665 : List (BitVec (edgeCount 12)) :=
  [missing34664]
abbrev records34664_34665 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34664]
theorem aligned34664_34665 :
    AlignedValid 12 4 missing34664_34665 records34664_34665 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34664
    maskCheck34664 AlignedValid.nil

def missing34665_34666 : List (BitVec (edgeCount 12)) :=
  [missing34665]
abbrev records34665_34666 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34665]
theorem aligned34665_34666 :
    AlignedValid 12 4 missing34665_34666 records34665_34666 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34665
    maskCheck34665 AlignedValid.nil

def missing34664_34666 : List (BitVec (edgeCount 12)) :=
  missing34664_34665 ++ missing34665_34666
abbrev records34664_34666 : List Blob :=
  records34664_34665 ++ records34665_34666
theorem aligned34664_34666 :
    AlignedValid 12 4 missing34664_34666 records34664_34666 :=
  aligned34664_34665.append aligned34665_34666

def missing34666_34667 : List (BitVec (edgeCount 12)) :=
  [missing34666]
abbrev records34666_34667 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34666]
theorem aligned34666_34667 :
    AlignedValid 12 4 missing34666_34667 records34666_34667 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34666
    maskCheck34666 AlignedValid.nil

def missing34667_34668 : List (BitVec (edgeCount 12)) :=
  [missing34667]
abbrev records34667_34668 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34667]
theorem aligned34667_34668 :
    AlignedValid 12 4 missing34667_34668 records34667_34668 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34667
    maskCheck34667 AlignedValid.nil

def missing34666_34668 : List (BitVec (edgeCount 12)) :=
  missing34666_34667 ++ missing34667_34668
abbrev records34666_34668 : List Blob :=
  records34666_34667 ++ records34667_34668
theorem aligned34666_34668 :
    AlignedValid 12 4 missing34666_34668 records34666_34668 :=
  aligned34666_34667.append aligned34667_34668

def missing34664_34668 : List (BitVec (edgeCount 12)) :=
  missing34664_34666 ++ missing34666_34668
abbrev records34664_34668 : List Blob :=
  records34664_34666 ++ records34666_34668
theorem aligned34664_34668 :
    AlignedValid 12 4 missing34664_34668 records34664_34668 :=
  aligned34664_34666.append aligned34666_34668

def missing34668_34669 : List (BitVec (edgeCount 12)) :=
  [missing34668]
abbrev records34668_34669 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34668]
theorem aligned34668_34669 :
    AlignedValid 12 4 missing34668_34669 records34668_34669 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34668
    maskCheck34668 AlignedValid.nil

def missing34669_34670 : List (BitVec (edgeCount 12)) :=
  [missing34669]
abbrev records34669_34670 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34669]
theorem aligned34669_34670 :
    AlignedValid 12 4 missing34669_34670 records34669_34670 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34669
    maskCheck34669 AlignedValid.nil

def missing34668_34670 : List (BitVec (edgeCount 12)) :=
  missing34668_34669 ++ missing34669_34670
abbrev records34668_34670 : List Blob :=
  records34668_34669 ++ records34669_34670
theorem aligned34668_34670 :
    AlignedValid 12 4 missing34668_34670 records34668_34670 :=
  aligned34668_34669.append aligned34669_34670

def missing34670_34671 : List (BitVec (edgeCount 12)) :=
  [missing34670]
abbrev records34670_34671 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34670]
theorem aligned34670_34671 :
    AlignedValid 12 4 missing34670_34671 records34670_34671 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34670
    maskCheck34670 AlignedValid.nil

def missing34671_34672 : List (BitVec (edgeCount 12)) :=
  [missing34671]
abbrev records34671_34672 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34671]
theorem aligned34671_34672 :
    AlignedValid 12 4 missing34671_34672 records34671_34672 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34671
    maskCheck34671 AlignedValid.nil

def missing34670_34672 : List (BitVec (edgeCount 12)) :=
  missing34670_34671 ++ missing34671_34672
abbrev records34670_34672 : List Blob :=
  records34670_34671 ++ records34671_34672
theorem aligned34670_34672 :
    AlignedValid 12 4 missing34670_34672 records34670_34672 :=
  aligned34670_34671.append aligned34671_34672

def missing34668_34672 : List (BitVec (edgeCount 12)) :=
  missing34668_34670 ++ missing34670_34672
abbrev records34668_34672 : List Blob :=
  records34668_34670 ++ records34670_34672
theorem aligned34668_34672 :
    AlignedValid 12 4 missing34668_34672 records34668_34672 :=
  aligned34668_34670.append aligned34670_34672

def missing34664_34672 : List (BitVec (edgeCount 12)) :=
  missing34664_34668 ++ missing34668_34672
abbrev records34664_34672 : List Blob :=
  records34664_34668 ++ records34668_34672
theorem aligned34664_34672 :
    AlignedValid 12 4 missing34664_34672 records34664_34672 :=
  aligned34664_34668.append aligned34668_34672

def missing34656_34672 : List (BitVec (edgeCount 12)) :=
  missing34656_34664 ++ missing34664_34672
abbrev records34656_34672 : List Blob :=
  records34656_34664 ++ records34664_34672
theorem aligned34656_34672 :
    AlignedValid 12 4 missing34656_34672 records34656_34672 :=
  aligned34656_34664.append aligned34664_34672

def missing34672_34673 : List (BitVec (edgeCount 12)) :=
  [missing34672]
abbrev records34672_34673 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34672]
theorem aligned34672_34673 :
    AlignedValid 12 4 missing34672_34673 records34672_34673 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34672
    maskCheck34672 AlignedValid.nil

def missing34673_34674 : List (BitVec (edgeCount 12)) :=
  [missing34673]
abbrev records34673_34674 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34673]
theorem aligned34673_34674 :
    AlignedValid 12 4 missing34673_34674 records34673_34674 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34673
    maskCheck34673 AlignedValid.nil

def missing34672_34674 : List (BitVec (edgeCount 12)) :=
  missing34672_34673 ++ missing34673_34674
abbrev records34672_34674 : List Blob :=
  records34672_34673 ++ records34673_34674
theorem aligned34672_34674 :
    AlignedValid 12 4 missing34672_34674 records34672_34674 :=
  aligned34672_34673.append aligned34673_34674

def missing34674_34675 : List (BitVec (edgeCount 12)) :=
  [missing34674]
abbrev records34674_34675 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34674]
theorem aligned34674_34675 :
    AlignedValid 12 4 missing34674_34675 records34674_34675 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34674
    maskCheck34674 AlignedValid.nil

def missing34675_34676 : List (BitVec (edgeCount 12)) :=
  [missing34675]
abbrev records34675_34676 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34675]
theorem aligned34675_34676 :
    AlignedValid 12 4 missing34675_34676 records34675_34676 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34675
    maskCheck34675 AlignedValid.nil

def missing34674_34676 : List (BitVec (edgeCount 12)) :=
  missing34674_34675 ++ missing34675_34676
abbrev records34674_34676 : List Blob :=
  records34674_34675 ++ records34675_34676
theorem aligned34674_34676 :
    AlignedValid 12 4 missing34674_34676 records34674_34676 :=
  aligned34674_34675.append aligned34675_34676

def missing34672_34676 : List (BitVec (edgeCount 12)) :=
  missing34672_34674 ++ missing34674_34676
abbrev records34672_34676 : List Blob :=
  records34672_34674 ++ records34674_34676
theorem aligned34672_34676 :
    AlignedValid 12 4 missing34672_34676 records34672_34676 :=
  aligned34672_34674.append aligned34674_34676

def missing34676_34677 : List (BitVec (edgeCount 12)) :=
  [missing34676]
abbrev records34676_34677 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34676]
theorem aligned34676_34677 :
    AlignedValid 12 4 missing34676_34677 records34676_34677 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34676
    maskCheck34676 AlignedValid.nil

def missing34677_34678 : List (BitVec (edgeCount 12)) :=
  [missing34677]
abbrev records34677_34678 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34677]
theorem aligned34677_34678 :
    AlignedValid 12 4 missing34677_34678 records34677_34678 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34677
    maskCheck34677 AlignedValid.nil

def missing34676_34678 : List (BitVec (edgeCount 12)) :=
  missing34676_34677 ++ missing34677_34678
abbrev records34676_34678 : List Blob :=
  records34676_34677 ++ records34677_34678
theorem aligned34676_34678 :
    AlignedValid 12 4 missing34676_34678 records34676_34678 :=
  aligned34676_34677.append aligned34677_34678

def missing34678_34679 : List (BitVec (edgeCount 12)) :=
  [missing34678]
abbrev records34678_34679 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34678]
theorem aligned34678_34679 :
    AlignedValid 12 4 missing34678_34679 records34678_34679 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34678
    maskCheck34678 AlignedValid.nil

def missing34679_34680 : List (BitVec (edgeCount 12)) :=
  [missing34679]
abbrev records34679_34680 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34679]
theorem aligned34679_34680 :
    AlignedValid 12 4 missing34679_34680 records34679_34680 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34679
    maskCheck34679 AlignedValid.nil

def missing34678_34680 : List (BitVec (edgeCount 12)) :=
  missing34678_34679 ++ missing34679_34680
abbrev records34678_34680 : List Blob :=
  records34678_34679 ++ records34679_34680
theorem aligned34678_34680 :
    AlignedValid 12 4 missing34678_34680 records34678_34680 :=
  aligned34678_34679.append aligned34679_34680

def missing34676_34680 : List (BitVec (edgeCount 12)) :=
  missing34676_34678 ++ missing34678_34680
abbrev records34676_34680 : List Blob :=
  records34676_34678 ++ records34678_34680
theorem aligned34676_34680 :
    AlignedValid 12 4 missing34676_34680 records34676_34680 :=
  aligned34676_34678.append aligned34678_34680

def missing34672_34680 : List (BitVec (edgeCount 12)) :=
  missing34672_34676 ++ missing34676_34680
abbrev records34672_34680 : List Blob :=
  records34672_34676 ++ records34676_34680
theorem aligned34672_34680 :
    AlignedValid 12 4 missing34672_34680 records34672_34680 :=
  aligned34672_34676.append aligned34676_34680

def missing34680_34681 : List (BitVec (edgeCount 12)) :=
  [missing34680]
abbrev records34680_34681 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34680]
theorem aligned34680_34681 :
    AlignedValid 12 4 missing34680_34681 records34680_34681 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34680
    maskCheck34680 AlignedValid.nil

def missing34681_34682 : List (BitVec (edgeCount 12)) :=
  [missing34681]
abbrev records34681_34682 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34681]
theorem aligned34681_34682 :
    AlignedValid 12 4 missing34681_34682 records34681_34682 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34681
    maskCheck34681 AlignedValid.nil

def missing34680_34682 : List (BitVec (edgeCount 12)) :=
  missing34680_34681 ++ missing34681_34682
abbrev records34680_34682 : List Blob :=
  records34680_34681 ++ records34681_34682
theorem aligned34680_34682 :
    AlignedValid 12 4 missing34680_34682 records34680_34682 :=
  aligned34680_34681.append aligned34681_34682

def missing34682_34683 : List (BitVec (edgeCount 12)) :=
  [missing34682]
abbrev records34682_34683 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34682]
theorem aligned34682_34683 :
    AlignedValid 12 4 missing34682_34683 records34682_34683 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34682
    maskCheck34682 AlignedValid.nil

def missing34683_34684 : List (BitVec (edgeCount 12)) :=
  [missing34683]
abbrev records34683_34684 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34683]
theorem aligned34683_34684 :
    AlignedValid 12 4 missing34683_34684 records34683_34684 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34683
    maskCheck34683 AlignedValid.nil

def missing34682_34684 : List (BitVec (edgeCount 12)) :=
  missing34682_34683 ++ missing34683_34684
abbrev records34682_34684 : List Blob :=
  records34682_34683 ++ records34683_34684
theorem aligned34682_34684 :
    AlignedValid 12 4 missing34682_34684 records34682_34684 :=
  aligned34682_34683.append aligned34683_34684

def missing34680_34684 : List (BitVec (edgeCount 12)) :=
  missing34680_34682 ++ missing34682_34684
abbrev records34680_34684 : List Blob :=
  records34680_34682 ++ records34682_34684
theorem aligned34680_34684 :
    AlignedValid 12 4 missing34680_34684 records34680_34684 :=
  aligned34680_34682.append aligned34682_34684

def missing34684_34685 : List (BitVec (edgeCount 12)) :=
  [missing34684]
abbrev records34684_34685 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34684]
theorem aligned34684_34685 :
    AlignedValid 12 4 missing34684_34685 records34684_34685 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34684
    maskCheck34684 AlignedValid.nil

def missing34685_34686 : List (BitVec (edgeCount 12)) :=
  [missing34685]
abbrev records34685_34686 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34685]
theorem aligned34685_34686 :
    AlignedValid 12 4 missing34685_34686 records34685_34686 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34685
    maskCheck34685 AlignedValid.nil

def missing34684_34686 : List (BitVec (edgeCount 12)) :=
  missing34684_34685 ++ missing34685_34686
abbrev records34684_34686 : List Blob :=
  records34684_34685 ++ records34685_34686
theorem aligned34684_34686 :
    AlignedValid 12 4 missing34684_34686 records34684_34686 :=
  aligned34684_34685.append aligned34685_34686

def missing34686_34687 : List (BitVec (edgeCount 12)) :=
  [missing34686]
abbrev records34686_34687 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34686]
theorem aligned34686_34687 :
    AlignedValid 12 4 missing34686_34687 records34686_34687 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34686
    maskCheck34686 AlignedValid.nil

def missing34687_34688 : List (BitVec (edgeCount 12)) :=
  [missing34687]
abbrev records34687_34688 : List Blob :=
  [StrongPackedBucketN12A4Shard270.record34687]
theorem aligned34687_34688 :
    AlignedValid 12 4 missing34687_34688 records34687_34688 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard270.check34687
    maskCheck34687 AlignedValid.nil

def missing34686_34688 : List (BitVec (edgeCount 12)) :=
  missing34686_34687 ++ missing34687_34688
abbrev records34686_34688 : List Blob :=
  records34686_34687 ++ records34687_34688
theorem aligned34686_34688 :
    AlignedValid 12 4 missing34686_34688 records34686_34688 :=
  aligned34686_34687.append aligned34687_34688

def missing34684_34688 : List (BitVec (edgeCount 12)) :=
  missing34684_34686 ++ missing34686_34688
abbrev records34684_34688 : List Blob :=
  records34684_34686 ++ records34686_34688
theorem aligned34684_34688 :
    AlignedValid 12 4 missing34684_34688 records34684_34688 :=
  aligned34684_34686.append aligned34686_34688

def missing34680_34688 : List (BitVec (edgeCount 12)) :=
  missing34680_34684 ++ missing34684_34688
abbrev records34680_34688 : List Blob :=
  records34680_34684 ++ records34684_34688
theorem aligned34680_34688 :
    AlignedValid 12 4 missing34680_34688 records34680_34688 :=
  aligned34680_34684.append aligned34684_34688

def missing34672_34688 : List (BitVec (edgeCount 12)) :=
  missing34672_34680 ++ missing34680_34688
abbrev records34672_34688 : List Blob :=
  records34672_34680 ++ records34680_34688
theorem aligned34672_34688 :
    AlignedValid 12 4 missing34672_34688 records34672_34688 :=
  aligned34672_34680.append aligned34680_34688

def missing34656_34688 : List (BitVec (edgeCount 12)) :=
  missing34656_34672 ++ missing34672_34688
abbrev records34656_34688 : List Blob :=
  records34656_34672 ++ records34672_34688
theorem aligned34656_34688 :
    AlignedValid 12 4 missing34656_34688 records34656_34688 :=
  aligned34656_34672.append aligned34672_34688

def missing34624_34688 : List (BitVec (edgeCount 12)) :=
  missing34624_34656 ++ missing34656_34688
abbrev records34624_34688 : List Blob :=
  records34624_34656 ++ records34656_34688
theorem aligned34624_34688 :
    AlignedValid 12 4 missing34624_34688 records34624_34688 :=
  aligned34624_34656.append aligned34656_34688

def missing34560_34688 : List (BitVec (edgeCount 12)) :=
  missing34560_34624 ++ missing34624_34688
abbrev records34560_34688 : List Blob :=
  records34560_34624 ++ records34624_34688
theorem aligned34560_34688 :
    AlignedValid 12 4 missing34560_34688 records34560_34688 :=
  aligned34560_34624.append aligned34624_34688

abbrev missing : List (BitVec (edgeCount 12)) := missing34560_34688
abbrev records : List Blob := records34560_34688
theorem aligned : AlignedValid 12 4 missing records := aligned34560_34688

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard270
