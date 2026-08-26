/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A3Shard036

/-! Decode-only alignment checks for n=12, a=3, records 4608--4735. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard036

open PackedBucketCertificate

def missing4608 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8215235048832499712
theorem maskCheck4608 :
    checkMaskFor missing4608 StrongPackedBucketN12A3Shard036.record4608 = true := by
  decide

def missing4609 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8647580613060067328
theorem maskCheck4609 :
    checkMaskFor missing4609 StrongPackedBucketN12A3Shard036.record4609 = true := by
  decide

def missing4610 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9476242944496238592
theorem maskCheck4610 :
    checkMaskFor missing4610 StrongPackedBucketN12A3Shard036.record4610 = true := by
  decide

def missing4611 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9692415726610022400
theorem maskCheck4611 :
    checkMaskFor missing4611 StrongPackedBucketN12A3Shard036.record4611 = true := by
  decide

def missing4612 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9908588508723806208
theorem maskCheck4612 :
    checkMaskFor missing4612 StrongPackedBucketN12A3Shard036.record4612 = true := by
  decide

def missing4613 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9980646102761734144
theorem maskCheck4613 :
    checkMaskFor missing4613 StrongPackedBucketN12A3Shard036.record4613 = true := by
  decide

def missing4614 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10232847681894481920
theorem maskCheck4614 :
    checkMaskFor missing4614 StrongPackedBucketN12A3Shard036.record4614 = true := by
  decide

def missing4615 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10485049261027229696
theorem maskCheck4615 :
    checkMaskFor missing4615 StrongPackedBucketN12A3Shard036.record4615 = true := by
  decide

def missing4616 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10557106855065157632
theorem maskCheck4616 :
    checkMaskFor missing4616 StrongPackedBucketN12A3Shard036.record4616 = true := by
  decide

def missing4617 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10809308434197905408
theorem maskCheck4617 :
    checkMaskFor missing4617 StrongPackedBucketN12A3Shard036.record4617 = true := by
  decide

def missing4618 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10989452419292725248
theorem maskCheck4618 :
    checkMaskFor missing4618 StrongPackedBucketN12A3Shard036.record4618 = true := by
  decide

def missing4619 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11097538810349617152
theorem maskCheck4619 :
    checkMaskFor missing4619 StrongPackedBucketN12A3Shard036.record4619 = true := by
  decide

def missing4620 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12718834676202995712
theorem maskCheck4620 :
    checkMaskFor missing4620 StrongPackedBucketN12A3Shard036.record4620 = true := by
  decide

def missing4621 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12826921067259887616
theorem maskCheck4621 :
    checkMaskFor missing4621 StrongPackedBucketN12A3Shard036.record4621 = true := by
  decide

def missing4622 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13259266631487455232
theorem maskCheck4622 :
    checkMaskFor missing4622 StrongPackedBucketN12A3Shard036.record4622 = true := by
  decide

def missing4623 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17294491897611419648
theorem maskCheck4623 :
    checkMaskFor missing4623 StrongPackedBucketN12A3Shard036.record4623 = true := by
  decide

def missing4624 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699614981351014400
theorem maskCheck4624 :
    checkMaskFor missing4624 StrongPackedBucketN12A3Shard036.record4624 = true := by
  decide

def missing4625 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18915787763464798208
theorem maskCheck4625 :
    checkMaskFor missing4625 StrongPackedBucketN12A3Shard036.record4625 = true := by
  decide

def missing4626 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19131960545578582016
theorem maskCheck4626 :
    checkMaskFor missing4626 StrongPackedBucketN12A3Shard036.record4626 = true := by
  decide

def missing4627 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19204018139616509952
theorem maskCheck4627 :
    checkMaskFor missing4627 StrongPackedBucketN12A3Shard036.record4627 = true := by
  decide

def missing4628 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19456219718749257728
theorem maskCheck4628 :
    checkMaskFor missing4628 StrongPackedBucketN12A3Shard036.record4628 = true := by
  decide

def missing4629 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19708421297882005504
theorem maskCheck4629 :
    checkMaskFor missing4629 StrongPackedBucketN12A3Shard036.record4629 = true := by
  decide

def missing4630 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19780478891919933440
theorem maskCheck4630 :
    checkMaskFor missing4630 StrongPackedBucketN12A3Shard036.record4630 = true := by
  decide

def missing4631 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20032680471052681216
theorem maskCheck4631 :
    checkMaskFor missing4631 StrongPackedBucketN12A3Shard036.record4631 = true := by
  decide

def missing4632 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20212824456147501056
theorem maskCheck4632 :
    checkMaskFor missing4632 StrongPackedBucketN12A3Shard036.record4632 = true := by
  decide

def missing4633 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20320910847204392960
theorem maskCheck4633 :
    checkMaskFor missing4633 StrongPackedBucketN12A3Shard036.record4633 = true := by
  decide

def missing4634 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21942206713057771520
theorem maskCheck4634 :
    checkMaskFor missing4634 StrongPackedBucketN12A3Shard036.record4634 = true := by
  decide

def missing4635 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22050293104114663424
theorem maskCheck4635 :
    checkMaskFor missing4635 StrongPackedBucketN12A3Shard036.record4635 = true := by
  decide

def missing4636 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22482638668342231040
theorem maskCheck4636 :
    checkMaskFor missing4636 StrongPackedBucketN12A3Shard036.record4636 = true := by
  decide

def missing4637 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 26517863934466195456
theorem maskCheck4637 :
    checkMaskFor missing4637 StrongPackedBucketN12A3Shard036.record4637 = true := by
  decide

def missing4638 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27778871830129934336
theorem maskCheck4638 :
    checkMaskFor missing4638 StrongPackedBucketN12A3Shard036.record4638 = true := by
  decide

def missing4639 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27850929424167862272
theorem maskCheck4639 :
    checkMaskFor missing4639 StrongPackedBucketN12A3Shard036.record4639 = true := by
  decide

def missing4640 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28103131003300610048
theorem maskCheck4640 :
    checkMaskFor missing4640 StrongPackedBucketN12A3Shard036.record4640 = true := by
  decide

def missing4641 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28283274988395429888
theorem maskCheck4641 :
    checkMaskFor missing4641 StrongPackedBucketN12A3Shard036.record4641 = true := by
  decide

def missing4642 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28391361379452321792
theorem maskCheck4642 :
    checkMaskFor missing4642 StrongPackedBucketN12A3Shard036.record4642 = true := by
  decide

def missing4643 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28859735740698853376
theorem maskCheck4643 :
    checkMaskFor missing4643 StrongPackedBucketN12A3Shard036.record4643 = true := by
  decide

def missing4644 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28967822131755745280
theorem maskCheck4644 :
    checkMaskFor missing4644 StrongPackedBucketN12A3Shard036.record4644 = true := by
  decide

def missing4645 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29400167695983312896
theorem maskCheck4645 :
    checkMaskFor missing4645 StrongPackedBucketN12A3Shard036.record4645 = true := by
  decide

def missing4646 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 31129549952893583360
theorem maskCheck4646 :
    checkMaskFor missing4646 StrongPackedBucketN12A3Shard036.record4646 = true := by
  decide

def missing4647 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37146359055060566016
theorem maskCheck4647 :
    checkMaskFor missing4647 StrongPackedBucketN12A3Shard036.record4647 = true := by
  decide

def missing4648 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37362531837174349824
theorem maskCheck4648 :
    checkMaskFor missing4648 StrongPackedBucketN12A3Shard036.record4648 = true := by
  decide

def missing4649 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37578704619288133632
theorem maskCheck4649 :
    checkMaskFor missing4649 StrongPackedBucketN12A3Shard036.record4649 = true := by
  decide

def missing4650 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37650762213326061568
theorem maskCheck4650 :
    checkMaskFor missing4650 StrongPackedBucketN12A3Shard036.record4650 = true := by
  decide

def missing4651 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37902963792458809344
theorem maskCheck4651 :
    checkMaskFor missing4651 StrongPackedBucketN12A3Shard036.record4651 = true := by
  decide

def missing4652 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38155165371591557120
theorem maskCheck4652 :
    checkMaskFor missing4652 StrongPackedBucketN12A3Shard036.record4652 = true := by
  decide

def missing4653 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38227222965629485056
theorem maskCheck4653 :
    checkMaskFor missing4653 StrongPackedBucketN12A3Shard036.record4653 = true := by
  decide

def missing4654 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38479424544762232832
theorem maskCheck4654 :
    checkMaskFor missing4654 StrongPackedBucketN12A3Shard036.record4654 = true := by
  decide

def missing4655 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46225615903839485952
theorem maskCheck4655 :
    checkMaskFor missing4655 StrongPackedBucketN12A3Shard036.record4655 = true := by
  decide

def missing4656 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46297673497877413888
theorem maskCheck4656 :
    checkMaskFor missing4656 StrongPackedBucketN12A3Shard036.record4656 = true := by
  decide

def missing4657 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46549875077010161664
theorem maskCheck4657 :
    checkMaskFor missing4657 StrongPackedBucketN12A3Shard036.record4657 = true := by
  decide

def missing4658 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55448987940694261760
theorem maskCheck4658 :
    checkMaskFor missing4658 StrongPackedBucketN12A3Shard036.record4658 = true := by
  decide

def missing4659 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55521045534732189696
theorem maskCheck4659 :
    checkMaskFor missing4659 StrongPackedBucketN12A3Shard036.record4659 = true := by
  decide

def missing4660 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55773247113864937472
theorem maskCheck4660 :
    checkMaskFor missing4660 StrongPackedBucketN12A3Shard036.record4660 = true := by
  decide

def missing4661 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 541171652537352192
theorem maskCheck4661 :
    checkMaskFor missing4661 StrongPackedBucketN12A3Shard036.record4661 = true := by
  decide

def missing4662 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 829402028689063936
theorem maskCheck4662 :
    checkMaskFor missing4662 StrongPackedBucketN12A3Shard036.record4662 = true := by
  decide

def missing4663 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 973517216764919808
theorem maskCheck4663 :
    checkMaskFor missing4663 StrongPackedBucketN12A3Shard036.record4663 = true := by
  decide

def missing4664 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1405862780992487424
theorem maskCheck4664 :
    checkMaskFor missing4664 StrongPackedBucketN12A3Shard036.record4664 = true := by
  decide

def missing4665 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1549977969068343296
theorem maskCheck4665 :
    checkMaskFor missing4665 StrongPackedBucketN12A3Shard036.record4665 = true := by
  decide

def missing4666 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1838208345220055040
theorem maskCheck4666 :
    checkMaskFor missing4666 StrongPackedBucketN12A3Shard036.record4666 = true := by
  decide

def missing4667 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1910265939257982976
theorem maskCheck4667 :
    checkMaskFor missing4667 StrongPackedBucketN12A3Shard036.record4667 = true := by
  decide

def missing4668 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1946294736276946944
theorem maskCheck4668 :
    checkMaskFor missing4668 StrongPackedBucketN12A3Shard036.record4668 = true := by
  decide

def missing4669 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2090409924352802816
theorem maskCheck4669 :
    checkMaskFor missing4669 StrongPackedBucketN12A3Shard036.record4669 = true := by
  decide

def missing4670 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3567590602130325504
theorem maskCheck4670 :
    checkMaskFor missing4670 StrongPackedBucketN12A3Shard036.record4670 = true := by
  decide

def missing4671 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3639648196168253440
theorem maskCheck4671 :
    checkMaskFor missing4671 StrongPackedBucketN12A3Shard036.record4671 = true := by
  decide

def missing4672 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3675676993187217408
theorem maskCheck4672 :
    checkMaskFor missing4672 StrongPackedBucketN12A3Shard036.record4672 = true := by
  decide

def missing4673 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3819792181263073280
theorem maskCheck4673 :
    checkMaskFor missing4673 StrongPackedBucketN12A3Shard036.record4673 = true := by
  decide

def missing4674 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4071993760395821056
theorem maskCheck4674 :
    checkMaskFor missing4674 StrongPackedBucketN12A3Shard036.record4674 = true := by
  decide

def missing4675 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4108022557414785024
theorem maskCheck4675 :
    checkMaskFor missing4675 StrongPackedBucketN12A3Shard036.record4675 = true := by
  decide

def missing4676 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8107219026519785472
theorem maskCheck4676 :
    checkMaskFor missing4676 StrongPackedBucketN12A3Shard036.record4676 = true := by
  decide

def missing4677 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8143247823538749440
theorem maskCheck4677 :
    checkMaskFor missing4677 StrongPackedBucketN12A3Shard036.record4677 = true := by
  decide

def missing4678 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8647650981804244992
theorem maskCheck4678 :
    checkMaskFor missing4678 StrongPackedBucketN12A3Shard036.record4678 = true := by
  decide

def missing4679 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9476313313240416256
theorem maskCheck4679 :
    checkMaskFor missing4679 StrongPackedBucketN12A3Shard036.record4679 = true := by
  decide

def missing4680 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9620428501316272128
theorem maskCheck4680 :
    checkMaskFor missing4680 StrongPackedBucketN12A3Shard036.record4680 = true := by
  decide

def missing4681 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9692486095354200064
theorem maskCheck4681 :
    checkMaskFor missing4681 StrongPackedBucketN12A3Shard036.record4681 = true := by
  decide

def missing4682 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9728514892373164032
theorem maskCheck4682 :
    checkMaskFor missing4682 StrongPackedBucketN12A3Shard036.record4682 = true := by
  decide

def missing4683 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9908658877467983872
theorem maskCheck4683 :
    checkMaskFor missing4683 StrongPackedBucketN12A3Shard036.record4683 = true := by
  decide

def missing4684 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9980716471505911808
theorem maskCheck4684 :
    checkMaskFor missing4684 StrongPackedBucketN12A3Shard036.record4684 = true := by
  decide

def missing4685 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10016745268524875776
theorem maskCheck4685 :
    checkMaskFor missing4685 StrongPackedBucketN12A3Shard036.record4685 = true := by
  decide

def missing4686 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10124831659581767680
theorem maskCheck4686 :
    checkMaskFor missing4686 StrongPackedBucketN12A3Shard036.record4686 = true := by
  decide

def missing4687 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10160860456600731648
theorem maskCheck4687 :
    checkMaskFor missing4687 StrongPackedBucketN12A3Shard036.record4687 = true := by
  decide

def missing4688 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10232918050638659584
theorem maskCheck4688 :
    checkMaskFor missing4688 StrongPackedBucketN12A3Shard036.record4688 = true := by
  decide

def missing4689 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10485119629771407360
theorem maskCheck4689 :
    checkMaskFor missing4689 StrongPackedBucketN12A3Shard036.record4689 = true := by
  decide

def missing4690 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10557177223809335296
theorem maskCheck4690 :
    checkMaskFor missing4690 StrongPackedBucketN12A3Shard036.record4690 = true := by
  decide

def missing4691 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10593206020828299264
theorem maskCheck4691 :
    checkMaskFor missing4691 StrongPackedBucketN12A3Shard036.record4691 = true := by
  decide

def missing4692 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10701292411885191168
theorem maskCheck4692 :
    checkMaskFor missing4692 StrongPackedBucketN12A3Shard036.record4692 = true := by
  decide

def missing4693 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10737321208904155136
theorem maskCheck4693 :
    checkMaskFor missing4693 StrongPackedBucketN12A3Shard036.record4693 = true := by
  decide

def missing4694 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10809378802942083072
theorem maskCheck4694 :
    checkMaskFor missing4694 StrongPackedBucketN12A3Shard036.record4694 = true := by
  decide

def missing4695 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10989522788036902912
theorem maskCheck4695 :
    checkMaskFor missing4695 StrongPackedBucketN12A3Shard036.record4695 = true := by
  decide

def missing4696 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11025551585055866880
theorem maskCheck4696 :
    checkMaskFor missing4696 StrongPackedBucketN12A3Shard036.record4696 = true := by
  decide

def missing4697 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11097609179093794816
theorem maskCheck4697 :
    checkMaskFor missing4697 StrongPackedBucketN12A3Shard036.record4697 = true := by
  decide

def missing4698 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11241724367169650688
theorem maskCheck4698 :
    checkMaskFor missing4698 StrongPackedBucketN12A3Shard036.record4698 = true := by
  decide

def missing4699 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12718905044947173376
theorem maskCheck4699 :
    checkMaskFor missing4699 StrongPackedBucketN12A3Shard036.record4699 = true := by
  decide

def missing4700 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12754933841966137344
theorem maskCheck4700 :
    checkMaskFor missing4700 StrongPackedBucketN12A3Shard036.record4700 = true := by
  decide

def missing4701 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12826991436004065280
theorem maskCheck4701 :
    checkMaskFor missing4701 StrongPackedBucketN12A3Shard036.record4701 = true := by
  decide

def missing4702 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12971106624079921152
theorem maskCheck4702 :
    checkMaskFor missing4702 StrongPackedBucketN12A3Shard036.record4702 = true := by
  decide

def missing4703 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13259337000231632896
theorem maskCheck4703 :
    checkMaskFor missing4703 StrongPackedBucketN12A3Shard036.record4703 = true := by
  decide

def missing4704 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17294562266355597312
theorem maskCheck4704 :
    checkMaskFor missing4704 StrongPackedBucketN12A3Shard036.record4704 = true := by
  decide

def missing4705 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27778942198874112000
theorem maskCheck4705 :
    checkMaskFor missing4705 StrongPackedBucketN12A3Shard036.record4705 = true := by
  decide

def missing4706 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27850999792912039936
theorem maskCheck4706 :
    checkMaskFor missing4706 StrongPackedBucketN12A3Shard036.record4706 = true := by
  decide

def missing4707 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27887028589931003904
theorem maskCheck4707 :
    checkMaskFor missing4707 StrongPackedBucketN12A3Shard036.record4707 = true := by
  decide

def missing4708 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28031143778006859776
theorem maskCheck4708 :
    checkMaskFor missing4708 StrongPackedBucketN12A3Shard036.record4708 = true := by
  decide

def missing4709 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28283345357139607552
theorem maskCheck4709 :
    checkMaskFor missing4709 StrongPackedBucketN12A3Shard036.record4709 = true := by
  decide

def missing4710 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28319374154158571520
theorem maskCheck4710 :
    checkMaskFor missing4710 StrongPackedBucketN12A3Shard036.record4710 = true := by
  decide

def missing4711 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28859806109443031040
theorem maskCheck4711 :
    checkMaskFor missing4711 StrongPackedBucketN12A3Shard036.record4711 = true := by
  decide

def missing4712 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28895834906461995008
theorem maskCheck4712 :
    checkMaskFor missing4712 StrongPackedBucketN12A3Shard036.record4712 = true := by
  decide

def missing4713 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29400238064727490560
theorem maskCheck4713 :
    checkMaskFor missing4713 StrongPackedBucketN12A3Shard036.record4713 = true := by
  decide

def missing4714 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 31129620321637761024
theorem maskCheck4714 :
    checkMaskFor missing4714 StrongPackedBucketN12A3Shard036.record4714 = true := by
  decide

def missing4715 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37146429423804743680
theorem maskCheck4715 :
    checkMaskFor missing4715 StrongPackedBucketN12A3Shard036.record4715 = true := by
  decide

def missing4716 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37290544611880599552
theorem maskCheck4716 :
    checkMaskFor missing4716 StrongPackedBucketN12A3Shard036.record4716 = true := by
  decide

def missing4717 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37650832582070239232
theorem maskCheck4717 :
    checkMaskFor missing4717 StrongPackedBucketN12A3Shard036.record4717 = true := by
  decide

def missing4718 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37686861379089203200
theorem maskCheck4718 :
    checkMaskFor missing4718 StrongPackedBucketN12A3Shard036.record4718 = true := by
  decide

def missing4719 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37830976567165059072
theorem maskCheck4719 :
    checkMaskFor missing4719 StrongPackedBucketN12A3Shard036.record4719 = true := by
  decide

def missing4720 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38227293334373662720
theorem maskCheck4720 :
    checkMaskFor missing4720 StrongPackedBucketN12A3Shard036.record4720 = true := by
  decide

def missing4721 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38263322131392626688
theorem maskCheck4721 :
    checkMaskFor missing4721 StrongPackedBucketN12A3Shard036.record4721 = true := by
  decide

def missing4722 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38407437319468482560
theorem maskCheck4722 :
    checkMaskFor missing4722 StrongPackedBucketN12A3Shard036.record4722 = true := by
  decide

def missing4723 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46225686272583663616
theorem maskCheck4723 :
    checkMaskFor missing4723 StrongPackedBucketN12A3Shard036.record4723 = true := by
  decide

def missing4724 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46297743866621591552
theorem maskCheck4724 :
    checkMaskFor missing4724 StrongPackedBucketN12A3Shard036.record4724 = true := by
  decide

def missing4725 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46333772663640555520
theorem maskCheck4725 :
    checkMaskFor missing4725 StrongPackedBucketN12A3Shard036.record4725 = true := by
  decide

def missing4726 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46441859054697447424
theorem maskCheck4726 :
    checkMaskFor missing4726 StrongPackedBucketN12A3Shard036.record4726 = true := by
  decide

def missing4727 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46477887851716411392
theorem maskCheck4727 :
    checkMaskFor missing4727 StrongPackedBucketN12A3Shard036.record4727 = true := by
  decide

def missing4728 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46549945445754339328
theorem maskCheck4728 :
    checkMaskFor missing4728 StrongPackedBucketN12A3Shard036.record4728 = true := by
  decide

def missing4729 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 542156814955839488
theorem maskCheck4729 :
    checkMaskFor missing4729 StrongPackedBucketN12A3Shard036.record4729 = true := by
  decide

def missing4730 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 830387191107551232
theorem maskCheck4730 :
    checkMaskFor missing4730 StrongPackedBucketN12A3Shard036.record4730 = true := by
  decide

def missing4731 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1046559973221335040
theorem maskCheck4731 :
    checkMaskFor missing4731 StrongPackedBucketN12A3Shard036.record4731 = true := by
  decide

def missing4732 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1082588770240299008
theorem maskCheck4732 :
    checkMaskFor missing4732 StrongPackedBucketN12A3Shard036.record4732 = true := by
  decide

def missing4733 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1839193507638542336
theorem maskCheck4733 :
    checkMaskFor missing4733 StrongPackedBucketN12A3Shard036.record4733 = true := by
  decide

def missing4734 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1911251101676470272
theorem maskCheck4734 :
    checkMaskFor missing4734 StrongPackedBucketN12A3Shard036.record4734 = true := by
  decide

def missing4735 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1947279898695434240
theorem maskCheck4735 :
    checkMaskFor missing4735 StrongPackedBucketN12A3Shard036.record4735 = true := by
  decide

def missing4608_4609 : List (BitVec (edgeCount 12)) :=
  [missing4608]
abbrev records4608_4609 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4608]
theorem aligned4608_4609 :
    AlignedValid 12 3 missing4608_4609 records4608_4609 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4608
    maskCheck4608 AlignedValid.nil

def missing4609_4610 : List (BitVec (edgeCount 12)) :=
  [missing4609]
abbrev records4609_4610 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4609]
theorem aligned4609_4610 :
    AlignedValid 12 3 missing4609_4610 records4609_4610 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4609
    maskCheck4609 AlignedValid.nil

def missing4608_4610 : List (BitVec (edgeCount 12)) :=
  missing4608_4609 ++ missing4609_4610
abbrev records4608_4610 : List Blob :=
  records4608_4609 ++ records4609_4610
theorem aligned4608_4610 :
    AlignedValid 12 3 missing4608_4610 records4608_4610 :=
  aligned4608_4609.append aligned4609_4610

def missing4610_4611 : List (BitVec (edgeCount 12)) :=
  [missing4610]
abbrev records4610_4611 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4610]
theorem aligned4610_4611 :
    AlignedValid 12 3 missing4610_4611 records4610_4611 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4610
    maskCheck4610 AlignedValid.nil

def missing4611_4612 : List (BitVec (edgeCount 12)) :=
  [missing4611]
abbrev records4611_4612 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4611]
theorem aligned4611_4612 :
    AlignedValid 12 3 missing4611_4612 records4611_4612 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4611
    maskCheck4611 AlignedValid.nil

def missing4610_4612 : List (BitVec (edgeCount 12)) :=
  missing4610_4611 ++ missing4611_4612
abbrev records4610_4612 : List Blob :=
  records4610_4611 ++ records4611_4612
theorem aligned4610_4612 :
    AlignedValid 12 3 missing4610_4612 records4610_4612 :=
  aligned4610_4611.append aligned4611_4612

def missing4608_4612 : List (BitVec (edgeCount 12)) :=
  missing4608_4610 ++ missing4610_4612
abbrev records4608_4612 : List Blob :=
  records4608_4610 ++ records4610_4612
theorem aligned4608_4612 :
    AlignedValid 12 3 missing4608_4612 records4608_4612 :=
  aligned4608_4610.append aligned4610_4612

def missing4612_4613 : List (BitVec (edgeCount 12)) :=
  [missing4612]
abbrev records4612_4613 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4612]
theorem aligned4612_4613 :
    AlignedValid 12 3 missing4612_4613 records4612_4613 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4612
    maskCheck4612 AlignedValid.nil

def missing4613_4614 : List (BitVec (edgeCount 12)) :=
  [missing4613]
abbrev records4613_4614 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4613]
theorem aligned4613_4614 :
    AlignedValid 12 3 missing4613_4614 records4613_4614 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4613
    maskCheck4613 AlignedValid.nil

def missing4612_4614 : List (BitVec (edgeCount 12)) :=
  missing4612_4613 ++ missing4613_4614
abbrev records4612_4614 : List Blob :=
  records4612_4613 ++ records4613_4614
theorem aligned4612_4614 :
    AlignedValid 12 3 missing4612_4614 records4612_4614 :=
  aligned4612_4613.append aligned4613_4614

def missing4614_4615 : List (BitVec (edgeCount 12)) :=
  [missing4614]
abbrev records4614_4615 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4614]
theorem aligned4614_4615 :
    AlignedValid 12 3 missing4614_4615 records4614_4615 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4614
    maskCheck4614 AlignedValid.nil

def missing4615_4616 : List (BitVec (edgeCount 12)) :=
  [missing4615]
abbrev records4615_4616 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4615]
theorem aligned4615_4616 :
    AlignedValid 12 3 missing4615_4616 records4615_4616 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4615
    maskCheck4615 AlignedValid.nil

def missing4614_4616 : List (BitVec (edgeCount 12)) :=
  missing4614_4615 ++ missing4615_4616
abbrev records4614_4616 : List Blob :=
  records4614_4615 ++ records4615_4616
theorem aligned4614_4616 :
    AlignedValid 12 3 missing4614_4616 records4614_4616 :=
  aligned4614_4615.append aligned4615_4616

def missing4612_4616 : List (BitVec (edgeCount 12)) :=
  missing4612_4614 ++ missing4614_4616
abbrev records4612_4616 : List Blob :=
  records4612_4614 ++ records4614_4616
theorem aligned4612_4616 :
    AlignedValid 12 3 missing4612_4616 records4612_4616 :=
  aligned4612_4614.append aligned4614_4616

def missing4608_4616 : List (BitVec (edgeCount 12)) :=
  missing4608_4612 ++ missing4612_4616
abbrev records4608_4616 : List Blob :=
  records4608_4612 ++ records4612_4616
theorem aligned4608_4616 :
    AlignedValid 12 3 missing4608_4616 records4608_4616 :=
  aligned4608_4612.append aligned4612_4616

def missing4616_4617 : List (BitVec (edgeCount 12)) :=
  [missing4616]
abbrev records4616_4617 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4616]
theorem aligned4616_4617 :
    AlignedValid 12 3 missing4616_4617 records4616_4617 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4616
    maskCheck4616 AlignedValid.nil

def missing4617_4618 : List (BitVec (edgeCount 12)) :=
  [missing4617]
abbrev records4617_4618 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4617]
theorem aligned4617_4618 :
    AlignedValid 12 3 missing4617_4618 records4617_4618 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4617
    maskCheck4617 AlignedValid.nil

def missing4616_4618 : List (BitVec (edgeCount 12)) :=
  missing4616_4617 ++ missing4617_4618
abbrev records4616_4618 : List Blob :=
  records4616_4617 ++ records4617_4618
theorem aligned4616_4618 :
    AlignedValid 12 3 missing4616_4618 records4616_4618 :=
  aligned4616_4617.append aligned4617_4618

def missing4618_4619 : List (BitVec (edgeCount 12)) :=
  [missing4618]
abbrev records4618_4619 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4618]
theorem aligned4618_4619 :
    AlignedValid 12 3 missing4618_4619 records4618_4619 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4618
    maskCheck4618 AlignedValid.nil

def missing4619_4620 : List (BitVec (edgeCount 12)) :=
  [missing4619]
abbrev records4619_4620 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4619]
theorem aligned4619_4620 :
    AlignedValid 12 3 missing4619_4620 records4619_4620 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4619
    maskCheck4619 AlignedValid.nil

def missing4618_4620 : List (BitVec (edgeCount 12)) :=
  missing4618_4619 ++ missing4619_4620
abbrev records4618_4620 : List Blob :=
  records4618_4619 ++ records4619_4620
theorem aligned4618_4620 :
    AlignedValid 12 3 missing4618_4620 records4618_4620 :=
  aligned4618_4619.append aligned4619_4620

def missing4616_4620 : List (BitVec (edgeCount 12)) :=
  missing4616_4618 ++ missing4618_4620
abbrev records4616_4620 : List Blob :=
  records4616_4618 ++ records4618_4620
theorem aligned4616_4620 :
    AlignedValid 12 3 missing4616_4620 records4616_4620 :=
  aligned4616_4618.append aligned4618_4620

def missing4620_4621 : List (BitVec (edgeCount 12)) :=
  [missing4620]
abbrev records4620_4621 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4620]
theorem aligned4620_4621 :
    AlignedValid 12 3 missing4620_4621 records4620_4621 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4620
    maskCheck4620 AlignedValid.nil

def missing4621_4622 : List (BitVec (edgeCount 12)) :=
  [missing4621]
abbrev records4621_4622 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4621]
theorem aligned4621_4622 :
    AlignedValid 12 3 missing4621_4622 records4621_4622 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4621
    maskCheck4621 AlignedValid.nil

def missing4620_4622 : List (BitVec (edgeCount 12)) :=
  missing4620_4621 ++ missing4621_4622
abbrev records4620_4622 : List Blob :=
  records4620_4621 ++ records4621_4622
theorem aligned4620_4622 :
    AlignedValid 12 3 missing4620_4622 records4620_4622 :=
  aligned4620_4621.append aligned4621_4622

def missing4622_4623 : List (BitVec (edgeCount 12)) :=
  [missing4622]
abbrev records4622_4623 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4622]
theorem aligned4622_4623 :
    AlignedValid 12 3 missing4622_4623 records4622_4623 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4622
    maskCheck4622 AlignedValid.nil

def missing4623_4624 : List (BitVec (edgeCount 12)) :=
  [missing4623]
abbrev records4623_4624 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4623]
theorem aligned4623_4624 :
    AlignedValid 12 3 missing4623_4624 records4623_4624 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4623
    maskCheck4623 AlignedValid.nil

def missing4622_4624 : List (BitVec (edgeCount 12)) :=
  missing4622_4623 ++ missing4623_4624
abbrev records4622_4624 : List Blob :=
  records4622_4623 ++ records4623_4624
theorem aligned4622_4624 :
    AlignedValid 12 3 missing4622_4624 records4622_4624 :=
  aligned4622_4623.append aligned4623_4624

def missing4620_4624 : List (BitVec (edgeCount 12)) :=
  missing4620_4622 ++ missing4622_4624
abbrev records4620_4624 : List Blob :=
  records4620_4622 ++ records4622_4624
theorem aligned4620_4624 :
    AlignedValid 12 3 missing4620_4624 records4620_4624 :=
  aligned4620_4622.append aligned4622_4624

def missing4616_4624 : List (BitVec (edgeCount 12)) :=
  missing4616_4620 ++ missing4620_4624
abbrev records4616_4624 : List Blob :=
  records4616_4620 ++ records4620_4624
theorem aligned4616_4624 :
    AlignedValid 12 3 missing4616_4624 records4616_4624 :=
  aligned4616_4620.append aligned4620_4624

def missing4608_4624 : List (BitVec (edgeCount 12)) :=
  missing4608_4616 ++ missing4616_4624
abbrev records4608_4624 : List Blob :=
  records4608_4616 ++ records4616_4624
theorem aligned4608_4624 :
    AlignedValid 12 3 missing4608_4624 records4608_4624 :=
  aligned4608_4616.append aligned4616_4624

def missing4624_4625 : List (BitVec (edgeCount 12)) :=
  [missing4624]
abbrev records4624_4625 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4624]
theorem aligned4624_4625 :
    AlignedValid 12 3 missing4624_4625 records4624_4625 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4624
    maskCheck4624 AlignedValid.nil

def missing4625_4626 : List (BitVec (edgeCount 12)) :=
  [missing4625]
abbrev records4625_4626 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4625]
theorem aligned4625_4626 :
    AlignedValid 12 3 missing4625_4626 records4625_4626 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4625
    maskCheck4625 AlignedValid.nil

def missing4624_4626 : List (BitVec (edgeCount 12)) :=
  missing4624_4625 ++ missing4625_4626
abbrev records4624_4626 : List Blob :=
  records4624_4625 ++ records4625_4626
theorem aligned4624_4626 :
    AlignedValid 12 3 missing4624_4626 records4624_4626 :=
  aligned4624_4625.append aligned4625_4626

def missing4626_4627 : List (BitVec (edgeCount 12)) :=
  [missing4626]
abbrev records4626_4627 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4626]
theorem aligned4626_4627 :
    AlignedValid 12 3 missing4626_4627 records4626_4627 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4626
    maskCheck4626 AlignedValid.nil

def missing4627_4628 : List (BitVec (edgeCount 12)) :=
  [missing4627]
abbrev records4627_4628 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4627]
theorem aligned4627_4628 :
    AlignedValid 12 3 missing4627_4628 records4627_4628 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4627
    maskCheck4627 AlignedValid.nil

def missing4626_4628 : List (BitVec (edgeCount 12)) :=
  missing4626_4627 ++ missing4627_4628
abbrev records4626_4628 : List Blob :=
  records4626_4627 ++ records4627_4628
theorem aligned4626_4628 :
    AlignedValid 12 3 missing4626_4628 records4626_4628 :=
  aligned4626_4627.append aligned4627_4628

def missing4624_4628 : List (BitVec (edgeCount 12)) :=
  missing4624_4626 ++ missing4626_4628
abbrev records4624_4628 : List Blob :=
  records4624_4626 ++ records4626_4628
theorem aligned4624_4628 :
    AlignedValid 12 3 missing4624_4628 records4624_4628 :=
  aligned4624_4626.append aligned4626_4628

def missing4628_4629 : List (BitVec (edgeCount 12)) :=
  [missing4628]
abbrev records4628_4629 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4628]
theorem aligned4628_4629 :
    AlignedValid 12 3 missing4628_4629 records4628_4629 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4628
    maskCheck4628 AlignedValid.nil

def missing4629_4630 : List (BitVec (edgeCount 12)) :=
  [missing4629]
abbrev records4629_4630 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4629]
theorem aligned4629_4630 :
    AlignedValid 12 3 missing4629_4630 records4629_4630 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4629
    maskCheck4629 AlignedValid.nil

def missing4628_4630 : List (BitVec (edgeCount 12)) :=
  missing4628_4629 ++ missing4629_4630
abbrev records4628_4630 : List Blob :=
  records4628_4629 ++ records4629_4630
theorem aligned4628_4630 :
    AlignedValid 12 3 missing4628_4630 records4628_4630 :=
  aligned4628_4629.append aligned4629_4630

def missing4630_4631 : List (BitVec (edgeCount 12)) :=
  [missing4630]
abbrev records4630_4631 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4630]
theorem aligned4630_4631 :
    AlignedValid 12 3 missing4630_4631 records4630_4631 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4630
    maskCheck4630 AlignedValid.nil

def missing4631_4632 : List (BitVec (edgeCount 12)) :=
  [missing4631]
abbrev records4631_4632 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4631]
theorem aligned4631_4632 :
    AlignedValid 12 3 missing4631_4632 records4631_4632 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4631
    maskCheck4631 AlignedValid.nil

def missing4630_4632 : List (BitVec (edgeCount 12)) :=
  missing4630_4631 ++ missing4631_4632
abbrev records4630_4632 : List Blob :=
  records4630_4631 ++ records4631_4632
theorem aligned4630_4632 :
    AlignedValid 12 3 missing4630_4632 records4630_4632 :=
  aligned4630_4631.append aligned4631_4632

def missing4628_4632 : List (BitVec (edgeCount 12)) :=
  missing4628_4630 ++ missing4630_4632
abbrev records4628_4632 : List Blob :=
  records4628_4630 ++ records4630_4632
theorem aligned4628_4632 :
    AlignedValid 12 3 missing4628_4632 records4628_4632 :=
  aligned4628_4630.append aligned4630_4632

def missing4624_4632 : List (BitVec (edgeCount 12)) :=
  missing4624_4628 ++ missing4628_4632
abbrev records4624_4632 : List Blob :=
  records4624_4628 ++ records4628_4632
theorem aligned4624_4632 :
    AlignedValid 12 3 missing4624_4632 records4624_4632 :=
  aligned4624_4628.append aligned4628_4632

def missing4632_4633 : List (BitVec (edgeCount 12)) :=
  [missing4632]
abbrev records4632_4633 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4632]
theorem aligned4632_4633 :
    AlignedValid 12 3 missing4632_4633 records4632_4633 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4632
    maskCheck4632 AlignedValid.nil

def missing4633_4634 : List (BitVec (edgeCount 12)) :=
  [missing4633]
abbrev records4633_4634 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4633]
theorem aligned4633_4634 :
    AlignedValid 12 3 missing4633_4634 records4633_4634 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4633
    maskCheck4633 AlignedValid.nil

def missing4632_4634 : List (BitVec (edgeCount 12)) :=
  missing4632_4633 ++ missing4633_4634
abbrev records4632_4634 : List Blob :=
  records4632_4633 ++ records4633_4634
theorem aligned4632_4634 :
    AlignedValid 12 3 missing4632_4634 records4632_4634 :=
  aligned4632_4633.append aligned4633_4634

def missing4634_4635 : List (BitVec (edgeCount 12)) :=
  [missing4634]
abbrev records4634_4635 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4634]
theorem aligned4634_4635 :
    AlignedValid 12 3 missing4634_4635 records4634_4635 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4634
    maskCheck4634 AlignedValid.nil

def missing4635_4636 : List (BitVec (edgeCount 12)) :=
  [missing4635]
abbrev records4635_4636 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4635]
theorem aligned4635_4636 :
    AlignedValid 12 3 missing4635_4636 records4635_4636 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4635
    maskCheck4635 AlignedValid.nil

def missing4634_4636 : List (BitVec (edgeCount 12)) :=
  missing4634_4635 ++ missing4635_4636
abbrev records4634_4636 : List Blob :=
  records4634_4635 ++ records4635_4636
theorem aligned4634_4636 :
    AlignedValid 12 3 missing4634_4636 records4634_4636 :=
  aligned4634_4635.append aligned4635_4636

def missing4632_4636 : List (BitVec (edgeCount 12)) :=
  missing4632_4634 ++ missing4634_4636
abbrev records4632_4636 : List Blob :=
  records4632_4634 ++ records4634_4636
theorem aligned4632_4636 :
    AlignedValid 12 3 missing4632_4636 records4632_4636 :=
  aligned4632_4634.append aligned4634_4636

def missing4636_4637 : List (BitVec (edgeCount 12)) :=
  [missing4636]
abbrev records4636_4637 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4636]
theorem aligned4636_4637 :
    AlignedValid 12 3 missing4636_4637 records4636_4637 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4636
    maskCheck4636 AlignedValid.nil

def missing4637_4638 : List (BitVec (edgeCount 12)) :=
  [missing4637]
abbrev records4637_4638 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4637]
theorem aligned4637_4638 :
    AlignedValid 12 3 missing4637_4638 records4637_4638 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4637
    maskCheck4637 AlignedValid.nil

def missing4636_4638 : List (BitVec (edgeCount 12)) :=
  missing4636_4637 ++ missing4637_4638
abbrev records4636_4638 : List Blob :=
  records4636_4637 ++ records4637_4638
theorem aligned4636_4638 :
    AlignedValid 12 3 missing4636_4638 records4636_4638 :=
  aligned4636_4637.append aligned4637_4638

def missing4638_4639 : List (BitVec (edgeCount 12)) :=
  [missing4638]
abbrev records4638_4639 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4638]
theorem aligned4638_4639 :
    AlignedValid 12 3 missing4638_4639 records4638_4639 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4638
    maskCheck4638 AlignedValid.nil

def missing4639_4640 : List (BitVec (edgeCount 12)) :=
  [missing4639]
abbrev records4639_4640 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4639]
theorem aligned4639_4640 :
    AlignedValid 12 3 missing4639_4640 records4639_4640 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4639
    maskCheck4639 AlignedValid.nil

def missing4638_4640 : List (BitVec (edgeCount 12)) :=
  missing4638_4639 ++ missing4639_4640
abbrev records4638_4640 : List Blob :=
  records4638_4639 ++ records4639_4640
theorem aligned4638_4640 :
    AlignedValid 12 3 missing4638_4640 records4638_4640 :=
  aligned4638_4639.append aligned4639_4640

def missing4636_4640 : List (BitVec (edgeCount 12)) :=
  missing4636_4638 ++ missing4638_4640
abbrev records4636_4640 : List Blob :=
  records4636_4638 ++ records4638_4640
theorem aligned4636_4640 :
    AlignedValid 12 3 missing4636_4640 records4636_4640 :=
  aligned4636_4638.append aligned4638_4640

def missing4632_4640 : List (BitVec (edgeCount 12)) :=
  missing4632_4636 ++ missing4636_4640
abbrev records4632_4640 : List Blob :=
  records4632_4636 ++ records4636_4640
theorem aligned4632_4640 :
    AlignedValid 12 3 missing4632_4640 records4632_4640 :=
  aligned4632_4636.append aligned4636_4640

def missing4624_4640 : List (BitVec (edgeCount 12)) :=
  missing4624_4632 ++ missing4632_4640
abbrev records4624_4640 : List Blob :=
  records4624_4632 ++ records4632_4640
theorem aligned4624_4640 :
    AlignedValid 12 3 missing4624_4640 records4624_4640 :=
  aligned4624_4632.append aligned4632_4640

def missing4608_4640 : List (BitVec (edgeCount 12)) :=
  missing4608_4624 ++ missing4624_4640
abbrev records4608_4640 : List Blob :=
  records4608_4624 ++ records4624_4640
theorem aligned4608_4640 :
    AlignedValid 12 3 missing4608_4640 records4608_4640 :=
  aligned4608_4624.append aligned4624_4640

def missing4640_4641 : List (BitVec (edgeCount 12)) :=
  [missing4640]
abbrev records4640_4641 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4640]
theorem aligned4640_4641 :
    AlignedValid 12 3 missing4640_4641 records4640_4641 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4640
    maskCheck4640 AlignedValid.nil

def missing4641_4642 : List (BitVec (edgeCount 12)) :=
  [missing4641]
abbrev records4641_4642 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4641]
theorem aligned4641_4642 :
    AlignedValid 12 3 missing4641_4642 records4641_4642 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4641
    maskCheck4641 AlignedValid.nil

def missing4640_4642 : List (BitVec (edgeCount 12)) :=
  missing4640_4641 ++ missing4641_4642
abbrev records4640_4642 : List Blob :=
  records4640_4641 ++ records4641_4642
theorem aligned4640_4642 :
    AlignedValid 12 3 missing4640_4642 records4640_4642 :=
  aligned4640_4641.append aligned4641_4642

def missing4642_4643 : List (BitVec (edgeCount 12)) :=
  [missing4642]
abbrev records4642_4643 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4642]
theorem aligned4642_4643 :
    AlignedValid 12 3 missing4642_4643 records4642_4643 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4642
    maskCheck4642 AlignedValid.nil

def missing4643_4644 : List (BitVec (edgeCount 12)) :=
  [missing4643]
abbrev records4643_4644 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4643]
theorem aligned4643_4644 :
    AlignedValid 12 3 missing4643_4644 records4643_4644 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4643
    maskCheck4643 AlignedValid.nil

def missing4642_4644 : List (BitVec (edgeCount 12)) :=
  missing4642_4643 ++ missing4643_4644
abbrev records4642_4644 : List Blob :=
  records4642_4643 ++ records4643_4644
theorem aligned4642_4644 :
    AlignedValid 12 3 missing4642_4644 records4642_4644 :=
  aligned4642_4643.append aligned4643_4644

def missing4640_4644 : List (BitVec (edgeCount 12)) :=
  missing4640_4642 ++ missing4642_4644
abbrev records4640_4644 : List Blob :=
  records4640_4642 ++ records4642_4644
theorem aligned4640_4644 :
    AlignedValid 12 3 missing4640_4644 records4640_4644 :=
  aligned4640_4642.append aligned4642_4644

def missing4644_4645 : List (BitVec (edgeCount 12)) :=
  [missing4644]
abbrev records4644_4645 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4644]
theorem aligned4644_4645 :
    AlignedValid 12 3 missing4644_4645 records4644_4645 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4644
    maskCheck4644 AlignedValid.nil

def missing4645_4646 : List (BitVec (edgeCount 12)) :=
  [missing4645]
abbrev records4645_4646 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4645]
theorem aligned4645_4646 :
    AlignedValid 12 3 missing4645_4646 records4645_4646 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4645
    maskCheck4645 AlignedValid.nil

def missing4644_4646 : List (BitVec (edgeCount 12)) :=
  missing4644_4645 ++ missing4645_4646
abbrev records4644_4646 : List Blob :=
  records4644_4645 ++ records4645_4646
theorem aligned4644_4646 :
    AlignedValid 12 3 missing4644_4646 records4644_4646 :=
  aligned4644_4645.append aligned4645_4646

def missing4646_4647 : List (BitVec (edgeCount 12)) :=
  [missing4646]
abbrev records4646_4647 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4646]
theorem aligned4646_4647 :
    AlignedValid 12 3 missing4646_4647 records4646_4647 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4646
    maskCheck4646 AlignedValid.nil

def missing4647_4648 : List (BitVec (edgeCount 12)) :=
  [missing4647]
abbrev records4647_4648 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4647]
theorem aligned4647_4648 :
    AlignedValid 12 3 missing4647_4648 records4647_4648 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4647
    maskCheck4647 AlignedValid.nil

def missing4646_4648 : List (BitVec (edgeCount 12)) :=
  missing4646_4647 ++ missing4647_4648
abbrev records4646_4648 : List Blob :=
  records4646_4647 ++ records4647_4648
theorem aligned4646_4648 :
    AlignedValid 12 3 missing4646_4648 records4646_4648 :=
  aligned4646_4647.append aligned4647_4648

def missing4644_4648 : List (BitVec (edgeCount 12)) :=
  missing4644_4646 ++ missing4646_4648
abbrev records4644_4648 : List Blob :=
  records4644_4646 ++ records4646_4648
theorem aligned4644_4648 :
    AlignedValid 12 3 missing4644_4648 records4644_4648 :=
  aligned4644_4646.append aligned4646_4648

def missing4640_4648 : List (BitVec (edgeCount 12)) :=
  missing4640_4644 ++ missing4644_4648
abbrev records4640_4648 : List Blob :=
  records4640_4644 ++ records4644_4648
theorem aligned4640_4648 :
    AlignedValid 12 3 missing4640_4648 records4640_4648 :=
  aligned4640_4644.append aligned4644_4648

def missing4648_4649 : List (BitVec (edgeCount 12)) :=
  [missing4648]
abbrev records4648_4649 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4648]
theorem aligned4648_4649 :
    AlignedValid 12 3 missing4648_4649 records4648_4649 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4648
    maskCheck4648 AlignedValid.nil

def missing4649_4650 : List (BitVec (edgeCount 12)) :=
  [missing4649]
abbrev records4649_4650 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4649]
theorem aligned4649_4650 :
    AlignedValid 12 3 missing4649_4650 records4649_4650 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4649
    maskCheck4649 AlignedValid.nil

def missing4648_4650 : List (BitVec (edgeCount 12)) :=
  missing4648_4649 ++ missing4649_4650
abbrev records4648_4650 : List Blob :=
  records4648_4649 ++ records4649_4650
theorem aligned4648_4650 :
    AlignedValid 12 3 missing4648_4650 records4648_4650 :=
  aligned4648_4649.append aligned4649_4650

def missing4650_4651 : List (BitVec (edgeCount 12)) :=
  [missing4650]
abbrev records4650_4651 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4650]
theorem aligned4650_4651 :
    AlignedValid 12 3 missing4650_4651 records4650_4651 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4650
    maskCheck4650 AlignedValid.nil

def missing4651_4652 : List (BitVec (edgeCount 12)) :=
  [missing4651]
abbrev records4651_4652 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4651]
theorem aligned4651_4652 :
    AlignedValid 12 3 missing4651_4652 records4651_4652 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4651
    maskCheck4651 AlignedValid.nil

def missing4650_4652 : List (BitVec (edgeCount 12)) :=
  missing4650_4651 ++ missing4651_4652
abbrev records4650_4652 : List Blob :=
  records4650_4651 ++ records4651_4652
theorem aligned4650_4652 :
    AlignedValid 12 3 missing4650_4652 records4650_4652 :=
  aligned4650_4651.append aligned4651_4652

def missing4648_4652 : List (BitVec (edgeCount 12)) :=
  missing4648_4650 ++ missing4650_4652
abbrev records4648_4652 : List Blob :=
  records4648_4650 ++ records4650_4652
theorem aligned4648_4652 :
    AlignedValid 12 3 missing4648_4652 records4648_4652 :=
  aligned4648_4650.append aligned4650_4652

def missing4652_4653 : List (BitVec (edgeCount 12)) :=
  [missing4652]
abbrev records4652_4653 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4652]
theorem aligned4652_4653 :
    AlignedValid 12 3 missing4652_4653 records4652_4653 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4652
    maskCheck4652 AlignedValid.nil

def missing4653_4654 : List (BitVec (edgeCount 12)) :=
  [missing4653]
abbrev records4653_4654 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4653]
theorem aligned4653_4654 :
    AlignedValid 12 3 missing4653_4654 records4653_4654 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4653
    maskCheck4653 AlignedValid.nil

def missing4652_4654 : List (BitVec (edgeCount 12)) :=
  missing4652_4653 ++ missing4653_4654
abbrev records4652_4654 : List Blob :=
  records4652_4653 ++ records4653_4654
theorem aligned4652_4654 :
    AlignedValid 12 3 missing4652_4654 records4652_4654 :=
  aligned4652_4653.append aligned4653_4654

def missing4654_4655 : List (BitVec (edgeCount 12)) :=
  [missing4654]
abbrev records4654_4655 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4654]
theorem aligned4654_4655 :
    AlignedValid 12 3 missing4654_4655 records4654_4655 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4654
    maskCheck4654 AlignedValid.nil

def missing4655_4656 : List (BitVec (edgeCount 12)) :=
  [missing4655]
abbrev records4655_4656 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4655]
theorem aligned4655_4656 :
    AlignedValid 12 3 missing4655_4656 records4655_4656 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4655
    maskCheck4655 AlignedValid.nil

def missing4654_4656 : List (BitVec (edgeCount 12)) :=
  missing4654_4655 ++ missing4655_4656
abbrev records4654_4656 : List Blob :=
  records4654_4655 ++ records4655_4656
theorem aligned4654_4656 :
    AlignedValid 12 3 missing4654_4656 records4654_4656 :=
  aligned4654_4655.append aligned4655_4656

def missing4652_4656 : List (BitVec (edgeCount 12)) :=
  missing4652_4654 ++ missing4654_4656
abbrev records4652_4656 : List Blob :=
  records4652_4654 ++ records4654_4656
theorem aligned4652_4656 :
    AlignedValid 12 3 missing4652_4656 records4652_4656 :=
  aligned4652_4654.append aligned4654_4656

def missing4648_4656 : List (BitVec (edgeCount 12)) :=
  missing4648_4652 ++ missing4652_4656
abbrev records4648_4656 : List Blob :=
  records4648_4652 ++ records4652_4656
theorem aligned4648_4656 :
    AlignedValid 12 3 missing4648_4656 records4648_4656 :=
  aligned4648_4652.append aligned4652_4656

def missing4640_4656 : List (BitVec (edgeCount 12)) :=
  missing4640_4648 ++ missing4648_4656
abbrev records4640_4656 : List Blob :=
  records4640_4648 ++ records4648_4656
theorem aligned4640_4656 :
    AlignedValid 12 3 missing4640_4656 records4640_4656 :=
  aligned4640_4648.append aligned4648_4656

def missing4656_4657 : List (BitVec (edgeCount 12)) :=
  [missing4656]
abbrev records4656_4657 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4656]
theorem aligned4656_4657 :
    AlignedValid 12 3 missing4656_4657 records4656_4657 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4656
    maskCheck4656 AlignedValid.nil

def missing4657_4658 : List (BitVec (edgeCount 12)) :=
  [missing4657]
abbrev records4657_4658 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4657]
theorem aligned4657_4658 :
    AlignedValid 12 3 missing4657_4658 records4657_4658 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4657
    maskCheck4657 AlignedValid.nil

def missing4656_4658 : List (BitVec (edgeCount 12)) :=
  missing4656_4657 ++ missing4657_4658
abbrev records4656_4658 : List Blob :=
  records4656_4657 ++ records4657_4658
theorem aligned4656_4658 :
    AlignedValid 12 3 missing4656_4658 records4656_4658 :=
  aligned4656_4657.append aligned4657_4658

def missing4658_4659 : List (BitVec (edgeCount 12)) :=
  [missing4658]
abbrev records4658_4659 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4658]
theorem aligned4658_4659 :
    AlignedValid 12 3 missing4658_4659 records4658_4659 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4658
    maskCheck4658 AlignedValid.nil

def missing4659_4660 : List (BitVec (edgeCount 12)) :=
  [missing4659]
abbrev records4659_4660 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4659]
theorem aligned4659_4660 :
    AlignedValid 12 3 missing4659_4660 records4659_4660 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4659
    maskCheck4659 AlignedValid.nil

def missing4658_4660 : List (BitVec (edgeCount 12)) :=
  missing4658_4659 ++ missing4659_4660
abbrev records4658_4660 : List Blob :=
  records4658_4659 ++ records4659_4660
theorem aligned4658_4660 :
    AlignedValid 12 3 missing4658_4660 records4658_4660 :=
  aligned4658_4659.append aligned4659_4660

def missing4656_4660 : List (BitVec (edgeCount 12)) :=
  missing4656_4658 ++ missing4658_4660
abbrev records4656_4660 : List Blob :=
  records4656_4658 ++ records4658_4660
theorem aligned4656_4660 :
    AlignedValid 12 3 missing4656_4660 records4656_4660 :=
  aligned4656_4658.append aligned4658_4660

def missing4660_4661 : List (BitVec (edgeCount 12)) :=
  [missing4660]
abbrev records4660_4661 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4660]
theorem aligned4660_4661 :
    AlignedValid 12 3 missing4660_4661 records4660_4661 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4660
    maskCheck4660 AlignedValid.nil

def missing4661_4662 : List (BitVec (edgeCount 12)) :=
  [missing4661]
abbrev records4661_4662 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4661]
theorem aligned4661_4662 :
    AlignedValid 12 3 missing4661_4662 records4661_4662 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4661
    maskCheck4661 AlignedValid.nil

def missing4660_4662 : List (BitVec (edgeCount 12)) :=
  missing4660_4661 ++ missing4661_4662
abbrev records4660_4662 : List Blob :=
  records4660_4661 ++ records4661_4662
theorem aligned4660_4662 :
    AlignedValid 12 3 missing4660_4662 records4660_4662 :=
  aligned4660_4661.append aligned4661_4662

def missing4662_4663 : List (BitVec (edgeCount 12)) :=
  [missing4662]
abbrev records4662_4663 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4662]
theorem aligned4662_4663 :
    AlignedValid 12 3 missing4662_4663 records4662_4663 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4662
    maskCheck4662 AlignedValid.nil

def missing4663_4664 : List (BitVec (edgeCount 12)) :=
  [missing4663]
abbrev records4663_4664 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4663]
theorem aligned4663_4664 :
    AlignedValid 12 3 missing4663_4664 records4663_4664 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4663
    maskCheck4663 AlignedValid.nil

def missing4662_4664 : List (BitVec (edgeCount 12)) :=
  missing4662_4663 ++ missing4663_4664
abbrev records4662_4664 : List Blob :=
  records4662_4663 ++ records4663_4664
theorem aligned4662_4664 :
    AlignedValid 12 3 missing4662_4664 records4662_4664 :=
  aligned4662_4663.append aligned4663_4664

def missing4660_4664 : List (BitVec (edgeCount 12)) :=
  missing4660_4662 ++ missing4662_4664
abbrev records4660_4664 : List Blob :=
  records4660_4662 ++ records4662_4664
theorem aligned4660_4664 :
    AlignedValid 12 3 missing4660_4664 records4660_4664 :=
  aligned4660_4662.append aligned4662_4664

def missing4656_4664 : List (BitVec (edgeCount 12)) :=
  missing4656_4660 ++ missing4660_4664
abbrev records4656_4664 : List Blob :=
  records4656_4660 ++ records4660_4664
theorem aligned4656_4664 :
    AlignedValid 12 3 missing4656_4664 records4656_4664 :=
  aligned4656_4660.append aligned4660_4664

def missing4664_4665 : List (BitVec (edgeCount 12)) :=
  [missing4664]
abbrev records4664_4665 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4664]
theorem aligned4664_4665 :
    AlignedValid 12 3 missing4664_4665 records4664_4665 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4664
    maskCheck4664 AlignedValid.nil

def missing4665_4666 : List (BitVec (edgeCount 12)) :=
  [missing4665]
abbrev records4665_4666 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4665]
theorem aligned4665_4666 :
    AlignedValid 12 3 missing4665_4666 records4665_4666 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4665
    maskCheck4665 AlignedValid.nil

def missing4664_4666 : List (BitVec (edgeCount 12)) :=
  missing4664_4665 ++ missing4665_4666
abbrev records4664_4666 : List Blob :=
  records4664_4665 ++ records4665_4666
theorem aligned4664_4666 :
    AlignedValid 12 3 missing4664_4666 records4664_4666 :=
  aligned4664_4665.append aligned4665_4666

def missing4666_4667 : List (BitVec (edgeCount 12)) :=
  [missing4666]
abbrev records4666_4667 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4666]
theorem aligned4666_4667 :
    AlignedValid 12 3 missing4666_4667 records4666_4667 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4666
    maskCheck4666 AlignedValid.nil

def missing4667_4668 : List (BitVec (edgeCount 12)) :=
  [missing4667]
abbrev records4667_4668 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4667]
theorem aligned4667_4668 :
    AlignedValid 12 3 missing4667_4668 records4667_4668 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4667
    maskCheck4667 AlignedValid.nil

def missing4666_4668 : List (BitVec (edgeCount 12)) :=
  missing4666_4667 ++ missing4667_4668
abbrev records4666_4668 : List Blob :=
  records4666_4667 ++ records4667_4668
theorem aligned4666_4668 :
    AlignedValid 12 3 missing4666_4668 records4666_4668 :=
  aligned4666_4667.append aligned4667_4668

def missing4664_4668 : List (BitVec (edgeCount 12)) :=
  missing4664_4666 ++ missing4666_4668
abbrev records4664_4668 : List Blob :=
  records4664_4666 ++ records4666_4668
theorem aligned4664_4668 :
    AlignedValid 12 3 missing4664_4668 records4664_4668 :=
  aligned4664_4666.append aligned4666_4668

def missing4668_4669 : List (BitVec (edgeCount 12)) :=
  [missing4668]
abbrev records4668_4669 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4668]
theorem aligned4668_4669 :
    AlignedValid 12 3 missing4668_4669 records4668_4669 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4668
    maskCheck4668 AlignedValid.nil

def missing4669_4670 : List (BitVec (edgeCount 12)) :=
  [missing4669]
abbrev records4669_4670 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4669]
theorem aligned4669_4670 :
    AlignedValid 12 3 missing4669_4670 records4669_4670 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4669
    maskCheck4669 AlignedValid.nil

def missing4668_4670 : List (BitVec (edgeCount 12)) :=
  missing4668_4669 ++ missing4669_4670
abbrev records4668_4670 : List Blob :=
  records4668_4669 ++ records4669_4670
theorem aligned4668_4670 :
    AlignedValid 12 3 missing4668_4670 records4668_4670 :=
  aligned4668_4669.append aligned4669_4670

def missing4670_4671 : List (BitVec (edgeCount 12)) :=
  [missing4670]
abbrev records4670_4671 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4670]
theorem aligned4670_4671 :
    AlignedValid 12 3 missing4670_4671 records4670_4671 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4670
    maskCheck4670 AlignedValid.nil

def missing4671_4672 : List (BitVec (edgeCount 12)) :=
  [missing4671]
abbrev records4671_4672 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4671]
theorem aligned4671_4672 :
    AlignedValid 12 3 missing4671_4672 records4671_4672 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4671
    maskCheck4671 AlignedValid.nil

def missing4670_4672 : List (BitVec (edgeCount 12)) :=
  missing4670_4671 ++ missing4671_4672
abbrev records4670_4672 : List Blob :=
  records4670_4671 ++ records4671_4672
theorem aligned4670_4672 :
    AlignedValid 12 3 missing4670_4672 records4670_4672 :=
  aligned4670_4671.append aligned4671_4672

def missing4668_4672 : List (BitVec (edgeCount 12)) :=
  missing4668_4670 ++ missing4670_4672
abbrev records4668_4672 : List Blob :=
  records4668_4670 ++ records4670_4672
theorem aligned4668_4672 :
    AlignedValid 12 3 missing4668_4672 records4668_4672 :=
  aligned4668_4670.append aligned4670_4672

def missing4664_4672 : List (BitVec (edgeCount 12)) :=
  missing4664_4668 ++ missing4668_4672
abbrev records4664_4672 : List Blob :=
  records4664_4668 ++ records4668_4672
theorem aligned4664_4672 :
    AlignedValid 12 3 missing4664_4672 records4664_4672 :=
  aligned4664_4668.append aligned4668_4672

def missing4656_4672 : List (BitVec (edgeCount 12)) :=
  missing4656_4664 ++ missing4664_4672
abbrev records4656_4672 : List Blob :=
  records4656_4664 ++ records4664_4672
theorem aligned4656_4672 :
    AlignedValid 12 3 missing4656_4672 records4656_4672 :=
  aligned4656_4664.append aligned4664_4672

def missing4640_4672 : List (BitVec (edgeCount 12)) :=
  missing4640_4656 ++ missing4656_4672
abbrev records4640_4672 : List Blob :=
  records4640_4656 ++ records4656_4672
theorem aligned4640_4672 :
    AlignedValid 12 3 missing4640_4672 records4640_4672 :=
  aligned4640_4656.append aligned4656_4672

def missing4608_4672 : List (BitVec (edgeCount 12)) :=
  missing4608_4640 ++ missing4640_4672
abbrev records4608_4672 : List Blob :=
  records4608_4640 ++ records4640_4672
theorem aligned4608_4672 :
    AlignedValid 12 3 missing4608_4672 records4608_4672 :=
  aligned4608_4640.append aligned4640_4672

def missing4672_4673 : List (BitVec (edgeCount 12)) :=
  [missing4672]
abbrev records4672_4673 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4672]
theorem aligned4672_4673 :
    AlignedValid 12 3 missing4672_4673 records4672_4673 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4672
    maskCheck4672 AlignedValid.nil

def missing4673_4674 : List (BitVec (edgeCount 12)) :=
  [missing4673]
abbrev records4673_4674 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4673]
theorem aligned4673_4674 :
    AlignedValid 12 3 missing4673_4674 records4673_4674 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4673
    maskCheck4673 AlignedValid.nil

def missing4672_4674 : List (BitVec (edgeCount 12)) :=
  missing4672_4673 ++ missing4673_4674
abbrev records4672_4674 : List Blob :=
  records4672_4673 ++ records4673_4674
theorem aligned4672_4674 :
    AlignedValid 12 3 missing4672_4674 records4672_4674 :=
  aligned4672_4673.append aligned4673_4674

def missing4674_4675 : List (BitVec (edgeCount 12)) :=
  [missing4674]
abbrev records4674_4675 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4674]
theorem aligned4674_4675 :
    AlignedValid 12 3 missing4674_4675 records4674_4675 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4674
    maskCheck4674 AlignedValid.nil

def missing4675_4676 : List (BitVec (edgeCount 12)) :=
  [missing4675]
abbrev records4675_4676 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4675]
theorem aligned4675_4676 :
    AlignedValid 12 3 missing4675_4676 records4675_4676 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4675
    maskCheck4675 AlignedValid.nil

def missing4674_4676 : List (BitVec (edgeCount 12)) :=
  missing4674_4675 ++ missing4675_4676
abbrev records4674_4676 : List Blob :=
  records4674_4675 ++ records4675_4676
theorem aligned4674_4676 :
    AlignedValid 12 3 missing4674_4676 records4674_4676 :=
  aligned4674_4675.append aligned4675_4676

def missing4672_4676 : List (BitVec (edgeCount 12)) :=
  missing4672_4674 ++ missing4674_4676
abbrev records4672_4676 : List Blob :=
  records4672_4674 ++ records4674_4676
theorem aligned4672_4676 :
    AlignedValid 12 3 missing4672_4676 records4672_4676 :=
  aligned4672_4674.append aligned4674_4676

def missing4676_4677 : List (BitVec (edgeCount 12)) :=
  [missing4676]
abbrev records4676_4677 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4676]
theorem aligned4676_4677 :
    AlignedValid 12 3 missing4676_4677 records4676_4677 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4676
    maskCheck4676 AlignedValid.nil

def missing4677_4678 : List (BitVec (edgeCount 12)) :=
  [missing4677]
abbrev records4677_4678 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4677]
theorem aligned4677_4678 :
    AlignedValid 12 3 missing4677_4678 records4677_4678 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4677
    maskCheck4677 AlignedValid.nil

def missing4676_4678 : List (BitVec (edgeCount 12)) :=
  missing4676_4677 ++ missing4677_4678
abbrev records4676_4678 : List Blob :=
  records4676_4677 ++ records4677_4678
theorem aligned4676_4678 :
    AlignedValid 12 3 missing4676_4678 records4676_4678 :=
  aligned4676_4677.append aligned4677_4678

def missing4678_4679 : List (BitVec (edgeCount 12)) :=
  [missing4678]
abbrev records4678_4679 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4678]
theorem aligned4678_4679 :
    AlignedValid 12 3 missing4678_4679 records4678_4679 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4678
    maskCheck4678 AlignedValid.nil

def missing4679_4680 : List (BitVec (edgeCount 12)) :=
  [missing4679]
abbrev records4679_4680 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4679]
theorem aligned4679_4680 :
    AlignedValid 12 3 missing4679_4680 records4679_4680 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4679
    maskCheck4679 AlignedValid.nil

def missing4678_4680 : List (BitVec (edgeCount 12)) :=
  missing4678_4679 ++ missing4679_4680
abbrev records4678_4680 : List Blob :=
  records4678_4679 ++ records4679_4680
theorem aligned4678_4680 :
    AlignedValid 12 3 missing4678_4680 records4678_4680 :=
  aligned4678_4679.append aligned4679_4680

def missing4676_4680 : List (BitVec (edgeCount 12)) :=
  missing4676_4678 ++ missing4678_4680
abbrev records4676_4680 : List Blob :=
  records4676_4678 ++ records4678_4680
theorem aligned4676_4680 :
    AlignedValid 12 3 missing4676_4680 records4676_4680 :=
  aligned4676_4678.append aligned4678_4680

def missing4672_4680 : List (BitVec (edgeCount 12)) :=
  missing4672_4676 ++ missing4676_4680
abbrev records4672_4680 : List Blob :=
  records4672_4676 ++ records4676_4680
theorem aligned4672_4680 :
    AlignedValid 12 3 missing4672_4680 records4672_4680 :=
  aligned4672_4676.append aligned4676_4680

def missing4680_4681 : List (BitVec (edgeCount 12)) :=
  [missing4680]
abbrev records4680_4681 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4680]
theorem aligned4680_4681 :
    AlignedValid 12 3 missing4680_4681 records4680_4681 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4680
    maskCheck4680 AlignedValid.nil

def missing4681_4682 : List (BitVec (edgeCount 12)) :=
  [missing4681]
abbrev records4681_4682 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4681]
theorem aligned4681_4682 :
    AlignedValid 12 3 missing4681_4682 records4681_4682 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4681
    maskCheck4681 AlignedValid.nil

def missing4680_4682 : List (BitVec (edgeCount 12)) :=
  missing4680_4681 ++ missing4681_4682
abbrev records4680_4682 : List Blob :=
  records4680_4681 ++ records4681_4682
theorem aligned4680_4682 :
    AlignedValid 12 3 missing4680_4682 records4680_4682 :=
  aligned4680_4681.append aligned4681_4682

def missing4682_4683 : List (BitVec (edgeCount 12)) :=
  [missing4682]
abbrev records4682_4683 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4682]
theorem aligned4682_4683 :
    AlignedValid 12 3 missing4682_4683 records4682_4683 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4682
    maskCheck4682 AlignedValid.nil

def missing4683_4684 : List (BitVec (edgeCount 12)) :=
  [missing4683]
abbrev records4683_4684 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4683]
theorem aligned4683_4684 :
    AlignedValid 12 3 missing4683_4684 records4683_4684 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4683
    maskCheck4683 AlignedValid.nil

def missing4682_4684 : List (BitVec (edgeCount 12)) :=
  missing4682_4683 ++ missing4683_4684
abbrev records4682_4684 : List Blob :=
  records4682_4683 ++ records4683_4684
theorem aligned4682_4684 :
    AlignedValid 12 3 missing4682_4684 records4682_4684 :=
  aligned4682_4683.append aligned4683_4684

def missing4680_4684 : List (BitVec (edgeCount 12)) :=
  missing4680_4682 ++ missing4682_4684
abbrev records4680_4684 : List Blob :=
  records4680_4682 ++ records4682_4684
theorem aligned4680_4684 :
    AlignedValid 12 3 missing4680_4684 records4680_4684 :=
  aligned4680_4682.append aligned4682_4684

def missing4684_4685 : List (BitVec (edgeCount 12)) :=
  [missing4684]
abbrev records4684_4685 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4684]
theorem aligned4684_4685 :
    AlignedValid 12 3 missing4684_4685 records4684_4685 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4684
    maskCheck4684 AlignedValid.nil

def missing4685_4686 : List (BitVec (edgeCount 12)) :=
  [missing4685]
abbrev records4685_4686 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4685]
theorem aligned4685_4686 :
    AlignedValid 12 3 missing4685_4686 records4685_4686 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4685
    maskCheck4685 AlignedValid.nil

def missing4684_4686 : List (BitVec (edgeCount 12)) :=
  missing4684_4685 ++ missing4685_4686
abbrev records4684_4686 : List Blob :=
  records4684_4685 ++ records4685_4686
theorem aligned4684_4686 :
    AlignedValid 12 3 missing4684_4686 records4684_4686 :=
  aligned4684_4685.append aligned4685_4686

def missing4686_4687 : List (BitVec (edgeCount 12)) :=
  [missing4686]
abbrev records4686_4687 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4686]
theorem aligned4686_4687 :
    AlignedValid 12 3 missing4686_4687 records4686_4687 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4686
    maskCheck4686 AlignedValid.nil

def missing4687_4688 : List (BitVec (edgeCount 12)) :=
  [missing4687]
abbrev records4687_4688 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4687]
theorem aligned4687_4688 :
    AlignedValid 12 3 missing4687_4688 records4687_4688 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4687
    maskCheck4687 AlignedValid.nil

def missing4686_4688 : List (BitVec (edgeCount 12)) :=
  missing4686_4687 ++ missing4687_4688
abbrev records4686_4688 : List Blob :=
  records4686_4687 ++ records4687_4688
theorem aligned4686_4688 :
    AlignedValid 12 3 missing4686_4688 records4686_4688 :=
  aligned4686_4687.append aligned4687_4688

def missing4684_4688 : List (BitVec (edgeCount 12)) :=
  missing4684_4686 ++ missing4686_4688
abbrev records4684_4688 : List Blob :=
  records4684_4686 ++ records4686_4688
theorem aligned4684_4688 :
    AlignedValid 12 3 missing4684_4688 records4684_4688 :=
  aligned4684_4686.append aligned4686_4688

def missing4680_4688 : List (BitVec (edgeCount 12)) :=
  missing4680_4684 ++ missing4684_4688
abbrev records4680_4688 : List Blob :=
  records4680_4684 ++ records4684_4688
theorem aligned4680_4688 :
    AlignedValid 12 3 missing4680_4688 records4680_4688 :=
  aligned4680_4684.append aligned4684_4688

def missing4672_4688 : List (BitVec (edgeCount 12)) :=
  missing4672_4680 ++ missing4680_4688
abbrev records4672_4688 : List Blob :=
  records4672_4680 ++ records4680_4688
theorem aligned4672_4688 :
    AlignedValid 12 3 missing4672_4688 records4672_4688 :=
  aligned4672_4680.append aligned4680_4688

def missing4688_4689 : List (BitVec (edgeCount 12)) :=
  [missing4688]
abbrev records4688_4689 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4688]
theorem aligned4688_4689 :
    AlignedValid 12 3 missing4688_4689 records4688_4689 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4688
    maskCheck4688 AlignedValid.nil

def missing4689_4690 : List (BitVec (edgeCount 12)) :=
  [missing4689]
abbrev records4689_4690 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4689]
theorem aligned4689_4690 :
    AlignedValid 12 3 missing4689_4690 records4689_4690 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4689
    maskCheck4689 AlignedValid.nil

def missing4688_4690 : List (BitVec (edgeCount 12)) :=
  missing4688_4689 ++ missing4689_4690
abbrev records4688_4690 : List Blob :=
  records4688_4689 ++ records4689_4690
theorem aligned4688_4690 :
    AlignedValid 12 3 missing4688_4690 records4688_4690 :=
  aligned4688_4689.append aligned4689_4690

def missing4690_4691 : List (BitVec (edgeCount 12)) :=
  [missing4690]
abbrev records4690_4691 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4690]
theorem aligned4690_4691 :
    AlignedValid 12 3 missing4690_4691 records4690_4691 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4690
    maskCheck4690 AlignedValid.nil

def missing4691_4692 : List (BitVec (edgeCount 12)) :=
  [missing4691]
abbrev records4691_4692 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4691]
theorem aligned4691_4692 :
    AlignedValid 12 3 missing4691_4692 records4691_4692 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4691
    maskCheck4691 AlignedValid.nil

def missing4690_4692 : List (BitVec (edgeCount 12)) :=
  missing4690_4691 ++ missing4691_4692
abbrev records4690_4692 : List Blob :=
  records4690_4691 ++ records4691_4692
theorem aligned4690_4692 :
    AlignedValid 12 3 missing4690_4692 records4690_4692 :=
  aligned4690_4691.append aligned4691_4692

def missing4688_4692 : List (BitVec (edgeCount 12)) :=
  missing4688_4690 ++ missing4690_4692
abbrev records4688_4692 : List Blob :=
  records4688_4690 ++ records4690_4692
theorem aligned4688_4692 :
    AlignedValid 12 3 missing4688_4692 records4688_4692 :=
  aligned4688_4690.append aligned4690_4692

def missing4692_4693 : List (BitVec (edgeCount 12)) :=
  [missing4692]
abbrev records4692_4693 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4692]
theorem aligned4692_4693 :
    AlignedValid 12 3 missing4692_4693 records4692_4693 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4692
    maskCheck4692 AlignedValid.nil

def missing4693_4694 : List (BitVec (edgeCount 12)) :=
  [missing4693]
abbrev records4693_4694 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4693]
theorem aligned4693_4694 :
    AlignedValid 12 3 missing4693_4694 records4693_4694 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4693
    maskCheck4693 AlignedValid.nil

def missing4692_4694 : List (BitVec (edgeCount 12)) :=
  missing4692_4693 ++ missing4693_4694
abbrev records4692_4694 : List Blob :=
  records4692_4693 ++ records4693_4694
theorem aligned4692_4694 :
    AlignedValid 12 3 missing4692_4694 records4692_4694 :=
  aligned4692_4693.append aligned4693_4694

def missing4694_4695 : List (BitVec (edgeCount 12)) :=
  [missing4694]
abbrev records4694_4695 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4694]
theorem aligned4694_4695 :
    AlignedValid 12 3 missing4694_4695 records4694_4695 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4694
    maskCheck4694 AlignedValid.nil

def missing4695_4696 : List (BitVec (edgeCount 12)) :=
  [missing4695]
abbrev records4695_4696 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4695]
theorem aligned4695_4696 :
    AlignedValid 12 3 missing4695_4696 records4695_4696 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4695
    maskCheck4695 AlignedValid.nil

def missing4694_4696 : List (BitVec (edgeCount 12)) :=
  missing4694_4695 ++ missing4695_4696
abbrev records4694_4696 : List Blob :=
  records4694_4695 ++ records4695_4696
theorem aligned4694_4696 :
    AlignedValid 12 3 missing4694_4696 records4694_4696 :=
  aligned4694_4695.append aligned4695_4696

def missing4692_4696 : List (BitVec (edgeCount 12)) :=
  missing4692_4694 ++ missing4694_4696
abbrev records4692_4696 : List Blob :=
  records4692_4694 ++ records4694_4696
theorem aligned4692_4696 :
    AlignedValid 12 3 missing4692_4696 records4692_4696 :=
  aligned4692_4694.append aligned4694_4696

def missing4688_4696 : List (BitVec (edgeCount 12)) :=
  missing4688_4692 ++ missing4692_4696
abbrev records4688_4696 : List Blob :=
  records4688_4692 ++ records4692_4696
theorem aligned4688_4696 :
    AlignedValid 12 3 missing4688_4696 records4688_4696 :=
  aligned4688_4692.append aligned4692_4696

def missing4696_4697 : List (BitVec (edgeCount 12)) :=
  [missing4696]
abbrev records4696_4697 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4696]
theorem aligned4696_4697 :
    AlignedValid 12 3 missing4696_4697 records4696_4697 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4696
    maskCheck4696 AlignedValid.nil

def missing4697_4698 : List (BitVec (edgeCount 12)) :=
  [missing4697]
abbrev records4697_4698 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4697]
theorem aligned4697_4698 :
    AlignedValid 12 3 missing4697_4698 records4697_4698 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4697
    maskCheck4697 AlignedValid.nil

def missing4696_4698 : List (BitVec (edgeCount 12)) :=
  missing4696_4697 ++ missing4697_4698
abbrev records4696_4698 : List Blob :=
  records4696_4697 ++ records4697_4698
theorem aligned4696_4698 :
    AlignedValid 12 3 missing4696_4698 records4696_4698 :=
  aligned4696_4697.append aligned4697_4698

def missing4698_4699 : List (BitVec (edgeCount 12)) :=
  [missing4698]
abbrev records4698_4699 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4698]
theorem aligned4698_4699 :
    AlignedValid 12 3 missing4698_4699 records4698_4699 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4698
    maskCheck4698 AlignedValid.nil

def missing4699_4700 : List (BitVec (edgeCount 12)) :=
  [missing4699]
abbrev records4699_4700 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4699]
theorem aligned4699_4700 :
    AlignedValid 12 3 missing4699_4700 records4699_4700 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4699
    maskCheck4699 AlignedValid.nil

def missing4698_4700 : List (BitVec (edgeCount 12)) :=
  missing4698_4699 ++ missing4699_4700
abbrev records4698_4700 : List Blob :=
  records4698_4699 ++ records4699_4700
theorem aligned4698_4700 :
    AlignedValid 12 3 missing4698_4700 records4698_4700 :=
  aligned4698_4699.append aligned4699_4700

def missing4696_4700 : List (BitVec (edgeCount 12)) :=
  missing4696_4698 ++ missing4698_4700
abbrev records4696_4700 : List Blob :=
  records4696_4698 ++ records4698_4700
theorem aligned4696_4700 :
    AlignedValid 12 3 missing4696_4700 records4696_4700 :=
  aligned4696_4698.append aligned4698_4700

def missing4700_4701 : List (BitVec (edgeCount 12)) :=
  [missing4700]
abbrev records4700_4701 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4700]
theorem aligned4700_4701 :
    AlignedValid 12 3 missing4700_4701 records4700_4701 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4700
    maskCheck4700 AlignedValid.nil

def missing4701_4702 : List (BitVec (edgeCount 12)) :=
  [missing4701]
abbrev records4701_4702 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4701]
theorem aligned4701_4702 :
    AlignedValid 12 3 missing4701_4702 records4701_4702 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4701
    maskCheck4701 AlignedValid.nil

def missing4700_4702 : List (BitVec (edgeCount 12)) :=
  missing4700_4701 ++ missing4701_4702
abbrev records4700_4702 : List Blob :=
  records4700_4701 ++ records4701_4702
theorem aligned4700_4702 :
    AlignedValid 12 3 missing4700_4702 records4700_4702 :=
  aligned4700_4701.append aligned4701_4702

def missing4702_4703 : List (BitVec (edgeCount 12)) :=
  [missing4702]
abbrev records4702_4703 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4702]
theorem aligned4702_4703 :
    AlignedValid 12 3 missing4702_4703 records4702_4703 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4702
    maskCheck4702 AlignedValid.nil

def missing4703_4704 : List (BitVec (edgeCount 12)) :=
  [missing4703]
abbrev records4703_4704 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4703]
theorem aligned4703_4704 :
    AlignedValid 12 3 missing4703_4704 records4703_4704 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4703
    maskCheck4703 AlignedValid.nil

def missing4702_4704 : List (BitVec (edgeCount 12)) :=
  missing4702_4703 ++ missing4703_4704
abbrev records4702_4704 : List Blob :=
  records4702_4703 ++ records4703_4704
theorem aligned4702_4704 :
    AlignedValid 12 3 missing4702_4704 records4702_4704 :=
  aligned4702_4703.append aligned4703_4704

def missing4700_4704 : List (BitVec (edgeCount 12)) :=
  missing4700_4702 ++ missing4702_4704
abbrev records4700_4704 : List Blob :=
  records4700_4702 ++ records4702_4704
theorem aligned4700_4704 :
    AlignedValid 12 3 missing4700_4704 records4700_4704 :=
  aligned4700_4702.append aligned4702_4704

def missing4696_4704 : List (BitVec (edgeCount 12)) :=
  missing4696_4700 ++ missing4700_4704
abbrev records4696_4704 : List Blob :=
  records4696_4700 ++ records4700_4704
theorem aligned4696_4704 :
    AlignedValid 12 3 missing4696_4704 records4696_4704 :=
  aligned4696_4700.append aligned4700_4704

def missing4688_4704 : List (BitVec (edgeCount 12)) :=
  missing4688_4696 ++ missing4696_4704
abbrev records4688_4704 : List Blob :=
  records4688_4696 ++ records4696_4704
theorem aligned4688_4704 :
    AlignedValid 12 3 missing4688_4704 records4688_4704 :=
  aligned4688_4696.append aligned4696_4704

def missing4672_4704 : List (BitVec (edgeCount 12)) :=
  missing4672_4688 ++ missing4688_4704
abbrev records4672_4704 : List Blob :=
  records4672_4688 ++ records4688_4704
theorem aligned4672_4704 :
    AlignedValid 12 3 missing4672_4704 records4672_4704 :=
  aligned4672_4688.append aligned4688_4704

def missing4704_4705 : List (BitVec (edgeCount 12)) :=
  [missing4704]
abbrev records4704_4705 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4704]
theorem aligned4704_4705 :
    AlignedValid 12 3 missing4704_4705 records4704_4705 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4704
    maskCheck4704 AlignedValid.nil

def missing4705_4706 : List (BitVec (edgeCount 12)) :=
  [missing4705]
abbrev records4705_4706 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4705]
theorem aligned4705_4706 :
    AlignedValid 12 3 missing4705_4706 records4705_4706 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4705
    maskCheck4705 AlignedValid.nil

def missing4704_4706 : List (BitVec (edgeCount 12)) :=
  missing4704_4705 ++ missing4705_4706
abbrev records4704_4706 : List Blob :=
  records4704_4705 ++ records4705_4706
theorem aligned4704_4706 :
    AlignedValid 12 3 missing4704_4706 records4704_4706 :=
  aligned4704_4705.append aligned4705_4706

def missing4706_4707 : List (BitVec (edgeCount 12)) :=
  [missing4706]
abbrev records4706_4707 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4706]
theorem aligned4706_4707 :
    AlignedValid 12 3 missing4706_4707 records4706_4707 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4706
    maskCheck4706 AlignedValid.nil

def missing4707_4708 : List (BitVec (edgeCount 12)) :=
  [missing4707]
abbrev records4707_4708 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4707]
theorem aligned4707_4708 :
    AlignedValid 12 3 missing4707_4708 records4707_4708 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4707
    maskCheck4707 AlignedValid.nil

def missing4706_4708 : List (BitVec (edgeCount 12)) :=
  missing4706_4707 ++ missing4707_4708
abbrev records4706_4708 : List Blob :=
  records4706_4707 ++ records4707_4708
theorem aligned4706_4708 :
    AlignedValid 12 3 missing4706_4708 records4706_4708 :=
  aligned4706_4707.append aligned4707_4708

def missing4704_4708 : List (BitVec (edgeCount 12)) :=
  missing4704_4706 ++ missing4706_4708
abbrev records4704_4708 : List Blob :=
  records4704_4706 ++ records4706_4708
theorem aligned4704_4708 :
    AlignedValid 12 3 missing4704_4708 records4704_4708 :=
  aligned4704_4706.append aligned4706_4708

def missing4708_4709 : List (BitVec (edgeCount 12)) :=
  [missing4708]
abbrev records4708_4709 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4708]
theorem aligned4708_4709 :
    AlignedValid 12 3 missing4708_4709 records4708_4709 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4708
    maskCheck4708 AlignedValid.nil

def missing4709_4710 : List (BitVec (edgeCount 12)) :=
  [missing4709]
abbrev records4709_4710 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4709]
theorem aligned4709_4710 :
    AlignedValid 12 3 missing4709_4710 records4709_4710 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4709
    maskCheck4709 AlignedValid.nil

def missing4708_4710 : List (BitVec (edgeCount 12)) :=
  missing4708_4709 ++ missing4709_4710
abbrev records4708_4710 : List Blob :=
  records4708_4709 ++ records4709_4710
theorem aligned4708_4710 :
    AlignedValid 12 3 missing4708_4710 records4708_4710 :=
  aligned4708_4709.append aligned4709_4710

def missing4710_4711 : List (BitVec (edgeCount 12)) :=
  [missing4710]
abbrev records4710_4711 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4710]
theorem aligned4710_4711 :
    AlignedValid 12 3 missing4710_4711 records4710_4711 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4710
    maskCheck4710 AlignedValid.nil

def missing4711_4712 : List (BitVec (edgeCount 12)) :=
  [missing4711]
abbrev records4711_4712 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4711]
theorem aligned4711_4712 :
    AlignedValid 12 3 missing4711_4712 records4711_4712 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4711
    maskCheck4711 AlignedValid.nil

def missing4710_4712 : List (BitVec (edgeCount 12)) :=
  missing4710_4711 ++ missing4711_4712
abbrev records4710_4712 : List Blob :=
  records4710_4711 ++ records4711_4712
theorem aligned4710_4712 :
    AlignedValid 12 3 missing4710_4712 records4710_4712 :=
  aligned4710_4711.append aligned4711_4712

def missing4708_4712 : List (BitVec (edgeCount 12)) :=
  missing4708_4710 ++ missing4710_4712
abbrev records4708_4712 : List Blob :=
  records4708_4710 ++ records4710_4712
theorem aligned4708_4712 :
    AlignedValid 12 3 missing4708_4712 records4708_4712 :=
  aligned4708_4710.append aligned4710_4712

def missing4704_4712 : List (BitVec (edgeCount 12)) :=
  missing4704_4708 ++ missing4708_4712
abbrev records4704_4712 : List Blob :=
  records4704_4708 ++ records4708_4712
theorem aligned4704_4712 :
    AlignedValid 12 3 missing4704_4712 records4704_4712 :=
  aligned4704_4708.append aligned4708_4712

def missing4712_4713 : List (BitVec (edgeCount 12)) :=
  [missing4712]
abbrev records4712_4713 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4712]
theorem aligned4712_4713 :
    AlignedValid 12 3 missing4712_4713 records4712_4713 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4712
    maskCheck4712 AlignedValid.nil

def missing4713_4714 : List (BitVec (edgeCount 12)) :=
  [missing4713]
abbrev records4713_4714 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4713]
theorem aligned4713_4714 :
    AlignedValid 12 3 missing4713_4714 records4713_4714 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4713
    maskCheck4713 AlignedValid.nil

def missing4712_4714 : List (BitVec (edgeCount 12)) :=
  missing4712_4713 ++ missing4713_4714
abbrev records4712_4714 : List Blob :=
  records4712_4713 ++ records4713_4714
theorem aligned4712_4714 :
    AlignedValid 12 3 missing4712_4714 records4712_4714 :=
  aligned4712_4713.append aligned4713_4714

def missing4714_4715 : List (BitVec (edgeCount 12)) :=
  [missing4714]
abbrev records4714_4715 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4714]
theorem aligned4714_4715 :
    AlignedValid 12 3 missing4714_4715 records4714_4715 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4714
    maskCheck4714 AlignedValid.nil

def missing4715_4716 : List (BitVec (edgeCount 12)) :=
  [missing4715]
abbrev records4715_4716 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4715]
theorem aligned4715_4716 :
    AlignedValid 12 3 missing4715_4716 records4715_4716 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4715
    maskCheck4715 AlignedValid.nil

def missing4714_4716 : List (BitVec (edgeCount 12)) :=
  missing4714_4715 ++ missing4715_4716
abbrev records4714_4716 : List Blob :=
  records4714_4715 ++ records4715_4716
theorem aligned4714_4716 :
    AlignedValid 12 3 missing4714_4716 records4714_4716 :=
  aligned4714_4715.append aligned4715_4716

def missing4712_4716 : List (BitVec (edgeCount 12)) :=
  missing4712_4714 ++ missing4714_4716
abbrev records4712_4716 : List Blob :=
  records4712_4714 ++ records4714_4716
theorem aligned4712_4716 :
    AlignedValid 12 3 missing4712_4716 records4712_4716 :=
  aligned4712_4714.append aligned4714_4716

def missing4716_4717 : List (BitVec (edgeCount 12)) :=
  [missing4716]
abbrev records4716_4717 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4716]
theorem aligned4716_4717 :
    AlignedValid 12 3 missing4716_4717 records4716_4717 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4716
    maskCheck4716 AlignedValid.nil

def missing4717_4718 : List (BitVec (edgeCount 12)) :=
  [missing4717]
abbrev records4717_4718 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4717]
theorem aligned4717_4718 :
    AlignedValid 12 3 missing4717_4718 records4717_4718 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4717
    maskCheck4717 AlignedValid.nil

def missing4716_4718 : List (BitVec (edgeCount 12)) :=
  missing4716_4717 ++ missing4717_4718
abbrev records4716_4718 : List Blob :=
  records4716_4717 ++ records4717_4718
theorem aligned4716_4718 :
    AlignedValid 12 3 missing4716_4718 records4716_4718 :=
  aligned4716_4717.append aligned4717_4718

def missing4718_4719 : List (BitVec (edgeCount 12)) :=
  [missing4718]
abbrev records4718_4719 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4718]
theorem aligned4718_4719 :
    AlignedValid 12 3 missing4718_4719 records4718_4719 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4718
    maskCheck4718 AlignedValid.nil

def missing4719_4720 : List (BitVec (edgeCount 12)) :=
  [missing4719]
abbrev records4719_4720 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4719]
theorem aligned4719_4720 :
    AlignedValid 12 3 missing4719_4720 records4719_4720 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4719
    maskCheck4719 AlignedValid.nil

def missing4718_4720 : List (BitVec (edgeCount 12)) :=
  missing4718_4719 ++ missing4719_4720
abbrev records4718_4720 : List Blob :=
  records4718_4719 ++ records4719_4720
theorem aligned4718_4720 :
    AlignedValid 12 3 missing4718_4720 records4718_4720 :=
  aligned4718_4719.append aligned4719_4720

def missing4716_4720 : List (BitVec (edgeCount 12)) :=
  missing4716_4718 ++ missing4718_4720
abbrev records4716_4720 : List Blob :=
  records4716_4718 ++ records4718_4720
theorem aligned4716_4720 :
    AlignedValid 12 3 missing4716_4720 records4716_4720 :=
  aligned4716_4718.append aligned4718_4720

def missing4712_4720 : List (BitVec (edgeCount 12)) :=
  missing4712_4716 ++ missing4716_4720
abbrev records4712_4720 : List Blob :=
  records4712_4716 ++ records4716_4720
theorem aligned4712_4720 :
    AlignedValid 12 3 missing4712_4720 records4712_4720 :=
  aligned4712_4716.append aligned4716_4720

def missing4704_4720 : List (BitVec (edgeCount 12)) :=
  missing4704_4712 ++ missing4712_4720
abbrev records4704_4720 : List Blob :=
  records4704_4712 ++ records4712_4720
theorem aligned4704_4720 :
    AlignedValid 12 3 missing4704_4720 records4704_4720 :=
  aligned4704_4712.append aligned4712_4720

def missing4720_4721 : List (BitVec (edgeCount 12)) :=
  [missing4720]
abbrev records4720_4721 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4720]
theorem aligned4720_4721 :
    AlignedValid 12 3 missing4720_4721 records4720_4721 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4720
    maskCheck4720 AlignedValid.nil

def missing4721_4722 : List (BitVec (edgeCount 12)) :=
  [missing4721]
abbrev records4721_4722 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4721]
theorem aligned4721_4722 :
    AlignedValid 12 3 missing4721_4722 records4721_4722 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4721
    maskCheck4721 AlignedValid.nil

def missing4720_4722 : List (BitVec (edgeCount 12)) :=
  missing4720_4721 ++ missing4721_4722
abbrev records4720_4722 : List Blob :=
  records4720_4721 ++ records4721_4722
theorem aligned4720_4722 :
    AlignedValid 12 3 missing4720_4722 records4720_4722 :=
  aligned4720_4721.append aligned4721_4722

def missing4722_4723 : List (BitVec (edgeCount 12)) :=
  [missing4722]
abbrev records4722_4723 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4722]
theorem aligned4722_4723 :
    AlignedValid 12 3 missing4722_4723 records4722_4723 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4722
    maskCheck4722 AlignedValid.nil

def missing4723_4724 : List (BitVec (edgeCount 12)) :=
  [missing4723]
abbrev records4723_4724 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4723]
theorem aligned4723_4724 :
    AlignedValid 12 3 missing4723_4724 records4723_4724 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4723
    maskCheck4723 AlignedValid.nil

def missing4722_4724 : List (BitVec (edgeCount 12)) :=
  missing4722_4723 ++ missing4723_4724
abbrev records4722_4724 : List Blob :=
  records4722_4723 ++ records4723_4724
theorem aligned4722_4724 :
    AlignedValid 12 3 missing4722_4724 records4722_4724 :=
  aligned4722_4723.append aligned4723_4724

def missing4720_4724 : List (BitVec (edgeCount 12)) :=
  missing4720_4722 ++ missing4722_4724
abbrev records4720_4724 : List Blob :=
  records4720_4722 ++ records4722_4724
theorem aligned4720_4724 :
    AlignedValid 12 3 missing4720_4724 records4720_4724 :=
  aligned4720_4722.append aligned4722_4724

def missing4724_4725 : List (BitVec (edgeCount 12)) :=
  [missing4724]
abbrev records4724_4725 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4724]
theorem aligned4724_4725 :
    AlignedValid 12 3 missing4724_4725 records4724_4725 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4724
    maskCheck4724 AlignedValid.nil

def missing4725_4726 : List (BitVec (edgeCount 12)) :=
  [missing4725]
abbrev records4725_4726 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4725]
theorem aligned4725_4726 :
    AlignedValid 12 3 missing4725_4726 records4725_4726 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4725
    maskCheck4725 AlignedValid.nil

def missing4724_4726 : List (BitVec (edgeCount 12)) :=
  missing4724_4725 ++ missing4725_4726
abbrev records4724_4726 : List Blob :=
  records4724_4725 ++ records4725_4726
theorem aligned4724_4726 :
    AlignedValid 12 3 missing4724_4726 records4724_4726 :=
  aligned4724_4725.append aligned4725_4726

def missing4726_4727 : List (BitVec (edgeCount 12)) :=
  [missing4726]
abbrev records4726_4727 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4726]
theorem aligned4726_4727 :
    AlignedValid 12 3 missing4726_4727 records4726_4727 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4726
    maskCheck4726 AlignedValid.nil

def missing4727_4728 : List (BitVec (edgeCount 12)) :=
  [missing4727]
abbrev records4727_4728 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4727]
theorem aligned4727_4728 :
    AlignedValid 12 3 missing4727_4728 records4727_4728 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4727
    maskCheck4727 AlignedValid.nil

def missing4726_4728 : List (BitVec (edgeCount 12)) :=
  missing4726_4727 ++ missing4727_4728
abbrev records4726_4728 : List Blob :=
  records4726_4727 ++ records4727_4728
theorem aligned4726_4728 :
    AlignedValid 12 3 missing4726_4728 records4726_4728 :=
  aligned4726_4727.append aligned4727_4728

def missing4724_4728 : List (BitVec (edgeCount 12)) :=
  missing4724_4726 ++ missing4726_4728
abbrev records4724_4728 : List Blob :=
  records4724_4726 ++ records4726_4728
theorem aligned4724_4728 :
    AlignedValid 12 3 missing4724_4728 records4724_4728 :=
  aligned4724_4726.append aligned4726_4728

def missing4720_4728 : List (BitVec (edgeCount 12)) :=
  missing4720_4724 ++ missing4724_4728
abbrev records4720_4728 : List Blob :=
  records4720_4724 ++ records4724_4728
theorem aligned4720_4728 :
    AlignedValid 12 3 missing4720_4728 records4720_4728 :=
  aligned4720_4724.append aligned4724_4728

def missing4728_4729 : List (BitVec (edgeCount 12)) :=
  [missing4728]
abbrev records4728_4729 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4728]
theorem aligned4728_4729 :
    AlignedValid 12 3 missing4728_4729 records4728_4729 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4728
    maskCheck4728 AlignedValid.nil

def missing4729_4730 : List (BitVec (edgeCount 12)) :=
  [missing4729]
abbrev records4729_4730 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4729]
theorem aligned4729_4730 :
    AlignedValid 12 3 missing4729_4730 records4729_4730 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4729
    maskCheck4729 AlignedValid.nil

def missing4728_4730 : List (BitVec (edgeCount 12)) :=
  missing4728_4729 ++ missing4729_4730
abbrev records4728_4730 : List Blob :=
  records4728_4729 ++ records4729_4730
theorem aligned4728_4730 :
    AlignedValid 12 3 missing4728_4730 records4728_4730 :=
  aligned4728_4729.append aligned4729_4730

def missing4730_4731 : List (BitVec (edgeCount 12)) :=
  [missing4730]
abbrev records4730_4731 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4730]
theorem aligned4730_4731 :
    AlignedValid 12 3 missing4730_4731 records4730_4731 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4730
    maskCheck4730 AlignedValid.nil

def missing4731_4732 : List (BitVec (edgeCount 12)) :=
  [missing4731]
abbrev records4731_4732 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4731]
theorem aligned4731_4732 :
    AlignedValid 12 3 missing4731_4732 records4731_4732 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4731
    maskCheck4731 AlignedValid.nil

def missing4730_4732 : List (BitVec (edgeCount 12)) :=
  missing4730_4731 ++ missing4731_4732
abbrev records4730_4732 : List Blob :=
  records4730_4731 ++ records4731_4732
theorem aligned4730_4732 :
    AlignedValid 12 3 missing4730_4732 records4730_4732 :=
  aligned4730_4731.append aligned4731_4732

def missing4728_4732 : List (BitVec (edgeCount 12)) :=
  missing4728_4730 ++ missing4730_4732
abbrev records4728_4732 : List Blob :=
  records4728_4730 ++ records4730_4732
theorem aligned4728_4732 :
    AlignedValid 12 3 missing4728_4732 records4728_4732 :=
  aligned4728_4730.append aligned4730_4732

def missing4732_4733 : List (BitVec (edgeCount 12)) :=
  [missing4732]
abbrev records4732_4733 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4732]
theorem aligned4732_4733 :
    AlignedValid 12 3 missing4732_4733 records4732_4733 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4732
    maskCheck4732 AlignedValid.nil

def missing4733_4734 : List (BitVec (edgeCount 12)) :=
  [missing4733]
abbrev records4733_4734 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4733]
theorem aligned4733_4734 :
    AlignedValid 12 3 missing4733_4734 records4733_4734 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4733
    maskCheck4733 AlignedValid.nil

def missing4732_4734 : List (BitVec (edgeCount 12)) :=
  missing4732_4733 ++ missing4733_4734
abbrev records4732_4734 : List Blob :=
  records4732_4733 ++ records4733_4734
theorem aligned4732_4734 :
    AlignedValid 12 3 missing4732_4734 records4732_4734 :=
  aligned4732_4733.append aligned4733_4734

def missing4734_4735 : List (BitVec (edgeCount 12)) :=
  [missing4734]
abbrev records4734_4735 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4734]
theorem aligned4734_4735 :
    AlignedValid 12 3 missing4734_4735 records4734_4735 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4734
    maskCheck4734 AlignedValid.nil

def missing4735_4736 : List (BitVec (edgeCount 12)) :=
  [missing4735]
abbrev records4735_4736 : List Blob :=
  [StrongPackedBucketN12A3Shard036.record4735]
theorem aligned4735_4736 :
    AlignedValid 12 3 missing4735_4736 records4735_4736 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard036.check4735
    maskCheck4735 AlignedValid.nil

def missing4734_4736 : List (BitVec (edgeCount 12)) :=
  missing4734_4735 ++ missing4735_4736
abbrev records4734_4736 : List Blob :=
  records4734_4735 ++ records4735_4736
theorem aligned4734_4736 :
    AlignedValid 12 3 missing4734_4736 records4734_4736 :=
  aligned4734_4735.append aligned4735_4736

def missing4732_4736 : List (BitVec (edgeCount 12)) :=
  missing4732_4734 ++ missing4734_4736
abbrev records4732_4736 : List Blob :=
  records4732_4734 ++ records4734_4736
theorem aligned4732_4736 :
    AlignedValid 12 3 missing4732_4736 records4732_4736 :=
  aligned4732_4734.append aligned4734_4736

def missing4728_4736 : List (BitVec (edgeCount 12)) :=
  missing4728_4732 ++ missing4732_4736
abbrev records4728_4736 : List Blob :=
  records4728_4732 ++ records4732_4736
theorem aligned4728_4736 :
    AlignedValid 12 3 missing4728_4736 records4728_4736 :=
  aligned4728_4732.append aligned4732_4736

def missing4720_4736 : List (BitVec (edgeCount 12)) :=
  missing4720_4728 ++ missing4728_4736
abbrev records4720_4736 : List Blob :=
  records4720_4728 ++ records4728_4736
theorem aligned4720_4736 :
    AlignedValid 12 3 missing4720_4736 records4720_4736 :=
  aligned4720_4728.append aligned4728_4736

def missing4704_4736 : List (BitVec (edgeCount 12)) :=
  missing4704_4720 ++ missing4720_4736
abbrev records4704_4736 : List Blob :=
  records4704_4720 ++ records4720_4736
theorem aligned4704_4736 :
    AlignedValid 12 3 missing4704_4736 records4704_4736 :=
  aligned4704_4720.append aligned4720_4736

def missing4672_4736 : List (BitVec (edgeCount 12)) :=
  missing4672_4704 ++ missing4704_4736
abbrev records4672_4736 : List Blob :=
  records4672_4704 ++ records4704_4736
theorem aligned4672_4736 :
    AlignedValid 12 3 missing4672_4736 records4672_4736 :=
  aligned4672_4704.append aligned4704_4736

def missing4608_4736 : List (BitVec (edgeCount 12)) :=
  missing4608_4672 ++ missing4672_4736
abbrev records4608_4736 : List Blob :=
  records4608_4672 ++ records4672_4736
theorem aligned4608_4736 :
    AlignedValid 12 3 missing4608_4736 records4608_4736 :=
  aligned4608_4672.append aligned4672_4736

abbrev missing : List (BitVec (edgeCount 12)) := missing4608_4736
abbrev records : List Blob := records4608_4736
theorem aligned : AlignedValid 12 3 missing records := aligned4608_4736

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard036
