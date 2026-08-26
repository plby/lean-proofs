/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard224

/-! Decode-only alignment checks for n=12, a=4, records 28672--28799. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard224

open PackedBucketCertificate

def missing28672 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11565634721083817984
theorem maskCheck28672 :
    checkMaskFor missing28672 StrongPackedBucketN12A4Shard224.record28672 = true := by
  decide

def missing28673 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11673721112140709888
theorem maskCheck28673 :
    checkMaskFor missing28673 StrongPackedBucketN12A4Shard224.record28673 = true := by
  decide

def missing28674 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13871477730297511936
theorem maskCheck28674 :
    checkMaskFor missing28674 StrongPackedBucketN12A4Shard224.record28674 = true := by
  decide

def missing28675 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13979564121354403840
theorem maskCheck28675 :
    checkMaskFor missing28675 StrongPackedBucketN12A4Shard224.record28675 = true := by
  decide

def missing28676 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14411909685581971456
theorem maskCheck28676 :
    checkMaskFor missing28676 StrongPackedBucketN12A4Shard224.record28676 = true := by
  decide

def missing28677 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16141291942492241920
theorem maskCheck28677 :
    checkMaskFor missing28677 StrongPackedBucketN12A4Shard224.record28677 = true := by
  decide

def missing28678 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 252698010245398528
theorem maskCheck28678 :
    checkMaskFor missing28678 StrongPackedBucketN12A4Shard224.record28678 = true := by
  decide

def missing28679 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 504899589378146304
theorem maskCheck28679 :
    checkMaskFor missing28679 StrongPackedBucketN12A4Shard224.record28679 = true := by
  decide

def missing28680 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2522512222440128512
theorem maskCheck28680 :
    checkMaskFor missing28680 StrongPackedBucketN12A4Shard224.record28680 = true := by
  decide

def missing28681 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5224671998862426112
theorem maskCheck28681 :
    checkMaskFor missing28681 StrongPackedBucketN12A4Shard224.record28681 = true := by
  decide

def missing28682 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6954054255772696576
theorem maskCheck28682 :
    checkMaskFor missing28682 StrongPackedBucketN12A4Shard224.record28682 = true := by
  decide

def missing28683 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9440041250081210368
theorem maskCheck28683 :
    checkMaskFor missing28683 StrongPackedBucketN12A4Shard224.record28683 = true := by
  decide

def missing28684 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9836358017289814016
theorem maskCheck28684 :
    checkMaskFor missing28684 StrongPackedBucketN12A4Shard224.record28684 = true := by
  decide

def missing28685 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10953250724877697024
theorem maskCheck28685 :
    checkMaskFor missing28685 StrongPackedBucketN12A4Shard224.record28685 = true := by
  decide

def missing28686 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11565740274200084480
theorem maskCheck28686 :
    checkMaskFor missing28686 StrongPackedBucketN12A4Shard224.record28686 = true := by
  decide

def missing28687 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13871583283413778432
theorem maskCheck28687 :
    checkMaskFor missing28687 StrongPackedBucketN12A4Shard224.record28687 = true := by
  decide

def missing28688 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 901603384679727104
theorem maskCheck28688 :
    checkMaskFor missing28688 StrongPackedBucketN12A4Shard224.record28688 = true := by
  decide

def missing28689 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1369977745926258688
theorem maskCheck28689 :
    checkMaskFor missing28689 StrongPackedBucketN12A4Shard224.record28689 = true := by
  decide

def missing28690 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2522899250533105664
theorem maskCheck28690 :
    checkMaskFor missing28690 StrongPackedBucketN12A4Shard224.record28690 = true := by
  decide

def missing28691 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4828742259746799616
theorem maskCheck28691 :
    checkMaskFor missing28691 StrongPackedBucketN12A4Shard224.record28691 = true := by
  decide

def missing28692 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5837548576277790720
theorem maskCheck28692 :
    checkMaskFor missing28692 StrongPackedBucketN12A4Shard224.record28692 = true := by
  decide

def missing28693 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6990470080884637696
theorem maskCheck28693 :
    checkMaskFor missing28693 StrongPackedBucketN12A4Shard224.record28693 = true := by
  decide

def missing28694 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9332341887117295616
theorem maskCheck28694 :
    checkMaskFor missing28694 StrongPackedBucketN12A4Shard224.record28694 = true := by
  decide

def missing28695 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9440428278174187520
theorem maskCheck28695 :
    checkMaskFor missing28695 StrongPackedBucketN12A4Shard224.record28695 = true := by
  decide

def missing28696 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10088946624515538944
theorem maskCheck28696 :
    checkMaskFor missing28696 StrongPackedBucketN12A4Shard224.record28696 = true := by
  decide

def missing28697 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11602156099312025600
theorem maskCheck28697 :
    checkMaskFor missing28697 StrongPackedBucketN12A4Shard224.record28697 = true := by
  decide

def missing28698 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13907999108525719552
theorem maskCheck28698 :
    checkMaskFor missing28698 StrongPackedBucketN12A4Shard224.record28698 = true := by
  decide

def missing28699 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14988863019094638592
theorem maskCheck28699 :
    checkMaskFor missing28699 StrongPackedBucketN12A4Shard224.record28699 = true := by
  decide

def missing28700 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16141784523701485568
theorem maskCheck28700 :
    checkMaskFor missing28700 StrongPackedBucketN12A4Shard224.record28700 = true := by
  decide

def missing28701 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 937667366070779904
theorem maskCheck28701 :
    checkMaskFor missing28701 StrongPackedBucketN12A4Shard224.record28701 = true := by
  decide

def missing28702 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1333984133279383552
theorem maskCheck28702 :
    checkMaskFor missing28702 StrongPackedBucketN12A4Shard224.record28702 = true := by
  decide

def missing28703 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2486905637886230528
theorem maskCheck28703 :
    checkMaskFor missing28703 StrongPackedBucketN12A4Shard224.record28703 = true := by
  decide

def missing28704 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3495711954417221632
theorem maskCheck28704 :
    checkMaskFor missing28704 StrongPackedBucketN12A4Shard224.record28704 = true := by
  decide

def missing28705 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4792748647099924480
theorem maskCheck28705 :
    checkMaskFor missing28705 StrongPackedBucketN12A4Shard224.record28705 = true := by
  decide

def missing28706 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5801554963630915584
theorem maskCheck28706 :
    checkMaskFor missing28706 StrongPackedBucketN12A4Shard224.record28706 = true := by
  decide

def missing28707 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6954476468237762560
theorem maskCheck28707 :
    checkMaskFor missing28707 StrongPackedBucketN12A4Shard224.record28707 = true := by
  decide

def missing28708 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9404434665527312384
theorem maskCheck28708 :
    checkMaskFor missing28708 StrongPackedBucketN12A4Shard224.record28708 = true := by
  decide

def missing28709 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10413240982058303488
theorem maskCheck28709 :
    checkMaskFor missing28709 StrongPackedBucketN12A4Shard224.record28709 = true := by
  decide

def missing28710 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10521327373115195392
theorem maskCheck28710 :
    checkMaskFor missing28710 StrongPackedBucketN12A4Shard224.record28710 = true := by
  decide

def missing28711 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11566162486665150464
theorem maskCheck28711 :
    checkMaskFor missing28711 StrongPackedBucketN12A4Shard224.record28711 = true := by
  decide

def missing28712 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12683055194253033472
theorem maskCheck28712 :
    checkMaskFor missing28712 StrongPackedBucketN12A4Shard224.record28712 = true := by
  decide

def missing28713 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13872005495878844416
theorem maskCheck28713 :
    checkMaskFor missing28713 StrongPackedBucketN12A4Shard224.record28713 = true := by
  decide

def missing28714 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 254175753873129472
theorem maskCheck28714 :
    checkMaskFor missing28714 StrongPackedBucketN12A4Shard224.record28714 = true := by
  decide

def missing28715 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2019586807802363904
theorem maskCheck28715 :
    checkMaskFor missing28715 StrongPackedBucketN12A4Shard224.record28715 = true := by
  decide

def missing28716 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2415903575010967552
theorem maskCheck28716 :
    checkMaskFor missing28716 StrongPackedBucketN12A4Shard224.record28716 = true := by
  decide

def missing28717 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2523989966067859456
theorem maskCheck28717 :
    checkMaskFor missing28717 StrongPackedBucketN12A4Shard224.record28717 = true := by
  decide

def missing28718 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4721746584224661504
theorem maskCheck28718 :
    checkMaskFor missing28718 StrongPackedBucketN12A4Shard224.record28718 = true := by
  decide

def missing28719 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6955531999400427520
theorem maskCheck28719 :
    checkMaskFor missing28719 StrongPackedBucketN12A4Shard224.record28719 = true := by
  decide

def missing28720 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9333432602652049408
theorem maskCheck28720 :
    checkMaskFor missing28720 StrongPackedBucketN12A4Shard224.record28720 = true := by
  decide

def missing28721 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9441518993708941312
theorem maskCheck28721 :
    checkMaskFor missing28721 StrongPackedBucketN12A4Shard224.record28721 = true := by
  decide

def missing28722 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11567218017827815424
theorem maskCheck28722 :
    checkMaskFor missing28722 StrongPackedBucketN12A4Shard224.record28722 = true := by
  decide

def missing28723 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11603246814846779392
theorem maskCheck28723 :
    checkMaskFor missing28723 StrongPackedBucketN12A4Shard224.record28723 = true := by
  decide

def missing28724 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13873061027041509376
theorem maskCheck28724 :
    checkMaskFor missing28724 StrongPackedBucketN12A4Shard224.record28724 = true := by
  decide

def missing28725 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 254562781966106624
theorem maskCheck28725 :
    checkMaskFor missing28725 StrongPackedBucketN12A4Shard224.record28725 = true := by
  decide

def missing28726 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5046392785488314368
theorem maskCheck28726 :
    checkMaskFor missing28726 StrongPackedBucketN12A4Shard224.record28726 = true := by
  decide

def missing28727 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7064005418550296576
theorem maskCheck28727 :
    checkMaskFor missing28727 StrongPackedBucketN12A4Shard224.record28727 = true := by
  decide

def missing28728 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9333819630745026560
theorem maskCheck28728 :
    checkMaskFor missing28728 StrongPackedBucketN12A4Shard224.record28728 = true := by
  decide

def missing28729 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9405877224782954496
theorem maskCheck28729 :
    checkMaskFor missing28729 StrongPackedBucketN12A4Shard224.record28729 = true := by
  decide

def missing28730 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9549992412858810368
theorem maskCheck28730 :
    checkMaskFor missing28730 StrongPackedBucketN12A4Shard224.record28730 = true := by
  decide

def missing28731 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11567605045920792576
theorem maskCheck28731 :
    checkMaskFor missing28731 StrongPackedBucketN12A4Shard224.record28731 = true := by
  decide

def missing28732 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11675691436977684480
theorem maskCheck28732 :
    checkMaskFor missing28732 StrongPackedBucketN12A4Shard224.record28732 = true := by
  decide

def missing28733 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13873448055134486528
theorem maskCheck28733 :
    checkMaskFor missing28733 StrongPackedBucketN12A4Shard224.record28733 = true := by
  decide

def missing28734 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13981534446191378432
theorem maskCheck28734 :
    checkMaskFor missing28734 StrongPackedBucketN12A4Shard224.record28734 = true := by
  decide

def missing28735 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14125649634267234304
theorem maskCheck28735 :
    checkMaskFor missing28735 StrongPackedBucketN12A4Shard224.record28735 = true := by
  decide

def missing28736 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16143262267329216512
theorem maskCheck28736 :
    checkMaskFor missing28736 StrongPackedBucketN12A4Shard224.record28736 = true := by
  decide

def missing28737 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 254668335082373120
theorem maskCheck28737 :
    checkMaskFor missing28737 StrongPackedBucketN12A4Shard224.record28737 = true := by
  decide

def missing28738 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2524482547277103104
theorem maskCheck28738 :
    checkMaskFor missing28738 StrongPackedBucketN12A4Shard224.record28738 = true := by
  decide

def missing28739 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4938411947547688960
theorem maskCheck28739 :
    checkMaskFor missing28739 StrongPackedBucketN12A4Shard224.record28739 = true := by
  decide

def missing28740 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6956024580609671168
theorem maskCheck28740 :
    checkMaskFor missing28740 StrongPackedBucketN12A4Shard224.record28740 = true := by
  decide

def missing28741 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9442011574918184960
theorem maskCheck28741 :
    checkMaskFor missing28741 StrongPackedBucketN12A4Shard224.record28741 = true := by
  decide

def missing28742 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9550097965975076864
theorem maskCheck28742 :
    checkMaskFor missing28742 StrongPackedBucketN12A4Shard224.record28742 = true := by
  decide

def missing28743 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10090529921259536384
theorem maskCheck28743 :
    checkMaskFor missing28743 StrongPackedBucketN12A4Shard224.record28743 = true := by
  decide

def missing28744 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11567710599037059072
theorem maskCheck28744 :
    checkMaskFor missing28744 StrongPackedBucketN12A4Shard224.record28744 = true := by
  decide

def missing28745 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13873553608250753024
theorem maskCheck28745 :
    checkMaskFor missing28745 StrongPackedBucketN12A4Shard224.record28745 = true := by
  decide

def missing28746 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 795205843483099136
theorem maskCheck28746 :
    checkMaskFor missing28746 StrongPackedBucketN12A4Shard224.record28746 = true := by
  decide

def missing28747 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2524588100393369600
theorem maskCheck28747 :
    checkMaskFor missing28747 StrongPackedBucketN12A4Shard224.record28747 = true := by
  decide

def missing28748 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4830431109607063552
theorem maskCheck28748 :
    checkMaskFor missing28748 StrongPackedBucketN12A4Shard224.record28748 = true := by
  decide

def missing28749 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5262776673834631168
theorem maskCheck28749 :
    checkMaskFor missing28749 StrongPackedBucketN12A4Shard224.record28749 = true := by
  decide

def missing28750 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6343640584403550208
theorem maskCheck28750 :
    checkMaskFor missing28750 StrongPackedBucketN12A4Shard224.record28750 = true := by
  decide

def missing28751 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6992158930744901632
theorem maskCheck28751 :
    checkMaskFor missing28751 StrongPackedBucketN12A4Shard224.record28751 = true := by
  decide

def missing28752 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7496562089010397184
theorem maskCheck28752 :
    checkMaskFor missing28752 StrongPackedBucketN12A4Shard224.record28752 = true := by
  decide

def missing28753 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9334030736977559552
theorem maskCheck28753 :
    checkMaskFor missing28753 StrongPackedBucketN12A4Shard224.record28753 = true := by
  decide

def missing28754 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9442117128034451456
theorem maskCheck28754 :
    checkMaskFor missing28754 StrongPackedBucketN12A4Shard224.record28754 = true := by
  decide

def missing28755 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9550203519091343360
theorem maskCheck28755 :
    checkMaskFor missing28755 StrongPackedBucketN12A4Shard224.record28755 = true := by
  decide

def missing28756 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9838433895243055104
theorem maskCheck28756 :
    checkMaskFor missing28756 StrongPackedBucketN12A4Shard224.record28756 = true := by
  decide

def missing28757 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11567816152153325568
theorem maskCheck28757 :
    checkMaskFor missing28757 StrongPackedBucketN12A4Shard224.record28757 = true := by
  decide

def missing28758 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13909687958385983488
theorem maskCheck28758 :
    checkMaskFor missing28758 StrongPackedBucketN12A4Shard224.record28758 = true := by
  decide

def missing28759 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14414091116651479040
theorem maskCheck28759 :
    checkMaskFor missing28759 StrongPackedBucketN12A4Shard224.record28759 = true := by
  decide

def missing28760 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16143473373561749504
theorem maskCheck28760 :
    checkMaskFor missing28760 StrongPackedBucketN12A4Shard224.record28760 = true := by
  decide

def missing28761 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 759212230836224000
theorem maskCheck28761 :
    checkMaskFor missing28761 StrongPackedBucketN12A4Shard224.record28761 = true := by
  decide

def missing28762 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1768018547367215104
theorem maskCheck28762 :
    checkMaskFor missing28762 StrongPackedBucketN12A4Shard224.record28762 = true := by
  decide

def missing28763 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1876104938424107008
theorem maskCheck28763 :
    checkMaskFor missing28763 StrongPackedBucketN12A4Shard224.record28763 = true := by
  decide

def missing28764 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2488594487746494464
theorem maskCheck28764 :
    checkMaskFor missing28764 StrongPackedBucketN12A4Shard224.record28764 = true := by
  decide

def missing28765 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2920940051974062080
theorem maskCheck28765 :
    checkMaskFor missing28765 StrongPackedBucketN12A4Shard224.record28765 = true := by
  decide

def missing28766 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3029026443030953984
theorem maskCheck28766 :
    checkMaskFor missing28766 StrongPackedBucketN12A4Shard224.record28766 = true := by
  decide

def missing28767 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4794437496960188416
theorem maskCheck28767 :
    checkMaskFor missing28767 StrongPackedBucketN12A4Shard224.record28767 = true := by
  decide

def missing28768 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5226783061187756032
theorem maskCheck28768 :
    checkMaskFor missing28768 StrongPackedBucketN12A4Shard224.record28768 = true := by
  decide

def missing28769 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6956165318098026496
theorem maskCheck28769 :
    checkMaskFor missing28769 StrongPackedBucketN12A4Shard224.record28769 = true := by
  decide

def missing28770 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9406123515387576320
theorem maskCheck28770 :
    checkMaskFor missing28770 StrongPackedBucketN12A4Shard224.record28770 = true := by
  decide

def missing28771 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9838469079615143936
theorem maskCheck28771 :
    checkMaskFor missing28771 StrongPackedBucketN12A4Shard224.record28771 = true := by
  decide

def missing28772 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9946555470672035840
theorem maskCheck28772 :
    checkMaskFor missing28772 StrongPackedBucketN12A4Shard224.record28772 = true := by
  decide

def missing28773 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10955361787203026944
theorem maskCheck28773 :
    checkMaskFor missing28773 StrongPackedBucketN12A4Shard224.record28773 = true := by
  decide

def missing28774 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11567851336525414400
theorem maskCheck28774 :
    checkMaskFor missing28774 StrongPackedBucketN12A4Shard224.record28774 = true := by
  decide

def missing28775 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11675937727582306304
theorem maskCheck28775 :
    checkMaskFor missing28775 StrongPackedBucketN12A4Shard224.record28775 = true := by
  decide

def missing28776 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12108283291809873920
theorem maskCheck28776 :
    checkMaskFor missing28776 StrongPackedBucketN12A4Shard224.record28776 = true := by
  decide

def missing28777 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13873694345739108352
theorem maskCheck28777 :
    checkMaskFor missing28777 StrongPackedBucketN12A4Shard224.record28777 = true := by
  decide

def missing28778 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 255301653779972096
theorem maskCheck28778 :
    checkMaskFor missing28778 StrongPackedBucketN12A4Shard224.record28778 = true := by
  decide

def missing28779 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1264107970310963200
theorem maskCheck28779 :
    checkMaskFor missing28779 StrongPackedBucketN12A4Shard224.record28779 = true := by
  decide

def missing28780 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1372194361367855104
theorem maskCheck28780 :
    checkMaskFor missing28780 StrongPackedBucketN12A4Shard224.record28780 = true := by
  decide

def missing28781 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3497893385486729216
theorem maskCheck28781 :
    checkMaskFor missing28781 StrongPackedBucketN12A4Shard224.record28781 = true := by
  decide

def missing28782 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3533922182505693184
theorem maskCheck28782 :
    checkMaskFor missing28782 StrongPackedBucketN12A4Shard224.record28782 = true := by
  decide

def missing28783 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4722872484131504128
theorem maskCheck28783 :
    checkMaskFor missing28783 StrongPackedBucketN12A4Shard224.record28783 = true := by
  decide

def missing28784 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5803736394700423168
theorem maskCheck28784 :
    checkMaskFor missing28784 StrongPackedBucketN12A4Shard224.record28784 = true := by
  decide

def missing28785 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9334558502558892032
theorem maskCheck28785 :
    checkMaskFor missing28785 StrongPackedBucketN12A4Shard224.record28785 = true := by
  decide

def missing28786 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9442644893615783936
theorem maskCheck28786 :
    checkMaskFor missing28786 StrongPackedBucketN12A4Shard224.record28786 = true := by
  decide

def missing28787 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10415422413127811072
theorem maskCheck28787 :
    checkMaskFor missing28787 StrongPackedBucketN12A4Shard224.record28787 = true := by
  decide

def missing28788 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10451451210146775040
theorem maskCheck28788 :
    checkMaskFor missing28788 StrongPackedBucketN12A4Shard224.record28788 = true := by
  decide

def missing28789 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12685236625322541056
theorem maskCheck28789 :
    checkMaskFor missing28789 StrongPackedBucketN12A4Shard224.record28789 = true := by
  decide

def missing28790 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13874186926948352000
theorem maskCheck28790 :
    checkMaskFor missing28790 StrongPackedBucketN12A4Shard224.record28790 = true := by
  decide

def missing28791 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 256814581779791872
theorem maskCheck28791 :
    checkMaskFor missing28791 StrongPackedBucketN12A4Shard224.record28791 = true := by
  decide

def missing28792 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9336071430558711808
theorem maskCheck28792 :
    checkMaskFor missing28792 StrongPackedBucketN12A4Shard224.record28792 = true := by
  decide

def missing28793 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9408129024596639744
theorem maskCheck28793 :
    checkMaskFor missing28793 StrongPackedBucketN12A4Shard224.record28793 = true := by
  decide

def missing28794 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11677943236791369728
theorem maskCheck28794 :
    checkMaskFor missing28794 StrongPackedBucketN12A4Shard224.record28794 = true := by
  decide

def missing28795 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13875699854948171776
theorem maskCheck28795 :
    checkMaskFor missing28795 StrongPackedBucketN12A4Shard224.record28795 = true := by
  decide

def missing28796 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9444368927848136704
theorem maskCheck28796 :
    checkMaskFor missing28796 StrongPackedBucketN12A4Shard224.record28796 = true := by
  decide

def missing28797 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9552455318905028608
theorem maskCheck28797 :
    checkMaskFor missing28797 StrongPackedBucketN12A4Shard224.record28797 = true := by
  decide

def missing28798 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11606096748985974784
theorem maskCheck28798 :
    checkMaskFor missing28798 StrongPackedBucketN12A4Shard224.record28798 = true := by
  decide

def missing28799 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13875910961180704768
theorem maskCheck28799 :
    checkMaskFor missing28799 StrongPackedBucketN12A4Shard224.record28799 = true := by
  decide

def missing28672_28673 : List (BitVec (edgeCount 12)) :=
  [missing28672]
abbrev records28672_28673 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28672]
theorem aligned28672_28673 :
    AlignedValid 12 4 missing28672_28673 records28672_28673 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28672
    maskCheck28672 AlignedValid.nil

def missing28673_28674 : List (BitVec (edgeCount 12)) :=
  [missing28673]
abbrev records28673_28674 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28673]
theorem aligned28673_28674 :
    AlignedValid 12 4 missing28673_28674 records28673_28674 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28673
    maskCheck28673 AlignedValid.nil

def missing28672_28674 : List (BitVec (edgeCount 12)) :=
  missing28672_28673 ++ missing28673_28674
abbrev records28672_28674 : List Blob :=
  records28672_28673 ++ records28673_28674
theorem aligned28672_28674 :
    AlignedValid 12 4 missing28672_28674 records28672_28674 :=
  aligned28672_28673.append aligned28673_28674

def missing28674_28675 : List (BitVec (edgeCount 12)) :=
  [missing28674]
abbrev records28674_28675 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28674]
theorem aligned28674_28675 :
    AlignedValid 12 4 missing28674_28675 records28674_28675 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28674
    maskCheck28674 AlignedValid.nil

def missing28675_28676 : List (BitVec (edgeCount 12)) :=
  [missing28675]
abbrev records28675_28676 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28675]
theorem aligned28675_28676 :
    AlignedValid 12 4 missing28675_28676 records28675_28676 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28675
    maskCheck28675 AlignedValid.nil

def missing28674_28676 : List (BitVec (edgeCount 12)) :=
  missing28674_28675 ++ missing28675_28676
abbrev records28674_28676 : List Blob :=
  records28674_28675 ++ records28675_28676
theorem aligned28674_28676 :
    AlignedValid 12 4 missing28674_28676 records28674_28676 :=
  aligned28674_28675.append aligned28675_28676

def missing28672_28676 : List (BitVec (edgeCount 12)) :=
  missing28672_28674 ++ missing28674_28676
abbrev records28672_28676 : List Blob :=
  records28672_28674 ++ records28674_28676
theorem aligned28672_28676 :
    AlignedValid 12 4 missing28672_28676 records28672_28676 :=
  aligned28672_28674.append aligned28674_28676

def missing28676_28677 : List (BitVec (edgeCount 12)) :=
  [missing28676]
abbrev records28676_28677 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28676]
theorem aligned28676_28677 :
    AlignedValid 12 4 missing28676_28677 records28676_28677 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28676
    maskCheck28676 AlignedValid.nil

def missing28677_28678 : List (BitVec (edgeCount 12)) :=
  [missing28677]
abbrev records28677_28678 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28677]
theorem aligned28677_28678 :
    AlignedValid 12 4 missing28677_28678 records28677_28678 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28677
    maskCheck28677 AlignedValid.nil

def missing28676_28678 : List (BitVec (edgeCount 12)) :=
  missing28676_28677 ++ missing28677_28678
abbrev records28676_28678 : List Blob :=
  records28676_28677 ++ records28677_28678
theorem aligned28676_28678 :
    AlignedValid 12 4 missing28676_28678 records28676_28678 :=
  aligned28676_28677.append aligned28677_28678

def missing28678_28679 : List (BitVec (edgeCount 12)) :=
  [missing28678]
abbrev records28678_28679 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28678]
theorem aligned28678_28679 :
    AlignedValid 12 4 missing28678_28679 records28678_28679 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28678
    maskCheck28678 AlignedValid.nil

def missing28679_28680 : List (BitVec (edgeCount 12)) :=
  [missing28679]
abbrev records28679_28680 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28679]
theorem aligned28679_28680 :
    AlignedValid 12 4 missing28679_28680 records28679_28680 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28679
    maskCheck28679 AlignedValid.nil

def missing28678_28680 : List (BitVec (edgeCount 12)) :=
  missing28678_28679 ++ missing28679_28680
abbrev records28678_28680 : List Blob :=
  records28678_28679 ++ records28679_28680
theorem aligned28678_28680 :
    AlignedValid 12 4 missing28678_28680 records28678_28680 :=
  aligned28678_28679.append aligned28679_28680

def missing28676_28680 : List (BitVec (edgeCount 12)) :=
  missing28676_28678 ++ missing28678_28680
abbrev records28676_28680 : List Blob :=
  records28676_28678 ++ records28678_28680
theorem aligned28676_28680 :
    AlignedValid 12 4 missing28676_28680 records28676_28680 :=
  aligned28676_28678.append aligned28678_28680

def missing28672_28680 : List (BitVec (edgeCount 12)) :=
  missing28672_28676 ++ missing28676_28680
abbrev records28672_28680 : List Blob :=
  records28672_28676 ++ records28676_28680
theorem aligned28672_28680 :
    AlignedValid 12 4 missing28672_28680 records28672_28680 :=
  aligned28672_28676.append aligned28676_28680

def missing28680_28681 : List (BitVec (edgeCount 12)) :=
  [missing28680]
abbrev records28680_28681 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28680]
theorem aligned28680_28681 :
    AlignedValid 12 4 missing28680_28681 records28680_28681 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28680
    maskCheck28680 AlignedValid.nil

def missing28681_28682 : List (BitVec (edgeCount 12)) :=
  [missing28681]
abbrev records28681_28682 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28681]
theorem aligned28681_28682 :
    AlignedValid 12 4 missing28681_28682 records28681_28682 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28681
    maskCheck28681 AlignedValid.nil

def missing28680_28682 : List (BitVec (edgeCount 12)) :=
  missing28680_28681 ++ missing28681_28682
abbrev records28680_28682 : List Blob :=
  records28680_28681 ++ records28681_28682
theorem aligned28680_28682 :
    AlignedValid 12 4 missing28680_28682 records28680_28682 :=
  aligned28680_28681.append aligned28681_28682

def missing28682_28683 : List (BitVec (edgeCount 12)) :=
  [missing28682]
abbrev records28682_28683 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28682]
theorem aligned28682_28683 :
    AlignedValid 12 4 missing28682_28683 records28682_28683 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28682
    maskCheck28682 AlignedValid.nil

def missing28683_28684 : List (BitVec (edgeCount 12)) :=
  [missing28683]
abbrev records28683_28684 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28683]
theorem aligned28683_28684 :
    AlignedValid 12 4 missing28683_28684 records28683_28684 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28683
    maskCheck28683 AlignedValid.nil

def missing28682_28684 : List (BitVec (edgeCount 12)) :=
  missing28682_28683 ++ missing28683_28684
abbrev records28682_28684 : List Blob :=
  records28682_28683 ++ records28683_28684
theorem aligned28682_28684 :
    AlignedValid 12 4 missing28682_28684 records28682_28684 :=
  aligned28682_28683.append aligned28683_28684

def missing28680_28684 : List (BitVec (edgeCount 12)) :=
  missing28680_28682 ++ missing28682_28684
abbrev records28680_28684 : List Blob :=
  records28680_28682 ++ records28682_28684
theorem aligned28680_28684 :
    AlignedValid 12 4 missing28680_28684 records28680_28684 :=
  aligned28680_28682.append aligned28682_28684

def missing28684_28685 : List (BitVec (edgeCount 12)) :=
  [missing28684]
abbrev records28684_28685 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28684]
theorem aligned28684_28685 :
    AlignedValid 12 4 missing28684_28685 records28684_28685 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28684
    maskCheck28684 AlignedValid.nil

def missing28685_28686 : List (BitVec (edgeCount 12)) :=
  [missing28685]
abbrev records28685_28686 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28685]
theorem aligned28685_28686 :
    AlignedValid 12 4 missing28685_28686 records28685_28686 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28685
    maskCheck28685 AlignedValid.nil

def missing28684_28686 : List (BitVec (edgeCount 12)) :=
  missing28684_28685 ++ missing28685_28686
abbrev records28684_28686 : List Blob :=
  records28684_28685 ++ records28685_28686
theorem aligned28684_28686 :
    AlignedValid 12 4 missing28684_28686 records28684_28686 :=
  aligned28684_28685.append aligned28685_28686

def missing28686_28687 : List (BitVec (edgeCount 12)) :=
  [missing28686]
abbrev records28686_28687 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28686]
theorem aligned28686_28687 :
    AlignedValid 12 4 missing28686_28687 records28686_28687 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28686
    maskCheck28686 AlignedValid.nil

def missing28687_28688 : List (BitVec (edgeCount 12)) :=
  [missing28687]
abbrev records28687_28688 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28687]
theorem aligned28687_28688 :
    AlignedValid 12 4 missing28687_28688 records28687_28688 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28687
    maskCheck28687 AlignedValid.nil

def missing28686_28688 : List (BitVec (edgeCount 12)) :=
  missing28686_28687 ++ missing28687_28688
abbrev records28686_28688 : List Blob :=
  records28686_28687 ++ records28687_28688
theorem aligned28686_28688 :
    AlignedValid 12 4 missing28686_28688 records28686_28688 :=
  aligned28686_28687.append aligned28687_28688

def missing28684_28688 : List (BitVec (edgeCount 12)) :=
  missing28684_28686 ++ missing28686_28688
abbrev records28684_28688 : List Blob :=
  records28684_28686 ++ records28686_28688
theorem aligned28684_28688 :
    AlignedValid 12 4 missing28684_28688 records28684_28688 :=
  aligned28684_28686.append aligned28686_28688

def missing28680_28688 : List (BitVec (edgeCount 12)) :=
  missing28680_28684 ++ missing28684_28688
abbrev records28680_28688 : List Blob :=
  records28680_28684 ++ records28684_28688
theorem aligned28680_28688 :
    AlignedValid 12 4 missing28680_28688 records28680_28688 :=
  aligned28680_28684.append aligned28684_28688

def missing28672_28688 : List (BitVec (edgeCount 12)) :=
  missing28672_28680 ++ missing28680_28688
abbrev records28672_28688 : List Blob :=
  records28672_28680 ++ records28680_28688
theorem aligned28672_28688 :
    AlignedValid 12 4 missing28672_28688 records28672_28688 :=
  aligned28672_28680.append aligned28680_28688

def missing28688_28689 : List (BitVec (edgeCount 12)) :=
  [missing28688]
abbrev records28688_28689 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28688]
theorem aligned28688_28689 :
    AlignedValid 12 4 missing28688_28689 records28688_28689 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28688
    maskCheck28688 AlignedValid.nil

def missing28689_28690 : List (BitVec (edgeCount 12)) :=
  [missing28689]
abbrev records28689_28690 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28689]
theorem aligned28689_28690 :
    AlignedValid 12 4 missing28689_28690 records28689_28690 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28689
    maskCheck28689 AlignedValid.nil

def missing28688_28690 : List (BitVec (edgeCount 12)) :=
  missing28688_28689 ++ missing28689_28690
abbrev records28688_28690 : List Blob :=
  records28688_28689 ++ records28689_28690
theorem aligned28688_28690 :
    AlignedValid 12 4 missing28688_28690 records28688_28690 :=
  aligned28688_28689.append aligned28689_28690

def missing28690_28691 : List (BitVec (edgeCount 12)) :=
  [missing28690]
abbrev records28690_28691 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28690]
theorem aligned28690_28691 :
    AlignedValid 12 4 missing28690_28691 records28690_28691 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28690
    maskCheck28690 AlignedValid.nil

def missing28691_28692 : List (BitVec (edgeCount 12)) :=
  [missing28691]
abbrev records28691_28692 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28691]
theorem aligned28691_28692 :
    AlignedValid 12 4 missing28691_28692 records28691_28692 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28691
    maskCheck28691 AlignedValid.nil

def missing28690_28692 : List (BitVec (edgeCount 12)) :=
  missing28690_28691 ++ missing28691_28692
abbrev records28690_28692 : List Blob :=
  records28690_28691 ++ records28691_28692
theorem aligned28690_28692 :
    AlignedValid 12 4 missing28690_28692 records28690_28692 :=
  aligned28690_28691.append aligned28691_28692

def missing28688_28692 : List (BitVec (edgeCount 12)) :=
  missing28688_28690 ++ missing28690_28692
abbrev records28688_28692 : List Blob :=
  records28688_28690 ++ records28690_28692
theorem aligned28688_28692 :
    AlignedValid 12 4 missing28688_28692 records28688_28692 :=
  aligned28688_28690.append aligned28690_28692

def missing28692_28693 : List (BitVec (edgeCount 12)) :=
  [missing28692]
abbrev records28692_28693 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28692]
theorem aligned28692_28693 :
    AlignedValid 12 4 missing28692_28693 records28692_28693 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28692
    maskCheck28692 AlignedValid.nil

def missing28693_28694 : List (BitVec (edgeCount 12)) :=
  [missing28693]
abbrev records28693_28694 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28693]
theorem aligned28693_28694 :
    AlignedValid 12 4 missing28693_28694 records28693_28694 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28693
    maskCheck28693 AlignedValid.nil

def missing28692_28694 : List (BitVec (edgeCount 12)) :=
  missing28692_28693 ++ missing28693_28694
abbrev records28692_28694 : List Blob :=
  records28692_28693 ++ records28693_28694
theorem aligned28692_28694 :
    AlignedValid 12 4 missing28692_28694 records28692_28694 :=
  aligned28692_28693.append aligned28693_28694

def missing28694_28695 : List (BitVec (edgeCount 12)) :=
  [missing28694]
abbrev records28694_28695 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28694]
theorem aligned28694_28695 :
    AlignedValid 12 4 missing28694_28695 records28694_28695 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28694
    maskCheck28694 AlignedValid.nil

def missing28695_28696 : List (BitVec (edgeCount 12)) :=
  [missing28695]
abbrev records28695_28696 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28695]
theorem aligned28695_28696 :
    AlignedValid 12 4 missing28695_28696 records28695_28696 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28695
    maskCheck28695 AlignedValid.nil

def missing28694_28696 : List (BitVec (edgeCount 12)) :=
  missing28694_28695 ++ missing28695_28696
abbrev records28694_28696 : List Blob :=
  records28694_28695 ++ records28695_28696
theorem aligned28694_28696 :
    AlignedValid 12 4 missing28694_28696 records28694_28696 :=
  aligned28694_28695.append aligned28695_28696

def missing28692_28696 : List (BitVec (edgeCount 12)) :=
  missing28692_28694 ++ missing28694_28696
abbrev records28692_28696 : List Blob :=
  records28692_28694 ++ records28694_28696
theorem aligned28692_28696 :
    AlignedValid 12 4 missing28692_28696 records28692_28696 :=
  aligned28692_28694.append aligned28694_28696

def missing28688_28696 : List (BitVec (edgeCount 12)) :=
  missing28688_28692 ++ missing28692_28696
abbrev records28688_28696 : List Blob :=
  records28688_28692 ++ records28692_28696
theorem aligned28688_28696 :
    AlignedValid 12 4 missing28688_28696 records28688_28696 :=
  aligned28688_28692.append aligned28692_28696

def missing28696_28697 : List (BitVec (edgeCount 12)) :=
  [missing28696]
abbrev records28696_28697 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28696]
theorem aligned28696_28697 :
    AlignedValid 12 4 missing28696_28697 records28696_28697 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28696
    maskCheck28696 AlignedValid.nil

def missing28697_28698 : List (BitVec (edgeCount 12)) :=
  [missing28697]
abbrev records28697_28698 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28697]
theorem aligned28697_28698 :
    AlignedValid 12 4 missing28697_28698 records28697_28698 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28697
    maskCheck28697 AlignedValid.nil

def missing28696_28698 : List (BitVec (edgeCount 12)) :=
  missing28696_28697 ++ missing28697_28698
abbrev records28696_28698 : List Blob :=
  records28696_28697 ++ records28697_28698
theorem aligned28696_28698 :
    AlignedValid 12 4 missing28696_28698 records28696_28698 :=
  aligned28696_28697.append aligned28697_28698

def missing28698_28699 : List (BitVec (edgeCount 12)) :=
  [missing28698]
abbrev records28698_28699 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28698]
theorem aligned28698_28699 :
    AlignedValid 12 4 missing28698_28699 records28698_28699 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28698
    maskCheck28698 AlignedValid.nil

def missing28699_28700 : List (BitVec (edgeCount 12)) :=
  [missing28699]
abbrev records28699_28700 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28699]
theorem aligned28699_28700 :
    AlignedValid 12 4 missing28699_28700 records28699_28700 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28699
    maskCheck28699 AlignedValid.nil

def missing28698_28700 : List (BitVec (edgeCount 12)) :=
  missing28698_28699 ++ missing28699_28700
abbrev records28698_28700 : List Blob :=
  records28698_28699 ++ records28699_28700
theorem aligned28698_28700 :
    AlignedValid 12 4 missing28698_28700 records28698_28700 :=
  aligned28698_28699.append aligned28699_28700

def missing28696_28700 : List (BitVec (edgeCount 12)) :=
  missing28696_28698 ++ missing28698_28700
abbrev records28696_28700 : List Blob :=
  records28696_28698 ++ records28698_28700
theorem aligned28696_28700 :
    AlignedValid 12 4 missing28696_28700 records28696_28700 :=
  aligned28696_28698.append aligned28698_28700

def missing28700_28701 : List (BitVec (edgeCount 12)) :=
  [missing28700]
abbrev records28700_28701 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28700]
theorem aligned28700_28701 :
    AlignedValid 12 4 missing28700_28701 records28700_28701 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28700
    maskCheck28700 AlignedValid.nil

def missing28701_28702 : List (BitVec (edgeCount 12)) :=
  [missing28701]
abbrev records28701_28702 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28701]
theorem aligned28701_28702 :
    AlignedValid 12 4 missing28701_28702 records28701_28702 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28701
    maskCheck28701 AlignedValid.nil

def missing28700_28702 : List (BitVec (edgeCount 12)) :=
  missing28700_28701 ++ missing28701_28702
abbrev records28700_28702 : List Blob :=
  records28700_28701 ++ records28701_28702
theorem aligned28700_28702 :
    AlignedValid 12 4 missing28700_28702 records28700_28702 :=
  aligned28700_28701.append aligned28701_28702

def missing28702_28703 : List (BitVec (edgeCount 12)) :=
  [missing28702]
abbrev records28702_28703 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28702]
theorem aligned28702_28703 :
    AlignedValid 12 4 missing28702_28703 records28702_28703 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28702
    maskCheck28702 AlignedValid.nil

def missing28703_28704 : List (BitVec (edgeCount 12)) :=
  [missing28703]
abbrev records28703_28704 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28703]
theorem aligned28703_28704 :
    AlignedValid 12 4 missing28703_28704 records28703_28704 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28703
    maskCheck28703 AlignedValid.nil

def missing28702_28704 : List (BitVec (edgeCount 12)) :=
  missing28702_28703 ++ missing28703_28704
abbrev records28702_28704 : List Blob :=
  records28702_28703 ++ records28703_28704
theorem aligned28702_28704 :
    AlignedValid 12 4 missing28702_28704 records28702_28704 :=
  aligned28702_28703.append aligned28703_28704

def missing28700_28704 : List (BitVec (edgeCount 12)) :=
  missing28700_28702 ++ missing28702_28704
abbrev records28700_28704 : List Blob :=
  records28700_28702 ++ records28702_28704
theorem aligned28700_28704 :
    AlignedValid 12 4 missing28700_28704 records28700_28704 :=
  aligned28700_28702.append aligned28702_28704

def missing28696_28704 : List (BitVec (edgeCount 12)) :=
  missing28696_28700 ++ missing28700_28704
abbrev records28696_28704 : List Blob :=
  records28696_28700 ++ records28700_28704
theorem aligned28696_28704 :
    AlignedValid 12 4 missing28696_28704 records28696_28704 :=
  aligned28696_28700.append aligned28700_28704

def missing28688_28704 : List (BitVec (edgeCount 12)) :=
  missing28688_28696 ++ missing28696_28704
abbrev records28688_28704 : List Blob :=
  records28688_28696 ++ records28696_28704
theorem aligned28688_28704 :
    AlignedValid 12 4 missing28688_28704 records28688_28704 :=
  aligned28688_28696.append aligned28696_28704

def missing28672_28704 : List (BitVec (edgeCount 12)) :=
  missing28672_28688 ++ missing28688_28704
abbrev records28672_28704 : List Blob :=
  records28672_28688 ++ records28688_28704
theorem aligned28672_28704 :
    AlignedValid 12 4 missing28672_28704 records28672_28704 :=
  aligned28672_28688.append aligned28688_28704

def missing28704_28705 : List (BitVec (edgeCount 12)) :=
  [missing28704]
abbrev records28704_28705 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28704]
theorem aligned28704_28705 :
    AlignedValid 12 4 missing28704_28705 records28704_28705 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28704
    maskCheck28704 AlignedValid.nil

def missing28705_28706 : List (BitVec (edgeCount 12)) :=
  [missing28705]
abbrev records28705_28706 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28705]
theorem aligned28705_28706 :
    AlignedValid 12 4 missing28705_28706 records28705_28706 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28705
    maskCheck28705 AlignedValid.nil

def missing28704_28706 : List (BitVec (edgeCount 12)) :=
  missing28704_28705 ++ missing28705_28706
abbrev records28704_28706 : List Blob :=
  records28704_28705 ++ records28705_28706
theorem aligned28704_28706 :
    AlignedValid 12 4 missing28704_28706 records28704_28706 :=
  aligned28704_28705.append aligned28705_28706

def missing28706_28707 : List (BitVec (edgeCount 12)) :=
  [missing28706]
abbrev records28706_28707 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28706]
theorem aligned28706_28707 :
    AlignedValid 12 4 missing28706_28707 records28706_28707 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28706
    maskCheck28706 AlignedValid.nil

def missing28707_28708 : List (BitVec (edgeCount 12)) :=
  [missing28707]
abbrev records28707_28708 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28707]
theorem aligned28707_28708 :
    AlignedValid 12 4 missing28707_28708 records28707_28708 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28707
    maskCheck28707 AlignedValid.nil

def missing28706_28708 : List (BitVec (edgeCount 12)) :=
  missing28706_28707 ++ missing28707_28708
abbrev records28706_28708 : List Blob :=
  records28706_28707 ++ records28707_28708
theorem aligned28706_28708 :
    AlignedValid 12 4 missing28706_28708 records28706_28708 :=
  aligned28706_28707.append aligned28707_28708

def missing28704_28708 : List (BitVec (edgeCount 12)) :=
  missing28704_28706 ++ missing28706_28708
abbrev records28704_28708 : List Blob :=
  records28704_28706 ++ records28706_28708
theorem aligned28704_28708 :
    AlignedValid 12 4 missing28704_28708 records28704_28708 :=
  aligned28704_28706.append aligned28706_28708

def missing28708_28709 : List (BitVec (edgeCount 12)) :=
  [missing28708]
abbrev records28708_28709 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28708]
theorem aligned28708_28709 :
    AlignedValid 12 4 missing28708_28709 records28708_28709 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28708
    maskCheck28708 AlignedValid.nil

def missing28709_28710 : List (BitVec (edgeCount 12)) :=
  [missing28709]
abbrev records28709_28710 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28709]
theorem aligned28709_28710 :
    AlignedValid 12 4 missing28709_28710 records28709_28710 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28709
    maskCheck28709 AlignedValid.nil

def missing28708_28710 : List (BitVec (edgeCount 12)) :=
  missing28708_28709 ++ missing28709_28710
abbrev records28708_28710 : List Blob :=
  records28708_28709 ++ records28709_28710
theorem aligned28708_28710 :
    AlignedValid 12 4 missing28708_28710 records28708_28710 :=
  aligned28708_28709.append aligned28709_28710

def missing28710_28711 : List (BitVec (edgeCount 12)) :=
  [missing28710]
abbrev records28710_28711 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28710]
theorem aligned28710_28711 :
    AlignedValid 12 4 missing28710_28711 records28710_28711 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28710
    maskCheck28710 AlignedValid.nil

def missing28711_28712 : List (BitVec (edgeCount 12)) :=
  [missing28711]
abbrev records28711_28712 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28711]
theorem aligned28711_28712 :
    AlignedValid 12 4 missing28711_28712 records28711_28712 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28711
    maskCheck28711 AlignedValid.nil

def missing28710_28712 : List (BitVec (edgeCount 12)) :=
  missing28710_28711 ++ missing28711_28712
abbrev records28710_28712 : List Blob :=
  records28710_28711 ++ records28711_28712
theorem aligned28710_28712 :
    AlignedValid 12 4 missing28710_28712 records28710_28712 :=
  aligned28710_28711.append aligned28711_28712

def missing28708_28712 : List (BitVec (edgeCount 12)) :=
  missing28708_28710 ++ missing28710_28712
abbrev records28708_28712 : List Blob :=
  records28708_28710 ++ records28710_28712
theorem aligned28708_28712 :
    AlignedValid 12 4 missing28708_28712 records28708_28712 :=
  aligned28708_28710.append aligned28710_28712

def missing28704_28712 : List (BitVec (edgeCount 12)) :=
  missing28704_28708 ++ missing28708_28712
abbrev records28704_28712 : List Blob :=
  records28704_28708 ++ records28708_28712
theorem aligned28704_28712 :
    AlignedValid 12 4 missing28704_28712 records28704_28712 :=
  aligned28704_28708.append aligned28708_28712

def missing28712_28713 : List (BitVec (edgeCount 12)) :=
  [missing28712]
abbrev records28712_28713 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28712]
theorem aligned28712_28713 :
    AlignedValid 12 4 missing28712_28713 records28712_28713 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28712
    maskCheck28712 AlignedValid.nil

def missing28713_28714 : List (BitVec (edgeCount 12)) :=
  [missing28713]
abbrev records28713_28714 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28713]
theorem aligned28713_28714 :
    AlignedValid 12 4 missing28713_28714 records28713_28714 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28713
    maskCheck28713 AlignedValid.nil

def missing28712_28714 : List (BitVec (edgeCount 12)) :=
  missing28712_28713 ++ missing28713_28714
abbrev records28712_28714 : List Blob :=
  records28712_28713 ++ records28713_28714
theorem aligned28712_28714 :
    AlignedValid 12 4 missing28712_28714 records28712_28714 :=
  aligned28712_28713.append aligned28713_28714

def missing28714_28715 : List (BitVec (edgeCount 12)) :=
  [missing28714]
abbrev records28714_28715 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28714]
theorem aligned28714_28715 :
    AlignedValid 12 4 missing28714_28715 records28714_28715 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28714
    maskCheck28714 AlignedValid.nil

def missing28715_28716 : List (BitVec (edgeCount 12)) :=
  [missing28715]
abbrev records28715_28716 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28715]
theorem aligned28715_28716 :
    AlignedValid 12 4 missing28715_28716 records28715_28716 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28715
    maskCheck28715 AlignedValid.nil

def missing28714_28716 : List (BitVec (edgeCount 12)) :=
  missing28714_28715 ++ missing28715_28716
abbrev records28714_28716 : List Blob :=
  records28714_28715 ++ records28715_28716
theorem aligned28714_28716 :
    AlignedValid 12 4 missing28714_28716 records28714_28716 :=
  aligned28714_28715.append aligned28715_28716

def missing28712_28716 : List (BitVec (edgeCount 12)) :=
  missing28712_28714 ++ missing28714_28716
abbrev records28712_28716 : List Blob :=
  records28712_28714 ++ records28714_28716
theorem aligned28712_28716 :
    AlignedValid 12 4 missing28712_28716 records28712_28716 :=
  aligned28712_28714.append aligned28714_28716

def missing28716_28717 : List (BitVec (edgeCount 12)) :=
  [missing28716]
abbrev records28716_28717 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28716]
theorem aligned28716_28717 :
    AlignedValid 12 4 missing28716_28717 records28716_28717 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28716
    maskCheck28716 AlignedValid.nil

def missing28717_28718 : List (BitVec (edgeCount 12)) :=
  [missing28717]
abbrev records28717_28718 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28717]
theorem aligned28717_28718 :
    AlignedValid 12 4 missing28717_28718 records28717_28718 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28717
    maskCheck28717 AlignedValid.nil

def missing28716_28718 : List (BitVec (edgeCount 12)) :=
  missing28716_28717 ++ missing28717_28718
abbrev records28716_28718 : List Blob :=
  records28716_28717 ++ records28717_28718
theorem aligned28716_28718 :
    AlignedValid 12 4 missing28716_28718 records28716_28718 :=
  aligned28716_28717.append aligned28717_28718

def missing28718_28719 : List (BitVec (edgeCount 12)) :=
  [missing28718]
abbrev records28718_28719 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28718]
theorem aligned28718_28719 :
    AlignedValid 12 4 missing28718_28719 records28718_28719 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28718
    maskCheck28718 AlignedValid.nil

def missing28719_28720 : List (BitVec (edgeCount 12)) :=
  [missing28719]
abbrev records28719_28720 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28719]
theorem aligned28719_28720 :
    AlignedValid 12 4 missing28719_28720 records28719_28720 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28719
    maskCheck28719 AlignedValid.nil

def missing28718_28720 : List (BitVec (edgeCount 12)) :=
  missing28718_28719 ++ missing28719_28720
abbrev records28718_28720 : List Blob :=
  records28718_28719 ++ records28719_28720
theorem aligned28718_28720 :
    AlignedValid 12 4 missing28718_28720 records28718_28720 :=
  aligned28718_28719.append aligned28719_28720

def missing28716_28720 : List (BitVec (edgeCount 12)) :=
  missing28716_28718 ++ missing28718_28720
abbrev records28716_28720 : List Blob :=
  records28716_28718 ++ records28718_28720
theorem aligned28716_28720 :
    AlignedValid 12 4 missing28716_28720 records28716_28720 :=
  aligned28716_28718.append aligned28718_28720

def missing28712_28720 : List (BitVec (edgeCount 12)) :=
  missing28712_28716 ++ missing28716_28720
abbrev records28712_28720 : List Blob :=
  records28712_28716 ++ records28716_28720
theorem aligned28712_28720 :
    AlignedValid 12 4 missing28712_28720 records28712_28720 :=
  aligned28712_28716.append aligned28716_28720

def missing28704_28720 : List (BitVec (edgeCount 12)) :=
  missing28704_28712 ++ missing28712_28720
abbrev records28704_28720 : List Blob :=
  records28704_28712 ++ records28712_28720
theorem aligned28704_28720 :
    AlignedValid 12 4 missing28704_28720 records28704_28720 :=
  aligned28704_28712.append aligned28712_28720

def missing28720_28721 : List (BitVec (edgeCount 12)) :=
  [missing28720]
abbrev records28720_28721 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28720]
theorem aligned28720_28721 :
    AlignedValid 12 4 missing28720_28721 records28720_28721 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28720
    maskCheck28720 AlignedValid.nil

def missing28721_28722 : List (BitVec (edgeCount 12)) :=
  [missing28721]
abbrev records28721_28722 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28721]
theorem aligned28721_28722 :
    AlignedValid 12 4 missing28721_28722 records28721_28722 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28721
    maskCheck28721 AlignedValid.nil

def missing28720_28722 : List (BitVec (edgeCount 12)) :=
  missing28720_28721 ++ missing28721_28722
abbrev records28720_28722 : List Blob :=
  records28720_28721 ++ records28721_28722
theorem aligned28720_28722 :
    AlignedValid 12 4 missing28720_28722 records28720_28722 :=
  aligned28720_28721.append aligned28721_28722

def missing28722_28723 : List (BitVec (edgeCount 12)) :=
  [missing28722]
abbrev records28722_28723 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28722]
theorem aligned28722_28723 :
    AlignedValid 12 4 missing28722_28723 records28722_28723 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28722
    maskCheck28722 AlignedValid.nil

def missing28723_28724 : List (BitVec (edgeCount 12)) :=
  [missing28723]
abbrev records28723_28724 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28723]
theorem aligned28723_28724 :
    AlignedValid 12 4 missing28723_28724 records28723_28724 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28723
    maskCheck28723 AlignedValid.nil

def missing28722_28724 : List (BitVec (edgeCount 12)) :=
  missing28722_28723 ++ missing28723_28724
abbrev records28722_28724 : List Blob :=
  records28722_28723 ++ records28723_28724
theorem aligned28722_28724 :
    AlignedValid 12 4 missing28722_28724 records28722_28724 :=
  aligned28722_28723.append aligned28723_28724

def missing28720_28724 : List (BitVec (edgeCount 12)) :=
  missing28720_28722 ++ missing28722_28724
abbrev records28720_28724 : List Blob :=
  records28720_28722 ++ records28722_28724
theorem aligned28720_28724 :
    AlignedValid 12 4 missing28720_28724 records28720_28724 :=
  aligned28720_28722.append aligned28722_28724

def missing28724_28725 : List (BitVec (edgeCount 12)) :=
  [missing28724]
abbrev records28724_28725 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28724]
theorem aligned28724_28725 :
    AlignedValid 12 4 missing28724_28725 records28724_28725 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28724
    maskCheck28724 AlignedValid.nil

def missing28725_28726 : List (BitVec (edgeCount 12)) :=
  [missing28725]
abbrev records28725_28726 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28725]
theorem aligned28725_28726 :
    AlignedValid 12 4 missing28725_28726 records28725_28726 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28725
    maskCheck28725 AlignedValid.nil

def missing28724_28726 : List (BitVec (edgeCount 12)) :=
  missing28724_28725 ++ missing28725_28726
abbrev records28724_28726 : List Blob :=
  records28724_28725 ++ records28725_28726
theorem aligned28724_28726 :
    AlignedValid 12 4 missing28724_28726 records28724_28726 :=
  aligned28724_28725.append aligned28725_28726

def missing28726_28727 : List (BitVec (edgeCount 12)) :=
  [missing28726]
abbrev records28726_28727 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28726]
theorem aligned28726_28727 :
    AlignedValid 12 4 missing28726_28727 records28726_28727 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28726
    maskCheck28726 AlignedValid.nil

def missing28727_28728 : List (BitVec (edgeCount 12)) :=
  [missing28727]
abbrev records28727_28728 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28727]
theorem aligned28727_28728 :
    AlignedValid 12 4 missing28727_28728 records28727_28728 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28727
    maskCheck28727 AlignedValid.nil

def missing28726_28728 : List (BitVec (edgeCount 12)) :=
  missing28726_28727 ++ missing28727_28728
abbrev records28726_28728 : List Blob :=
  records28726_28727 ++ records28727_28728
theorem aligned28726_28728 :
    AlignedValid 12 4 missing28726_28728 records28726_28728 :=
  aligned28726_28727.append aligned28727_28728

def missing28724_28728 : List (BitVec (edgeCount 12)) :=
  missing28724_28726 ++ missing28726_28728
abbrev records28724_28728 : List Blob :=
  records28724_28726 ++ records28726_28728
theorem aligned28724_28728 :
    AlignedValid 12 4 missing28724_28728 records28724_28728 :=
  aligned28724_28726.append aligned28726_28728

def missing28720_28728 : List (BitVec (edgeCount 12)) :=
  missing28720_28724 ++ missing28724_28728
abbrev records28720_28728 : List Blob :=
  records28720_28724 ++ records28724_28728
theorem aligned28720_28728 :
    AlignedValid 12 4 missing28720_28728 records28720_28728 :=
  aligned28720_28724.append aligned28724_28728

def missing28728_28729 : List (BitVec (edgeCount 12)) :=
  [missing28728]
abbrev records28728_28729 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28728]
theorem aligned28728_28729 :
    AlignedValid 12 4 missing28728_28729 records28728_28729 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28728
    maskCheck28728 AlignedValid.nil

def missing28729_28730 : List (BitVec (edgeCount 12)) :=
  [missing28729]
abbrev records28729_28730 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28729]
theorem aligned28729_28730 :
    AlignedValid 12 4 missing28729_28730 records28729_28730 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28729
    maskCheck28729 AlignedValid.nil

def missing28728_28730 : List (BitVec (edgeCount 12)) :=
  missing28728_28729 ++ missing28729_28730
abbrev records28728_28730 : List Blob :=
  records28728_28729 ++ records28729_28730
theorem aligned28728_28730 :
    AlignedValid 12 4 missing28728_28730 records28728_28730 :=
  aligned28728_28729.append aligned28729_28730

def missing28730_28731 : List (BitVec (edgeCount 12)) :=
  [missing28730]
abbrev records28730_28731 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28730]
theorem aligned28730_28731 :
    AlignedValid 12 4 missing28730_28731 records28730_28731 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28730
    maskCheck28730 AlignedValid.nil

def missing28731_28732 : List (BitVec (edgeCount 12)) :=
  [missing28731]
abbrev records28731_28732 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28731]
theorem aligned28731_28732 :
    AlignedValid 12 4 missing28731_28732 records28731_28732 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28731
    maskCheck28731 AlignedValid.nil

def missing28730_28732 : List (BitVec (edgeCount 12)) :=
  missing28730_28731 ++ missing28731_28732
abbrev records28730_28732 : List Blob :=
  records28730_28731 ++ records28731_28732
theorem aligned28730_28732 :
    AlignedValid 12 4 missing28730_28732 records28730_28732 :=
  aligned28730_28731.append aligned28731_28732

def missing28728_28732 : List (BitVec (edgeCount 12)) :=
  missing28728_28730 ++ missing28730_28732
abbrev records28728_28732 : List Blob :=
  records28728_28730 ++ records28730_28732
theorem aligned28728_28732 :
    AlignedValid 12 4 missing28728_28732 records28728_28732 :=
  aligned28728_28730.append aligned28730_28732

def missing28732_28733 : List (BitVec (edgeCount 12)) :=
  [missing28732]
abbrev records28732_28733 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28732]
theorem aligned28732_28733 :
    AlignedValid 12 4 missing28732_28733 records28732_28733 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28732
    maskCheck28732 AlignedValid.nil

def missing28733_28734 : List (BitVec (edgeCount 12)) :=
  [missing28733]
abbrev records28733_28734 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28733]
theorem aligned28733_28734 :
    AlignedValid 12 4 missing28733_28734 records28733_28734 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28733
    maskCheck28733 AlignedValid.nil

def missing28732_28734 : List (BitVec (edgeCount 12)) :=
  missing28732_28733 ++ missing28733_28734
abbrev records28732_28734 : List Blob :=
  records28732_28733 ++ records28733_28734
theorem aligned28732_28734 :
    AlignedValid 12 4 missing28732_28734 records28732_28734 :=
  aligned28732_28733.append aligned28733_28734

def missing28734_28735 : List (BitVec (edgeCount 12)) :=
  [missing28734]
abbrev records28734_28735 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28734]
theorem aligned28734_28735 :
    AlignedValid 12 4 missing28734_28735 records28734_28735 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28734
    maskCheck28734 AlignedValid.nil

def missing28735_28736 : List (BitVec (edgeCount 12)) :=
  [missing28735]
abbrev records28735_28736 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28735]
theorem aligned28735_28736 :
    AlignedValid 12 4 missing28735_28736 records28735_28736 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28735
    maskCheck28735 AlignedValid.nil

def missing28734_28736 : List (BitVec (edgeCount 12)) :=
  missing28734_28735 ++ missing28735_28736
abbrev records28734_28736 : List Blob :=
  records28734_28735 ++ records28735_28736
theorem aligned28734_28736 :
    AlignedValid 12 4 missing28734_28736 records28734_28736 :=
  aligned28734_28735.append aligned28735_28736

def missing28732_28736 : List (BitVec (edgeCount 12)) :=
  missing28732_28734 ++ missing28734_28736
abbrev records28732_28736 : List Blob :=
  records28732_28734 ++ records28734_28736
theorem aligned28732_28736 :
    AlignedValid 12 4 missing28732_28736 records28732_28736 :=
  aligned28732_28734.append aligned28734_28736

def missing28728_28736 : List (BitVec (edgeCount 12)) :=
  missing28728_28732 ++ missing28732_28736
abbrev records28728_28736 : List Blob :=
  records28728_28732 ++ records28732_28736
theorem aligned28728_28736 :
    AlignedValid 12 4 missing28728_28736 records28728_28736 :=
  aligned28728_28732.append aligned28732_28736

def missing28720_28736 : List (BitVec (edgeCount 12)) :=
  missing28720_28728 ++ missing28728_28736
abbrev records28720_28736 : List Blob :=
  records28720_28728 ++ records28728_28736
theorem aligned28720_28736 :
    AlignedValid 12 4 missing28720_28736 records28720_28736 :=
  aligned28720_28728.append aligned28728_28736

def missing28704_28736 : List (BitVec (edgeCount 12)) :=
  missing28704_28720 ++ missing28720_28736
abbrev records28704_28736 : List Blob :=
  records28704_28720 ++ records28720_28736
theorem aligned28704_28736 :
    AlignedValid 12 4 missing28704_28736 records28704_28736 :=
  aligned28704_28720.append aligned28720_28736

def missing28672_28736 : List (BitVec (edgeCount 12)) :=
  missing28672_28704 ++ missing28704_28736
abbrev records28672_28736 : List Blob :=
  records28672_28704 ++ records28704_28736
theorem aligned28672_28736 :
    AlignedValid 12 4 missing28672_28736 records28672_28736 :=
  aligned28672_28704.append aligned28704_28736

def missing28736_28737 : List (BitVec (edgeCount 12)) :=
  [missing28736]
abbrev records28736_28737 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28736]
theorem aligned28736_28737 :
    AlignedValid 12 4 missing28736_28737 records28736_28737 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28736
    maskCheck28736 AlignedValid.nil

def missing28737_28738 : List (BitVec (edgeCount 12)) :=
  [missing28737]
abbrev records28737_28738 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28737]
theorem aligned28737_28738 :
    AlignedValid 12 4 missing28737_28738 records28737_28738 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28737
    maskCheck28737 AlignedValid.nil

def missing28736_28738 : List (BitVec (edgeCount 12)) :=
  missing28736_28737 ++ missing28737_28738
abbrev records28736_28738 : List Blob :=
  records28736_28737 ++ records28737_28738
theorem aligned28736_28738 :
    AlignedValid 12 4 missing28736_28738 records28736_28738 :=
  aligned28736_28737.append aligned28737_28738

def missing28738_28739 : List (BitVec (edgeCount 12)) :=
  [missing28738]
abbrev records28738_28739 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28738]
theorem aligned28738_28739 :
    AlignedValid 12 4 missing28738_28739 records28738_28739 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28738
    maskCheck28738 AlignedValid.nil

def missing28739_28740 : List (BitVec (edgeCount 12)) :=
  [missing28739]
abbrev records28739_28740 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28739]
theorem aligned28739_28740 :
    AlignedValid 12 4 missing28739_28740 records28739_28740 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28739
    maskCheck28739 AlignedValid.nil

def missing28738_28740 : List (BitVec (edgeCount 12)) :=
  missing28738_28739 ++ missing28739_28740
abbrev records28738_28740 : List Blob :=
  records28738_28739 ++ records28739_28740
theorem aligned28738_28740 :
    AlignedValid 12 4 missing28738_28740 records28738_28740 :=
  aligned28738_28739.append aligned28739_28740

def missing28736_28740 : List (BitVec (edgeCount 12)) :=
  missing28736_28738 ++ missing28738_28740
abbrev records28736_28740 : List Blob :=
  records28736_28738 ++ records28738_28740
theorem aligned28736_28740 :
    AlignedValid 12 4 missing28736_28740 records28736_28740 :=
  aligned28736_28738.append aligned28738_28740

def missing28740_28741 : List (BitVec (edgeCount 12)) :=
  [missing28740]
abbrev records28740_28741 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28740]
theorem aligned28740_28741 :
    AlignedValid 12 4 missing28740_28741 records28740_28741 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28740
    maskCheck28740 AlignedValid.nil

def missing28741_28742 : List (BitVec (edgeCount 12)) :=
  [missing28741]
abbrev records28741_28742 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28741]
theorem aligned28741_28742 :
    AlignedValid 12 4 missing28741_28742 records28741_28742 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28741
    maskCheck28741 AlignedValid.nil

def missing28740_28742 : List (BitVec (edgeCount 12)) :=
  missing28740_28741 ++ missing28741_28742
abbrev records28740_28742 : List Blob :=
  records28740_28741 ++ records28741_28742
theorem aligned28740_28742 :
    AlignedValid 12 4 missing28740_28742 records28740_28742 :=
  aligned28740_28741.append aligned28741_28742

def missing28742_28743 : List (BitVec (edgeCount 12)) :=
  [missing28742]
abbrev records28742_28743 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28742]
theorem aligned28742_28743 :
    AlignedValid 12 4 missing28742_28743 records28742_28743 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28742
    maskCheck28742 AlignedValid.nil

def missing28743_28744 : List (BitVec (edgeCount 12)) :=
  [missing28743]
abbrev records28743_28744 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28743]
theorem aligned28743_28744 :
    AlignedValid 12 4 missing28743_28744 records28743_28744 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28743
    maskCheck28743 AlignedValid.nil

def missing28742_28744 : List (BitVec (edgeCount 12)) :=
  missing28742_28743 ++ missing28743_28744
abbrev records28742_28744 : List Blob :=
  records28742_28743 ++ records28743_28744
theorem aligned28742_28744 :
    AlignedValid 12 4 missing28742_28744 records28742_28744 :=
  aligned28742_28743.append aligned28743_28744

def missing28740_28744 : List (BitVec (edgeCount 12)) :=
  missing28740_28742 ++ missing28742_28744
abbrev records28740_28744 : List Blob :=
  records28740_28742 ++ records28742_28744
theorem aligned28740_28744 :
    AlignedValid 12 4 missing28740_28744 records28740_28744 :=
  aligned28740_28742.append aligned28742_28744

def missing28736_28744 : List (BitVec (edgeCount 12)) :=
  missing28736_28740 ++ missing28740_28744
abbrev records28736_28744 : List Blob :=
  records28736_28740 ++ records28740_28744
theorem aligned28736_28744 :
    AlignedValid 12 4 missing28736_28744 records28736_28744 :=
  aligned28736_28740.append aligned28740_28744

def missing28744_28745 : List (BitVec (edgeCount 12)) :=
  [missing28744]
abbrev records28744_28745 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28744]
theorem aligned28744_28745 :
    AlignedValid 12 4 missing28744_28745 records28744_28745 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28744
    maskCheck28744 AlignedValid.nil

def missing28745_28746 : List (BitVec (edgeCount 12)) :=
  [missing28745]
abbrev records28745_28746 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28745]
theorem aligned28745_28746 :
    AlignedValid 12 4 missing28745_28746 records28745_28746 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28745
    maskCheck28745 AlignedValid.nil

def missing28744_28746 : List (BitVec (edgeCount 12)) :=
  missing28744_28745 ++ missing28745_28746
abbrev records28744_28746 : List Blob :=
  records28744_28745 ++ records28745_28746
theorem aligned28744_28746 :
    AlignedValid 12 4 missing28744_28746 records28744_28746 :=
  aligned28744_28745.append aligned28745_28746

def missing28746_28747 : List (BitVec (edgeCount 12)) :=
  [missing28746]
abbrev records28746_28747 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28746]
theorem aligned28746_28747 :
    AlignedValid 12 4 missing28746_28747 records28746_28747 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28746
    maskCheck28746 AlignedValid.nil

def missing28747_28748 : List (BitVec (edgeCount 12)) :=
  [missing28747]
abbrev records28747_28748 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28747]
theorem aligned28747_28748 :
    AlignedValid 12 4 missing28747_28748 records28747_28748 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28747
    maskCheck28747 AlignedValid.nil

def missing28746_28748 : List (BitVec (edgeCount 12)) :=
  missing28746_28747 ++ missing28747_28748
abbrev records28746_28748 : List Blob :=
  records28746_28747 ++ records28747_28748
theorem aligned28746_28748 :
    AlignedValid 12 4 missing28746_28748 records28746_28748 :=
  aligned28746_28747.append aligned28747_28748

def missing28744_28748 : List (BitVec (edgeCount 12)) :=
  missing28744_28746 ++ missing28746_28748
abbrev records28744_28748 : List Blob :=
  records28744_28746 ++ records28746_28748
theorem aligned28744_28748 :
    AlignedValid 12 4 missing28744_28748 records28744_28748 :=
  aligned28744_28746.append aligned28746_28748

def missing28748_28749 : List (BitVec (edgeCount 12)) :=
  [missing28748]
abbrev records28748_28749 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28748]
theorem aligned28748_28749 :
    AlignedValid 12 4 missing28748_28749 records28748_28749 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28748
    maskCheck28748 AlignedValid.nil

def missing28749_28750 : List (BitVec (edgeCount 12)) :=
  [missing28749]
abbrev records28749_28750 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28749]
theorem aligned28749_28750 :
    AlignedValid 12 4 missing28749_28750 records28749_28750 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28749
    maskCheck28749 AlignedValid.nil

def missing28748_28750 : List (BitVec (edgeCount 12)) :=
  missing28748_28749 ++ missing28749_28750
abbrev records28748_28750 : List Blob :=
  records28748_28749 ++ records28749_28750
theorem aligned28748_28750 :
    AlignedValid 12 4 missing28748_28750 records28748_28750 :=
  aligned28748_28749.append aligned28749_28750

def missing28750_28751 : List (BitVec (edgeCount 12)) :=
  [missing28750]
abbrev records28750_28751 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28750]
theorem aligned28750_28751 :
    AlignedValid 12 4 missing28750_28751 records28750_28751 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28750
    maskCheck28750 AlignedValid.nil

def missing28751_28752 : List (BitVec (edgeCount 12)) :=
  [missing28751]
abbrev records28751_28752 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28751]
theorem aligned28751_28752 :
    AlignedValid 12 4 missing28751_28752 records28751_28752 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28751
    maskCheck28751 AlignedValid.nil

def missing28750_28752 : List (BitVec (edgeCount 12)) :=
  missing28750_28751 ++ missing28751_28752
abbrev records28750_28752 : List Blob :=
  records28750_28751 ++ records28751_28752
theorem aligned28750_28752 :
    AlignedValid 12 4 missing28750_28752 records28750_28752 :=
  aligned28750_28751.append aligned28751_28752

def missing28748_28752 : List (BitVec (edgeCount 12)) :=
  missing28748_28750 ++ missing28750_28752
abbrev records28748_28752 : List Blob :=
  records28748_28750 ++ records28750_28752
theorem aligned28748_28752 :
    AlignedValid 12 4 missing28748_28752 records28748_28752 :=
  aligned28748_28750.append aligned28750_28752

def missing28744_28752 : List (BitVec (edgeCount 12)) :=
  missing28744_28748 ++ missing28748_28752
abbrev records28744_28752 : List Blob :=
  records28744_28748 ++ records28748_28752
theorem aligned28744_28752 :
    AlignedValid 12 4 missing28744_28752 records28744_28752 :=
  aligned28744_28748.append aligned28748_28752

def missing28736_28752 : List (BitVec (edgeCount 12)) :=
  missing28736_28744 ++ missing28744_28752
abbrev records28736_28752 : List Blob :=
  records28736_28744 ++ records28744_28752
theorem aligned28736_28752 :
    AlignedValid 12 4 missing28736_28752 records28736_28752 :=
  aligned28736_28744.append aligned28744_28752

def missing28752_28753 : List (BitVec (edgeCount 12)) :=
  [missing28752]
abbrev records28752_28753 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28752]
theorem aligned28752_28753 :
    AlignedValid 12 4 missing28752_28753 records28752_28753 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28752
    maskCheck28752 AlignedValid.nil

def missing28753_28754 : List (BitVec (edgeCount 12)) :=
  [missing28753]
abbrev records28753_28754 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28753]
theorem aligned28753_28754 :
    AlignedValid 12 4 missing28753_28754 records28753_28754 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28753
    maskCheck28753 AlignedValid.nil

def missing28752_28754 : List (BitVec (edgeCount 12)) :=
  missing28752_28753 ++ missing28753_28754
abbrev records28752_28754 : List Blob :=
  records28752_28753 ++ records28753_28754
theorem aligned28752_28754 :
    AlignedValid 12 4 missing28752_28754 records28752_28754 :=
  aligned28752_28753.append aligned28753_28754

def missing28754_28755 : List (BitVec (edgeCount 12)) :=
  [missing28754]
abbrev records28754_28755 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28754]
theorem aligned28754_28755 :
    AlignedValid 12 4 missing28754_28755 records28754_28755 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28754
    maskCheck28754 AlignedValid.nil

def missing28755_28756 : List (BitVec (edgeCount 12)) :=
  [missing28755]
abbrev records28755_28756 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28755]
theorem aligned28755_28756 :
    AlignedValid 12 4 missing28755_28756 records28755_28756 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28755
    maskCheck28755 AlignedValid.nil

def missing28754_28756 : List (BitVec (edgeCount 12)) :=
  missing28754_28755 ++ missing28755_28756
abbrev records28754_28756 : List Blob :=
  records28754_28755 ++ records28755_28756
theorem aligned28754_28756 :
    AlignedValid 12 4 missing28754_28756 records28754_28756 :=
  aligned28754_28755.append aligned28755_28756

def missing28752_28756 : List (BitVec (edgeCount 12)) :=
  missing28752_28754 ++ missing28754_28756
abbrev records28752_28756 : List Blob :=
  records28752_28754 ++ records28754_28756
theorem aligned28752_28756 :
    AlignedValid 12 4 missing28752_28756 records28752_28756 :=
  aligned28752_28754.append aligned28754_28756

def missing28756_28757 : List (BitVec (edgeCount 12)) :=
  [missing28756]
abbrev records28756_28757 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28756]
theorem aligned28756_28757 :
    AlignedValid 12 4 missing28756_28757 records28756_28757 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28756
    maskCheck28756 AlignedValid.nil

def missing28757_28758 : List (BitVec (edgeCount 12)) :=
  [missing28757]
abbrev records28757_28758 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28757]
theorem aligned28757_28758 :
    AlignedValid 12 4 missing28757_28758 records28757_28758 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28757
    maskCheck28757 AlignedValid.nil

def missing28756_28758 : List (BitVec (edgeCount 12)) :=
  missing28756_28757 ++ missing28757_28758
abbrev records28756_28758 : List Blob :=
  records28756_28757 ++ records28757_28758
theorem aligned28756_28758 :
    AlignedValid 12 4 missing28756_28758 records28756_28758 :=
  aligned28756_28757.append aligned28757_28758

def missing28758_28759 : List (BitVec (edgeCount 12)) :=
  [missing28758]
abbrev records28758_28759 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28758]
theorem aligned28758_28759 :
    AlignedValid 12 4 missing28758_28759 records28758_28759 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28758
    maskCheck28758 AlignedValid.nil

def missing28759_28760 : List (BitVec (edgeCount 12)) :=
  [missing28759]
abbrev records28759_28760 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28759]
theorem aligned28759_28760 :
    AlignedValid 12 4 missing28759_28760 records28759_28760 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28759
    maskCheck28759 AlignedValid.nil

def missing28758_28760 : List (BitVec (edgeCount 12)) :=
  missing28758_28759 ++ missing28759_28760
abbrev records28758_28760 : List Blob :=
  records28758_28759 ++ records28759_28760
theorem aligned28758_28760 :
    AlignedValid 12 4 missing28758_28760 records28758_28760 :=
  aligned28758_28759.append aligned28759_28760

def missing28756_28760 : List (BitVec (edgeCount 12)) :=
  missing28756_28758 ++ missing28758_28760
abbrev records28756_28760 : List Blob :=
  records28756_28758 ++ records28758_28760
theorem aligned28756_28760 :
    AlignedValid 12 4 missing28756_28760 records28756_28760 :=
  aligned28756_28758.append aligned28758_28760

def missing28752_28760 : List (BitVec (edgeCount 12)) :=
  missing28752_28756 ++ missing28756_28760
abbrev records28752_28760 : List Blob :=
  records28752_28756 ++ records28756_28760
theorem aligned28752_28760 :
    AlignedValid 12 4 missing28752_28760 records28752_28760 :=
  aligned28752_28756.append aligned28756_28760

def missing28760_28761 : List (BitVec (edgeCount 12)) :=
  [missing28760]
abbrev records28760_28761 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28760]
theorem aligned28760_28761 :
    AlignedValid 12 4 missing28760_28761 records28760_28761 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28760
    maskCheck28760 AlignedValid.nil

def missing28761_28762 : List (BitVec (edgeCount 12)) :=
  [missing28761]
abbrev records28761_28762 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28761]
theorem aligned28761_28762 :
    AlignedValid 12 4 missing28761_28762 records28761_28762 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28761
    maskCheck28761 AlignedValid.nil

def missing28760_28762 : List (BitVec (edgeCount 12)) :=
  missing28760_28761 ++ missing28761_28762
abbrev records28760_28762 : List Blob :=
  records28760_28761 ++ records28761_28762
theorem aligned28760_28762 :
    AlignedValid 12 4 missing28760_28762 records28760_28762 :=
  aligned28760_28761.append aligned28761_28762

def missing28762_28763 : List (BitVec (edgeCount 12)) :=
  [missing28762]
abbrev records28762_28763 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28762]
theorem aligned28762_28763 :
    AlignedValid 12 4 missing28762_28763 records28762_28763 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28762
    maskCheck28762 AlignedValid.nil

def missing28763_28764 : List (BitVec (edgeCount 12)) :=
  [missing28763]
abbrev records28763_28764 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28763]
theorem aligned28763_28764 :
    AlignedValid 12 4 missing28763_28764 records28763_28764 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28763
    maskCheck28763 AlignedValid.nil

def missing28762_28764 : List (BitVec (edgeCount 12)) :=
  missing28762_28763 ++ missing28763_28764
abbrev records28762_28764 : List Blob :=
  records28762_28763 ++ records28763_28764
theorem aligned28762_28764 :
    AlignedValid 12 4 missing28762_28764 records28762_28764 :=
  aligned28762_28763.append aligned28763_28764

def missing28760_28764 : List (BitVec (edgeCount 12)) :=
  missing28760_28762 ++ missing28762_28764
abbrev records28760_28764 : List Blob :=
  records28760_28762 ++ records28762_28764
theorem aligned28760_28764 :
    AlignedValid 12 4 missing28760_28764 records28760_28764 :=
  aligned28760_28762.append aligned28762_28764

def missing28764_28765 : List (BitVec (edgeCount 12)) :=
  [missing28764]
abbrev records28764_28765 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28764]
theorem aligned28764_28765 :
    AlignedValid 12 4 missing28764_28765 records28764_28765 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28764
    maskCheck28764 AlignedValid.nil

def missing28765_28766 : List (BitVec (edgeCount 12)) :=
  [missing28765]
abbrev records28765_28766 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28765]
theorem aligned28765_28766 :
    AlignedValid 12 4 missing28765_28766 records28765_28766 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28765
    maskCheck28765 AlignedValid.nil

def missing28764_28766 : List (BitVec (edgeCount 12)) :=
  missing28764_28765 ++ missing28765_28766
abbrev records28764_28766 : List Blob :=
  records28764_28765 ++ records28765_28766
theorem aligned28764_28766 :
    AlignedValid 12 4 missing28764_28766 records28764_28766 :=
  aligned28764_28765.append aligned28765_28766

def missing28766_28767 : List (BitVec (edgeCount 12)) :=
  [missing28766]
abbrev records28766_28767 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28766]
theorem aligned28766_28767 :
    AlignedValid 12 4 missing28766_28767 records28766_28767 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28766
    maskCheck28766 AlignedValid.nil

def missing28767_28768 : List (BitVec (edgeCount 12)) :=
  [missing28767]
abbrev records28767_28768 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28767]
theorem aligned28767_28768 :
    AlignedValid 12 4 missing28767_28768 records28767_28768 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28767
    maskCheck28767 AlignedValid.nil

def missing28766_28768 : List (BitVec (edgeCount 12)) :=
  missing28766_28767 ++ missing28767_28768
abbrev records28766_28768 : List Blob :=
  records28766_28767 ++ records28767_28768
theorem aligned28766_28768 :
    AlignedValid 12 4 missing28766_28768 records28766_28768 :=
  aligned28766_28767.append aligned28767_28768

def missing28764_28768 : List (BitVec (edgeCount 12)) :=
  missing28764_28766 ++ missing28766_28768
abbrev records28764_28768 : List Blob :=
  records28764_28766 ++ records28766_28768
theorem aligned28764_28768 :
    AlignedValid 12 4 missing28764_28768 records28764_28768 :=
  aligned28764_28766.append aligned28766_28768

def missing28760_28768 : List (BitVec (edgeCount 12)) :=
  missing28760_28764 ++ missing28764_28768
abbrev records28760_28768 : List Blob :=
  records28760_28764 ++ records28764_28768
theorem aligned28760_28768 :
    AlignedValid 12 4 missing28760_28768 records28760_28768 :=
  aligned28760_28764.append aligned28764_28768

def missing28752_28768 : List (BitVec (edgeCount 12)) :=
  missing28752_28760 ++ missing28760_28768
abbrev records28752_28768 : List Blob :=
  records28752_28760 ++ records28760_28768
theorem aligned28752_28768 :
    AlignedValid 12 4 missing28752_28768 records28752_28768 :=
  aligned28752_28760.append aligned28760_28768

def missing28736_28768 : List (BitVec (edgeCount 12)) :=
  missing28736_28752 ++ missing28752_28768
abbrev records28736_28768 : List Blob :=
  records28736_28752 ++ records28752_28768
theorem aligned28736_28768 :
    AlignedValid 12 4 missing28736_28768 records28736_28768 :=
  aligned28736_28752.append aligned28752_28768

def missing28768_28769 : List (BitVec (edgeCount 12)) :=
  [missing28768]
abbrev records28768_28769 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28768]
theorem aligned28768_28769 :
    AlignedValid 12 4 missing28768_28769 records28768_28769 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28768
    maskCheck28768 AlignedValid.nil

def missing28769_28770 : List (BitVec (edgeCount 12)) :=
  [missing28769]
abbrev records28769_28770 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28769]
theorem aligned28769_28770 :
    AlignedValid 12 4 missing28769_28770 records28769_28770 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28769
    maskCheck28769 AlignedValid.nil

def missing28768_28770 : List (BitVec (edgeCount 12)) :=
  missing28768_28769 ++ missing28769_28770
abbrev records28768_28770 : List Blob :=
  records28768_28769 ++ records28769_28770
theorem aligned28768_28770 :
    AlignedValid 12 4 missing28768_28770 records28768_28770 :=
  aligned28768_28769.append aligned28769_28770

def missing28770_28771 : List (BitVec (edgeCount 12)) :=
  [missing28770]
abbrev records28770_28771 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28770]
theorem aligned28770_28771 :
    AlignedValid 12 4 missing28770_28771 records28770_28771 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28770
    maskCheck28770 AlignedValid.nil

def missing28771_28772 : List (BitVec (edgeCount 12)) :=
  [missing28771]
abbrev records28771_28772 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28771]
theorem aligned28771_28772 :
    AlignedValid 12 4 missing28771_28772 records28771_28772 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28771
    maskCheck28771 AlignedValid.nil

def missing28770_28772 : List (BitVec (edgeCount 12)) :=
  missing28770_28771 ++ missing28771_28772
abbrev records28770_28772 : List Blob :=
  records28770_28771 ++ records28771_28772
theorem aligned28770_28772 :
    AlignedValid 12 4 missing28770_28772 records28770_28772 :=
  aligned28770_28771.append aligned28771_28772

def missing28768_28772 : List (BitVec (edgeCount 12)) :=
  missing28768_28770 ++ missing28770_28772
abbrev records28768_28772 : List Blob :=
  records28768_28770 ++ records28770_28772
theorem aligned28768_28772 :
    AlignedValid 12 4 missing28768_28772 records28768_28772 :=
  aligned28768_28770.append aligned28770_28772

def missing28772_28773 : List (BitVec (edgeCount 12)) :=
  [missing28772]
abbrev records28772_28773 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28772]
theorem aligned28772_28773 :
    AlignedValid 12 4 missing28772_28773 records28772_28773 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28772
    maskCheck28772 AlignedValid.nil

def missing28773_28774 : List (BitVec (edgeCount 12)) :=
  [missing28773]
abbrev records28773_28774 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28773]
theorem aligned28773_28774 :
    AlignedValid 12 4 missing28773_28774 records28773_28774 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28773
    maskCheck28773 AlignedValid.nil

def missing28772_28774 : List (BitVec (edgeCount 12)) :=
  missing28772_28773 ++ missing28773_28774
abbrev records28772_28774 : List Blob :=
  records28772_28773 ++ records28773_28774
theorem aligned28772_28774 :
    AlignedValid 12 4 missing28772_28774 records28772_28774 :=
  aligned28772_28773.append aligned28773_28774

def missing28774_28775 : List (BitVec (edgeCount 12)) :=
  [missing28774]
abbrev records28774_28775 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28774]
theorem aligned28774_28775 :
    AlignedValid 12 4 missing28774_28775 records28774_28775 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28774
    maskCheck28774 AlignedValid.nil

def missing28775_28776 : List (BitVec (edgeCount 12)) :=
  [missing28775]
abbrev records28775_28776 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28775]
theorem aligned28775_28776 :
    AlignedValid 12 4 missing28775_28776 records28775_28776 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28775
    maskCheck28775 AlignedValid.nil

def missing28774_28776 : List (BitVec (edgeCount 12)) :=
  missing28774_28775 ++ missing28775_28776
abbrev records28774_28776 : List Blob :=
  records28774_28775 ++ records28775_28776
theorem aligned28774_28776 :
    AlignedValid 12 4 missing28774_28776 records28774_28776 :=
  aligned28774_28775.append aligned28775_28776

def missing28772_28776 : List (BitVec (edgeCount 12)) :=
  missing28772_28774 ++ missing28774_28776
abbrev records28772_28776 : List Blob :=
  records28772_28774 ++ records28774_28776
theorem aligned28772_28776 :
    AlignedValid 12 4 missing28772_28776 records28772_28776 :=
  aligned28772_28774.append aligned28774_28776

def missing28768_28776 : List (BitVec (edgeCount 12)) :=
  missing28768_28772 ++ missing28772_28776
abbrev records28768_28776 : List Blob :=
  records28768_28772 ++ records28772_28776
theorem aligned28768_28776 :
    AlignedValid 12 4 missing28768_28776 records28768_28776 :=
  aligned28768_28772.append aligned28772_28776

def missing28776_28777 : List (BitVec (edgeCount 12)) :=
  [missing28776]
abbrev records28776_28777 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28776]
theorem aligned28776_28777 :
    AlignedValid 12 4 missing28776_28777 records28776_28777 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28776
    maskCheck28776 AlignedValid.nil

def missing28777_28778 : List (BitVec (edgeCount 12)) :=
  [missing28777]
abbrev records28777_28778 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28777]
theorem aligned28777_28778 :
    AlignedValid 12 4 missing28777_28778 records28777_28778 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28777
    maskCheck28777 AlignedValid.nil

def missing28776_28778 : List (BitVec (edgeCount 12)) :=
  missing28776_28777 ++ missing28777_28778
abbrev records28776_28778 : List Blob :=
  records28776_28777 ++ records28777_28778
theorem aligned28776_28778 :
    AlignedValid 12 4 missing28776_28778 records28776_28778 :=
  aligned28776_28777.append aligned28777_28778

def missing28778_28779 : List (BitVec (edgeCount 12)) :=
  [missing28778]
abbrev records28778_28779 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28778]
theorem aligned28778_28779 :
    AlignedValid 12 4 missing28778_28779 records28778_28779 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28778
    maskCheck28778 AlignedValid.nil

def missing28779_28780 : List (BitVec (edgeCount 12)) :=
  [missing28779]
abbrev records28779_28780 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28779]
theorem aligned28779_28780 :
    AlignedValid 12 4 missing28779_28780 records28779_28780 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28779
    maskCheck28779 AlignedValid.nil

def missing28778_28780 : List (BitVec (edgeCount 12)) :=
  missing28778_28779 ++ missing28779_28780
abbrev records28778_28780 : List Blob :=
  records28778_28779 ++ records28779_28780
theorem aligned28778_28780 :
    AlignedValid 12 4 missing28778_28780 records28778_28780 :=
  aligned28778_28779.append aligned28779_28780

def missing28776_28780 : List (BitVec (edgeCount 12)) :=
  missing28776_28778 ++ missing28778_28780
abbrev records28776_28780 : List Blob :=
  records28776_28778 ++ records28778_28780
theorem aligned28776_28780 :
    AlignedValid 12 4 missing28776_28780 records28776_28780 :=
  aligned28776_28778.append aligned28778_28780

def missing28780_28781 : List (BitVec (edgeCount 12)) :=
  [missing28780]
abbrev records28780_28781 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28780]
theorem aligned28780_28781 :
    AlignedValid 12 4 missing28780_28781 records28780_28781 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28780
    maskCheck28780 AlignedValid.nil

def missing28781_28782 : List (BitVec (edgeCount 12)) :=
  [missing28781]
abbrev records28781_28782 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28781]
theorem aligned28781_28782 :
    AlignedValid 12 4 missing28781_28782 records28781_28782 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28781
    maskCheck28781 AlignedValid.nil

def missing28780_28782 : List (BitVec (edgeCount 12)) :=
  missing28780_28781 ++ missing28781_28782
abbrev records28780_28782 : List Blob :=
  records28780_28781 ++ records28781_28782
theorem aligned28780_28782 :
    AlignedValid 12 4 missing28780_28782 records28780_28782 :=
  aligned28780_28781.append aligned28781_28782

def missing28782_28783 : List (BitVec (edgeCount 12)) :=
  [missing28782]
abbrev records28782_28783 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28782]
theorem aligned28782_28783 :
    AlignedValid 12 4 missing28782_28783 records28782_28783 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28782
    maskCheck28782 AlignedValid.nil

def missing28783_28784 : List (BitVec (edgeCount 12)) :=
  [missing28783]
abbrev records28783_28784 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28783]
theorem aligned28783_28784 :
    AlignedValid 12 4 missing28783_28784 records28783_28784 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28783
    maskCheck28783 AlignedValid.nil

def missing28782_28784 : List (BitVec (edgeCount 12)) :=
  missing28782_28783 ++ missing28783_28784
abbrev records28782_28784 : List Blob :=
  records28782_28783 ++ records28783_28784
theorem aligned28782_28784 :
    AlignedValid 12 4 missing28782_28784 records28782_28784 :=
  aligned28782_28783.append aligned28783_28784

def missing28780_28784 : List (BitVec (edgeCount 12)) :=
  missing28780_28782 ++ missing28782_28784
abbrev records28780_28784 : List Blob :=
  records28780_28782 ++ records28782_28784
theorem aligned28780_28784 :
    AlignedValid 12 4 missing28780_28784 records28780_28784 :=
  aligned28780_28782.append aligned28782_28784

def missing28776_28784 : List (BitVec (edgeCount 12)) :=
  missing28776_28780 ++ missing28780_28784
abbrev records28776_28784 : List Blob :=
  records28776_28780 ++ records28780_28784
theorem aligned28776_28784 :
    AlignedValid 12 4 missing28776_28784 records28776_28784 :=
  aligned28776_28780.append aligned28780_28784

def missing28768_28784 : List (BitVec (edgeCount 12)) :=
  missing28768_28776 ++ missing28776_28784
abbrev records28768_28784 : List Blob :=
  records28768_28776 ++ records28776_28784
theorem aligned28768_28784 :
    AlignedValid 12 4 missing28768_28784 records28768_28784 :=
  aligned28768_28776.append aligned28776_28784

def missing28784_28785 : List (BitVec (edgeCount 12)) :=
  [missing28784]
abbrev records28784_28785 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28784]
theorem aligned28784_28785 :
    AlignedValid 12 4 missing28784_28785 records28784_28785 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28784
    maskCheck28784 AlignedValid.nil

def missing28785_28786 : List (BitVec (edgeCount 12)) :=
  [missing28785]
abbrev records28785_28786 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28785]
theorem aligned28785_28786 :
    AlignedValid 12 4 missing28785_28786 records28785_28786 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28785
    maskCheck28785 AlignedValid.nil

def missing28784_28786 : List (BitVec (edgeCount 12)) :=
  missing28784_28785 ++ missing28785_28786
abbrev records28784_28786 : List Blob :=
  records28784_28785 ++ records28785_28786
theorem aligned28784_28786 :
    AlignedValid 12 4 missing28784_28786 records28784_28786 :=
  aligned28784_28785.append aligned28785_28786

def missing28786_28787 : List (BitVec (edgeCount 12)) :=
  [missing28786]
abbrev records28786_28787 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28786]
theorem aligned28786_28787 :
    AlignedValid 12 4 missing28786_28787 records28786_28787 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28786
    maskCheck28786 AlignedValid.nil

def missing28787_28788 : List (BitVec (edgeCount 12)) :=
  [missing28787]
abbrev records28787_28788 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28787]
theorem aligned28787_28788 :
    AlignedValid 12 4 missing28787_28788 records28787_28788 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28787
    maskCheck28787 AlignedValid.nil

def missing28786_28788 : List (BitVec (edgeCount 12)) :=
  missing28786_28787 ++ missing28787_28788
abbrev records28786_28788 : List Blob :=
  records28786_28787 ++ records28787_28788
theorem aligned28786_28788 :
    AlignedValid 12 4 missing28786_28788 records28786_28788 :=
  aligned28786_28787.append aligned28787_28788

def missing28784_28788 : List (BitVec (edgeCount 12)) :=
  missing28784_28786 ++ missing28786_28788
abbrev records28784_28788 : List Blob :=
  records28784_28786 ++ records28786_28788
theorem aligned28784_28788 :
    AlignedValid 12 4 missing28784_28788 records28784_28788 :=
  aligned28784_28786.append aligned28786_28788

def missing28788_28789 : List (BitVec (edgeCount 12)) :=
  [missing28788]
abbrev records28788_28789 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28788]
theorem aligned28788_28789 :
    AlignedValid 12 4 missing28788_28789 records28788_28789 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28788
    maskCheck28788 AlignedValid.nil

def missing28789_28790 : List (BitVec (edgeCount 12)) :=
  [missing28789]
abbrev records28789_28790 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28789]
theorem aligned28789_28790 :
    AlignedValid 12 4 missing28789_28790 records28789_28790 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28789
    maskCheck28789 AlignedValid.nil

def missing28788_28790 : List (BitVec (edgeCount 12)) :=
  missing28788_28789 ++ missing28789_28790
abbrev records28788_28790 : List Blob :=
  records28788_28789 ++ records28789_28790
theorem aligned28788_28790 :
    AlignedValid 12 4 missing28788_28790 records28788_28790 :=
  aligned28788_28789.append aligned28789_28790

def missing28790_28791 : List (BitVec (edgeCount 12)) :=
  [missing28790]
abbrev records28790_28791 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28790]
theorem aligned28790_28791 :
    AlignedValid 12 4 missing28790_28791 records28790_28791 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28790
    maskCheck28790 AlignedValid.nil

def missing28791_28792 : List (BitVec (edgeCount 12)) :=
  [missing28791]
abbrev records28791_28792 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28791]
theorem aligned28791_28792 :
    AlignedValid 12 4 missing28791_28792 records28791_28792 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28791
    maskCheck28791 AlignedValid.nil

def missing28790_28792 : List (BitVec (edgeCount 12)) :=
  missing28790_28791 ++ missing28791_28792
abbrev records28790_28792 : List Blob :=
  records28790_28791 ++ records28791_28792
theorem aligned28790_28792 :
    AlignedValid 12 4 missing28790_28792 records28790_28792 :=
  aligned28790_28791.append aligned28791_28792

def missing28788_28792 : List (BitVec (edgeCount 12)) :=
  missing28788_28790 ++ missing28790_28792
abbrev records28788_28792 : List Blob :=
  records28788_28790 ++ records28790_28792
theorem aligned28788_28792 :
    AlignedValid 12 4 missing28788_28792 records28788_28792 :=
  aligned28788_28790.append aligned28790_28792

def missing28784_28792 : List (BitVec (edgeCount 12)) :=
  missing28784_28788 ++ missing28788_28792
abbrev records28784_28792 : List Blob :=
  records28784_28788 ++ records28788_28792
theorem aligned28784_28792 :
    AlignedValid 12 4 missing28784_28792 records28784_28792 :=
  aligned28784_28788.append aligned28788_28792

def missing28792_28793 : List (BitVec (edgeCount 12)) :=
  [missing28792]
abbrev records28792_28793 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28792]
theorem aligned28792_28793 :
    AlignedValid 12 4 missing28792_28793 records28792_28793 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28792
    maskCheck28792 AlignedValid.nil

def missing28793_28794 : List (BitVec (edgeCount 12)) :=
  [missing28793]
abbrev records28793_28794 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28793]
theorem aligned28793_28794 :
    AlignedValid 12 4 missing28793_28794 records28793_28794 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28793
    maskCheck28793 AlignedValid.nil

def missing28792_28794 : List (BitVec (edgeCount 12)) :=
  missing28792_28793 ++ missing28793_28794
abbrev records28792_28794 : List Blob :=
  records28792_28793 ++ records28793_28794
theorem aligned28792_28794 :
    AlignedValid 12 4 missing28792_28794 records28792_28794 :=
  aligned28792_28793.append aligned28793_28794

def missing28794_28795 : List (BitVec (edgeCount 12)) :=
  [missing28794]
abbrev records28794_28795 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28794]
theorem aligned28794_28795 :
    AlignedValid 12 4 missing28794_28795 records28794_28795 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28794
    maskCheck28794 AlignedValid.nil

def missing28795_28796 : List (BitVec (edgeCount 12)) :=
  [missing28795]
abbrev records28795_28796 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28795]
theorem aligned28795_28796 :
    AlignedValid 12 4 missing28795_28796 records28795_28796 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28795
    maskCheck28795 AlignedValid.nil

def missing28794_28796 : List (BitVec (edgeCount 12)) :=
  missing28794_28795 ++ missing28795_28796
abbrev records28794_28796 : List Blob :=
  records28794_28795 ++ records28795_28796
theorem aligned28794_28796 :
    AlignedValid 12 4 missing28794_28796 records28794_28796 :=
  aligned28794_28795.append aligned28795_28796

def missing28792_28796 : List (BitVec (edgeCount 12)) :=
  missing28792_28794 ++ missing28794_28796
abbrev records28792_28796 : List Blob :=
  records28792_28794 ++ records28794_28796
theorem aligned28792_28796 :
    AlignedValid 12 4 missing28792_28796 records28792_28796 :=
  aligned28792_28794.append aligned28794_28796

def missing28796_28797 : List (BitVec (edgeCount 12)) :=
  [missing28796]
abbrev records28796_28797 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28796]
theorem aligned28796_28797 :
    AlignedValid 12 4 missing28796_28797 records28796_28797 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28796
    maskCheck28796 AlignedValid.nil

def missing28797_28798 : List (BitVec (edgeCount 12)) :=
  [missing28797]
abbrev records28797_28798 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28797]
theorem aligned28797_28798 :
    AlignedValid 12 4 missing28797_28798 records28797_28798 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28797
    maskCheck28797 AlignedValid.nil

def missing28796_28798 : List (BitVec (edgeCount 12)) :=
  missing28796_28797 ++ missing28797_28798
abbrev records28796_28798 : List Blob :=
  records28796_28797 ++ records28797_28798
theorem aligned28796_28798 :
    AlignedValid 12 4 missing28796_28798 records28796_28798 :=
  aligned28796_28797.append aligned28797_28798

def missing28798_28799 : List (BitVec (edgeCount 12)) :=
  [missing28798]
abbrev records28798_28799 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28798]
theorem aligned28798_28799 :
    AlignedValid 12 4 missing28798_28799 records28798_28799 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28798
    maskCheck28798 AlignedValid.nil

def missing28799_28800 : List (BitVec (edgeCount 12)) :=
  [missing28799]
abbrev records28799_28800 : List Blob :=
  [StrongPackedBucketN12A4Shard224.record28799]
theorem aligned28799_28800 :
    AlignedValid 12 4 missing28799_28800 records28799_28800 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard224.check28799
    maskCheck28799 AlignedValid.nil

def missing28798_28800 : List (BitVec (edgeCount 12)) :=
  missing28798_28799 ++ missing28799_28800
abbrev records28798_28800 : List Blob :=
  records28798_28799 ++ records28799_28800
theorem aligned28798_28800 :
    AlignedValid 12 4 missing28798_28800 records28798_28800 :=
  aligned28798_28799.append aligned28799_28800

def missing28796_28800 : List (BitVec (edgeCount 12)) :=
  missing28796_28798 ++ missing28798_28800
abbrev records28796_28800 : List Blob :=
  records28796_28798 ++ records28798_28800
theorem aligned28796_28800 :
    AlignedValid 12 4 missing28796_28800 records28796_28800 :=
  aligned28796_28798.append aligned28798_28800

def missing28792_28800 : List (BitVec (edgeCount 12)) :=
  missing28792_28796 ++ missing28796_28800
abbrev records28792_28800 : List Blob :=
  records28792_28796 ++ records28796_28800
theorem aligned28792_28800 :
    AlignedValid 12 4 missing28792_28800 records28792_28800 :=
  aligned28792_28796.append aligned28796_28800

def missing28784_28800 : List (BitVec (edgeCount 12)) :=
  missing28784_28792 ++ missing28792_28800
abbrev records28784_28800 : List Blob :=
  records28784_28792 ++ records28792_28800
theorem aligned28784_28800 :
    AlignedValid 12 4 missing28784_28800 records28784_28800 :=
  aligned28784_28792.append aligned28792_28800

def missing28768_28800 : List (BitVec (edgeCount 12)) :=
  missing28768_28784 ++ missing28784_28800
abbrev records28768_28800 : List Blob :=
  records28768_28784 ++ records28784_28800
theorem aligned28768_28800 :
    AlignedValid 12 4 missing28768_28800 records28768_28800 :=
  aligned28768_28784.append aligned28784_28800

def missing28736_28800 : List (BitVec (edgeCount 12)) :=
  missing28736_28768 ++ missing28768_28800
abbrev records28736_28800 : List Blob :=
  records28736_28768 ++ records28768_28800
theorem aligned28736_28800 :
    AlignedValid 12 4 missing28736_28800 records28736_28800 :=
  aligned28736_28768.append aligned28768_28800

def missing28672_28800 : List (BitVec (edgeCount 12)) :=
  missing28672_28736 ++ missing28736_28800
abbrev records28672_28800 : List Blob :=
  records28672_28736 ++ records28736_28800
theorem aligned28672_28800 :
    AlignedValid 12 4 missing28672_28800 records28672_28800 :=
  aligned28672_28736.append aligned28736_28800

abbrev missing : List (BitVec (edgeCount 12)) := missing28672_28800
abbrev records : List Blob := records28672_28800
theorem aligned : AlignedValid 12 4 missing records := aligned28672_28800

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard224
