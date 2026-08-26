/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard123

/-! Decode-only alignment checks for n=12, a=4, records 15744--15871. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard123

open PackedBucketCertificate

def missing15744 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4145142069702164480
theorem maskCheck15744 :
    checkMaskFor missing15744 StrongPackedBucketN12A4Shard123.record15744 = true := by
  decide

def missing15745 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4217199663740092416
theorem maskCheck15745 :
    checkMaskFor missing15745 StrongPackedBucketN12A4Shard123.record15745 = true := by
  decide

def missing15746 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4361314851815948288
theorem maskCheck15746 :
    checkMaskFor missing15746 StrongPackedBucketN12A4Shard123.record15746 = true := by
  decide

def missing15747 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4469401242872840192
theorem maskCheck15747 :
    checkMaskFor missing15747 StrongPackedBucketN12A4Shard123.record15747 = true := by
  decide

def missing15748 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5153948386233155584
theorem maskCheck15748 :
    checkMaskFor missing15748 StrongPackedBucketN12A4Shard123.record15748 = true := by
  decide

def missing15749 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5442178762384867328
theorem maskCheck15749 :
    checkMaskFor missing15749 StrongPackedBucketN12A4Shard123.record15749 = true := by
  decide

def missing15750 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5586293950460723200
theorem maskCheck15750 :
    checkMaskFor missing15750 StrongPackedBucketN12A4Shard123.record15750 = true := by
  decide

def missing15751 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5658351544498651136
theorem maskCheck15751 :
    checkMaskFor missing15751 StrongPackedBucketN12A4Shard123.record15751 = true := by
  decide

def missing15752 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6450985078915858432
theorem maskCheck15752 :
    checkMaskFor missing15752 StrongPackedBucketN12A4Shard123.record15752 = true := by
  decide

def missing15753 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6523042672953786368
theorem maskCheck15753 :
    checkMaskFor missing15753 StrongPackedBucketN12A4Shard123.record15753 = true := by
  decide

def missing15754 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6667157861029642240
theorem maskCheck15754 :
    checkMaskFor missing15754 StrongPackedBucketN12A4Shard123.record15754 = true := by
  decide

def missing15755 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7171561019295137792
theorem maskCheck15755 :
    checkMaskFor missing15755 StrongPackedBucketN12A4Shard123.record15755 = true := by
  decide

def missing15756 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7315676207370993664
theorem maskCheck15756 :
    checkMaskFor missing15756 StrongPackedBucketN12A4Shard123.record15756 = true := by
  decide

def missing15757 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7387733801408921600
theorem maskCheck15757 :
    checkMaskFor missing15757 StrongPackedBucketN12A4Shard123.record15757 = true := by
  decide

def missing15758 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7603906583522705408
theorem maskCheck15758 :
    checkMaskFor missing15758 StrongPackedBucketN12A4Shard123.record15758 = true := by
  decide

def missing15759 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7675964177560633344
theorem maskCheck15759 :
    checkMaskFor missing15759 StrongPackedBucketN12A4Shard123.record15759 = true := by
  decide

def missing15760 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7820079365636489216
theorem maskCheck15760 :
    checkMaskFor missing15760 StrongPackedBucketN12A4Shard123.record15760 = true := by
  decide

def missing15761 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8684770494091624448
theorem maskCheck15761 :
    checkMaskFor missing15761 StrongPackedBucketN12A4Shard123.record15761 = true := by
  decide

def missing15762 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14089090046936219648
theorem maskCheck15762 :
    checkMaskFor missing15762 StrongPackedBucketN12A4Shard123.record15762 = true := by
  decide

def missing15763 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14233205235012075520
theorem maskCheck15763 :
    checkMaskFor missing15763 StrongPackedBucketN12A4Shard123.record15763 = true := by
  decide

def missing15764 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14521435611163787264
theorem maskCheck15764 :
    checkMaskFor missing15764 StrongPackedBucketN12A4Shard123.record15764 = true := by
  decide

def missing15765 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16250817868074057728
theorem maskCheck15765 :
    checkMaskFor missing15765 StrongPackedBucketN12A4Shard123.record15765 = true := by
  decide

def missing15766 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18989006441515319296
theorem maskCheck15766 :
    checkMaskFor missing15766 StrongPackedBucketN12A4Shard123.record15766 = true := by
  decide

def missing15767 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19277236817667031040
theorem maskCheck15767 :
    checkMaskFor missing15767 StrongPackedBucketN12A4Shard123.record15767 = true := by
  decide

def missing15768 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19421352005742886912
theorem maskCheck15768 :
    checkMaskFor missing15768 StrongPackedBucketN12A4Shard123.record15768 = true := by
  decide

def missing15769 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19493409599780814848
theorem maskCheck15769 :
    checkMaskFor missing15769 StrongPackedBucketN12A4Shard123.record15769 = true := by
  decide

def missing15770 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20286043134198022144
theorem maskCheck15770 :
    checkMaskFor missing15770 StrongPackedBucketN12A4Shard123.record15770 = true := by
  decide

def missing15771 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20358100728235950080
theorem maskCheck15771 :
    checkMaskFor missing15771 StrongPackedBucketN12A4Shard123.record15771 = true := by
  decide

def missing15772 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20502215916311805952
theorem maskCheck15772 :
    checkMaskFor missing15772 StrongPackedBucketN12A4Shard123.record15772 = true := by
  decide

def missing15773 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20610302307368697856
theorem maskCheck15773 :
    checkMaskFor missing15773 StrongPackedBucketN12A4Shard123.record15773 = true := by
  decide

def missing15774 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21006619074577301504
theorem maskCheck15774 :
    checkMaskFor missing15774 StrongPackedBucketN12A4Shard123.record15774 = true := by
  decide

def missing15775 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21150734262653157376
theorem maskCheck15775 :
    checkMaskFor missing15775 StrongPackedBucketN12A4Shard123.record15775 = true := by
  decide

def missing15776 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21222791856691085312
theorem maskCheck15776 :
    checkMaskFor missing15776 StrongPackedBucketN12A4Shard123.record15776 = true := by
  decide

def missing15777 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21438964638804869120
theorem maskCheck15777 :
    checkMaskFor missing15777 StrongPackedBucketN12A4Shard123.record15777 = true := by
  decide

def missing15778 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21511022232842797056
theorem maskCheck15778 :
    checkMaskFor missing15778 StrongPackedBucketN12A4Shard123.record15778 = true := by
  decide

def missing15779 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21655137420918652928
theorem maskCheck15779 :
    checkMaskFor missing15779 StrongPackedBucketN12A4Shard123.record15779 = true := by
  decide

def missing15780 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21763223811975544832
theorem maskCheck15780 :
    checkMaskFor missing15780 StrongPackedBucketN12A4Shard123.record15780 = true := by
  decide

def missing15781 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22519828549373788160
theorem maskCheck15781 :
    checkMaskFor missing15781 StrongPackedBucketN12A4Shard123.record15781 = true := by
  decide

def missing15782 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22627914940430680064
theorem maskCheck15782 :
    checkMaskFor missing15782 StrongPackedBucketN12A4Shard123.record15782 = true := by
  decide

def missing15783 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22772030128506535936
theorem maskCheck15783 :
    checkMaskFor missing15783 StrongPackedBucketN12A4Shard123.record15783 = true := by
  decide

def missing15784 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23312462083790995456
theorem maskCheck15784 :
    checkMaskFor missing15784 StrongPackedBucketN12A4Shard123.record15784 = true := by
  decide

def missing15785 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23456577271866851328
theorem maskCheck15785 :
    checkMaskFor missing15785 StrongPackedBucketN12A4Shard123.record15785 = true := by
  decide

def missing15786 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23528634865904779264
theorem maskCheck15786 :
    checkMaskFor missing15786 StrongPackedBucketN12A4Shard123.record15786 = true := by
  decide

def missing15787 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23744807648018563072
theorem maskCheck15787 :
    checkMaskFor missing15787 StrongPackedBucketN12A4Shard123.record15787 = true := by
  decide

def missing15788 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23816865242056491008
theorem maskCheck15788 :
    checkMaskFor missing15788 StrongPackedBucketN12A4Shard123.record15788 = true := by
  decide

def missing15789 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23960980430132346880
theorem maskCheck15789 :
    checkMaskFor missing15789 StrongPackedBucketN12A4Shard123.record15789 = true := by
  decide

def missing15790 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24825671558587482112
theorem maskCheck15790 :
    checkMaskFor missing15790 StrongPackedBucketN12A4Shard123.record15790 = true := by
  decide

def missing15791 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25474189904928833536
theorem maskCheck15791 :
    checkMaskFor missing15791 StrongPackedBucketN12A4Shard123.record15791 = true := by
  decide

def missing15792 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25546247498966761472
theorem maskCheck15792 :
    checkMaskFor missing15792 StrongPackedBucketN12A4Shard123.record15792 = true := by
  decide

def missing15793 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25690362687042617344
theorem maskCheck15793 :
    checkMaskFor missing15793 StrongPackedBucketN12A4Shard123.record15793 = true := by
  decide

def missing15794 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25978593063194329088
theorem maskCheck15794 :
    checkMaskFor missing15794 StrongPackedBucketN12A4Shard123.record15794 = true := by
  decide

def missing15795 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32391718932569915392
theorem maskCheck15795 :
    checkMaskFor missing15795 StrongPackedBucketN12A4Shard123.record15795 = true := by
  decide

def missing15796 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37435750515224870912
theorem maskCheck15796 :
    checkMaskFor missing15796 StrongPackedBucketN12A4Shard123.record15796 = true := by
  decide

def missing15797 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37723980891376582656
theorem maskCheck15797 :
    checkMaskFor missing15797 StrongPackedBucketN12A4Shard123.record15797 = true := by
  decide

def missing15798 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37868096079452438528
theorem maskCheck15798 :
    checkMaskFor missing15798 StrongPackedBucketN12A4Shard123.record15798 = true := by
  decide

def missing15799 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37940153673490366464
theorem maskCheck15799 :
    checkMaskFor missing15799 StrongPackedBucketN12A4Shard123.record15799 = true := by
  decide

def missing15800 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38732787207907573760
theorem maskCheck15800 :
    checkMaskFor missing15800 StrongPackedBucketN12A4Shard123.record15800 = true := by
  decide

def missing15801 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38804844801945501696
theorem maskCheck15801 :
    checkMaskFor missing15801 StrongPackedBucketN12A4Shard123.record15801 = true := by
  decide

def missing15802 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38948959990021357568
theorem maskCheck15802 :
    checkMaskFor missing15802 StrongPackedBucketN12A4Shard123.record15802 = true := by
  decide

def missing15803 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39057046381078249472
theorem maskCheck15803 :
    checkMaskFor missing15803 StrongPackedBucketN12A4Shard123.record15803 = true := by
  decide

def missing15804 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39453363148286853120
theorem maskCheck15804 :
    checkMaskFor missing15804 StrongPackedBucketN12A4Shard123.record15804 = true := by
  decide

def missing15805 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39597478336362708992
theorem maskCheck15805 :
    checkMaskFor missing15805 StrongPackedBucketN12A4Shard123.record15805 = true := by
  decide

def missing15806 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39669535930400636928
theorem maskCheck15806 :
    checkMaskFor missing15806 StrongPackedBucketN12A4Shard123.record15806 = true := by
  decide

def missing15807 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39885708712514420736
theorem maskCheck15807 :
    checkMaskFor missing15807 StrongPackedBucketN12A4Shard123.record15807 = true := by
  decide

def missing15808 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39957766306552348672
theorem maskCheck15808 :
    checkMaskFor missing15808 StrongPackedBucketN12A4Shard123.record15808 = true := by
  decide

def missing15809 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40101881494628204544
theorem maskCheck15809 :
    checkMaskFor missing15809 StrongPackedBucketN12A4Shard123.record15809 = true := by
  decide

def missing15810 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40209967885685096448
theorem maskCheck15810 :
    checkMaskFor missing15810 StrongPackedBucketN12A4Shard123.record15810 = true := by
  decide

def missing15811 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40966572623083339776
theorem maskCheck15811 :
    checkMaskFor missing15811 StrongPackedBucketN12A4Shard123.record15811 = true := by
  decide

def missing15812 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41074659014140231680
theorem maskCheck15812 :
    checkMaskFor missing15812 StrongPackedBucketN12A4Shard123.record15812 = true := by
  decide

def missing15813 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41218774202216087552
theorem maskCheck15813 :
    checkMaskFor missing15813 StrongPackedBucketN12A4Shard123.record15813 = true := by
  decide

def missing15814 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41759206157500547072
theorem maskCheck15814 :
    checkMaskFor missing15814 StrongPackedBucketN12A4Shard123.record15814 = true := by
  decide

def missing15815 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41903321345576402944
theorem maskCheck15815 :
    checkMaskFor missing15815 StrongPackedBucketN12A4Shard123.record15815 = true := by
  decide

def missing15816 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41975378939614330880
theorem maskCheck15816 :
    checkMaskFor missing15816 StrongPackedBucketN12A4Shard123.record15816 = true := by
  decide

def missing15817 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42191551721728114688
theorem maskCheck15817 :
    checkMaskFor missing15817 StrongPackedBucketN12A4Shard123.record15817 = true := by
  decide

def missing15818 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42263609315766042624
theorem maskCheck15818 :
    checkMaskFor missing15818 StrongPackedBucketN12A4Shard123.record15818 = true := by
  decide

def missing15819 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42407724503841898496
theorem maskCheck15819 :
    checkMaskFor missing15819 StrongPackedBucketN12A4Shard123.record15819 = true := by
  decide

def missing15820 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43272415632297033728
theorem maskCheck15820 :
    checkMaskFor missing15820 StrongPackedBucketN12A4Shard123.record15820 = true := by
  decide

def missing15821 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43920933978638385152
theorem maskCheck15821 :
    checkMaskFor missing15821 StrongPackedBucketN12A4Shard123.record15821 = true := by
  decide

def missing15822 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43992991572676313088
theorem maskCheck15822 :
    checkMaskFor missing15822 StrongPackedBucketN12A4Shard123.record15822 = true := by
  decide

def missing15823 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 44137106760752168960
theorem maskCheck15823 :
    checkMaskFor missing15823 StrongPackedBucketN12A4Shard123.record15823 = true := by
  decide

def missing15824 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 44425337136903880704
theorem maskCheck15824 :
    checkMaskFor missing15824 StrongPackedBucketN12A4Shard123.record15824 = true := by
  decide

def missing15825 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50838463006279467008
theorem maskCheck15825 :
    checkMaskFor missing15825 StrongPackedBucketN12A4Shard123.record15825 = true := by
  decide

def missing15826 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55594264212782710784
theorem maskCheck15826 :
    checkMaskFor missing15826 StrongPackedBucketN12A4Shard123.record15826 = true := by
  decide

def missing15827 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55738379400858566656
theorem maskCheck15827 :
    checkMaskFor missing15827 StrongPackedBucketN12A4Shard123.record15827 = true := by
  decide

def missing15828 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55810436994896494592
theorem maskCheck15828 :
    checkMaskFor missing15828 StrongPackedBucketN12A4Shard123.record15828 = true := by
  decide

def missing15829 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56026609777010278400
theorem maskCheck15829 :
    checkMaskFor missing15829 StrongPackedBucketN12A4Shard123.record15829 = true := by
  decide

def missing15830 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56098667371048206336
theorem maskCheck15830 :
    checkMaskFor missing15830 StrongPackedBucketN12A4Shard123.record15830 = true := by
  decide

def missing15831 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56242782559124062208
theorem maskCheck15831 :
    checkMaskFor missing15831 StrongPackedBucketN12A4Shard123.record15831 = true := by
  decide

def missing15832 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56350868950180954112
theorem maskCheck15832 :
    checkMaskFor missing15832 StrongPackedBucketN12A4Shard123.record15832 = true := by
  decide

def missing15833 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57107473687579197440
theorem maskCheck15833 :
    checkMaskFor missing15833 StrongPackedBucketN12A4Shard123.record15833 = true := by
  decide

def missing15834 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57215560078636089344
theorem maskCheck15834 :
    checkMaskFor missing15834 StrongPackedBucketN12A4Shard123.record15834 = true := by
  decide

def missing15835 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57359675266711945216
theorem maskCheck15835 :
    checkMaskFor missing15835 StrongPackedBucketN12A4Shard123.record15835 = true := by
  decide

def missing15836 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57755992033920548864
theorem maskCheck15836 :
    checkMaskFor missing15836 StrongPackedBucketN12A4Shard123.record15836 = true := by
  decide

def missing15837 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57828049627958476800
theorem maskCheck15837 :
    checkMaskFor missing15837 StrongPackedBucketN12A4Shard123.record15837 = true := by
  decide

def missing15838 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57972164816034332672
theorem maskCheck15838 :
    checkMaskFor missing15838 StrongPackedBucketN12A4Shard123.record15838 = true := by
  decide

def missing15839 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58080251207091224576
theorem maskCheck15839 :
    checkMaskFor missing15839 StrongPackedBucketN12A4Shard123.record15839 = true := by
  decide

def missing15840 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58260395192186044416
theorem maskCheck15840 :
    checkMaskFor missing15840 StrongPackedBucketN12A4Shard123.record15840 = true := by
  decide

def missing15841 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58368481583242936320
theorem maskCheck15841 :
    checkMaskFor missing15841 StrongPackedBucketN12A4Shard123.record15841 = true := by
  decide

def missing15842 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58512596771318792192
theorem maskCheck15842 :
    checkMaskFor missing15842 StrongPackedBucketN12A4Shard123.record15842 = true := by
  decide

def missing15843 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59377287899773927424
theorem maskCheck15843 :
    checkMaskFor missing15843 StrongPackedBucketN12A4Shard123.record15843 = true := by
  decide

def missing15844 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60061835043134242816
theorem maskCheck15844 :
    checkMaskFor missing15844 StrongPackedBucketN12A4Shard123.record15844 = true := by
  decide

def missing15845 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60133892637172170752
theorem maskCheck15845 :
    checkMaskFor missing15845 StrongPackedBucketN12A4Shard123.record15845 = true := by
  decide

def missing15846 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60278007825248026624
theorem maskCheck15846 :
    checkMaskFor missing15846 StrongPackedBucketN12A4Shard123.record15846 = true := by
  decide

def missing15847 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60566238201399738368
theorem maskCheck15847 :
    checkMaskFor missing15847 StrongPackedBucketN12A4Shard123.record15847 = true := by
  decide

def missing15848 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 62295620458310008832
theorem maskCheck15848 :
    checkMaskFor missing15848 StrongPackedBucketN12A4Shard123.record15848 = true := by
  decide

def missing15849 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1120834182434521088
theorem maskCheck15849 :
    checkMaskFor missing15849 StrongPackedBucketN12A4Shard123.record15849 = true := by
  decide

def missing15850 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1985525310889656320
theorem maskCheck15850 :
    checkMaskFor missing15850 StrongPackedBucketN12A4Shard123.record15850 = true := by
  decide

def missing15851 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2201698093003440128
theorem maskCheck15851 :
    checkMaskFor missing15851 StrongPackedBucketN12A4Shard123.record15851 = true := by
  decide

def missing15852 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4147253132027494400
theorem maskCheck15852 :
    checkMaskFor missing15852 StrongPackedBucketN12A4Shard123.record15852 = true := by
  decide

def missing15853 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4219310726065422336
theorem maskCheck15853 :
    checkMaskFor missing15853 StrongPackedBucketN12A4Shard123.record15853 = true := by
  decide

def missing15854 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4471512305198170112
theorem maskCheck15854 :
    checkMaskFor missing15854 StrongPackedBucketN12A4Shard123.record15854 = true := by
  decide

def missing15855 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5156059448558485504
theorem maskCheck15855 :
    checkMaskFor missing15855 StrongPackedBucketN12A4Shard123.record15855 = true := by
  decide

def missing15856 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5444289824710197248
theorem maskCheck15856 :
    checkMaskFor missing15856 StrongPackedBucketN12A4Shard123.record15856 = true := by
  decide

def missing15857 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5660462606823981056
theorem maskCheck15857 :
    checkMaskFor missing15857 StrongPackedBucketN12A4Shard123.record15857 = true := by
  decide

def missing15858 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6453096141241188352
theorem maskCheck15858 :
    checkMaskFor missing15858 StrongPackedBucketN12A4Shard123.record15858 = true := by
  decide

def missing15859 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6525153735279116288
theorem maskCheck15859 :
    checkMaskFor missing15859 StrongPackedBucketN12A4Shard123.record15859 = true := by
  decide

def missing15860 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8686881556416954368
theorem maskCheck15860 :
    checkMaskFor missing15860 StrongPackedBucketN12A4Shard123.record15860 = true := by
  decide

def missing15861 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14091201109261549568
theorem maskCheck15861 :
    checkMaskFor missing15861 StrongPackedBucketN12A4Shard123.record15861 = true := by
  decide

def missing15862 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14523546673489117184
theorem maskCheck15862 :
    checkMaskFor missing15862 StrongPackedBucketN12A4Shard123.record15862 = true := by
  decide

def missing15863 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18991117503840649216
theorem maskCheck15863 :
    checkMaskFor missing15863 StrongPackedBucketN12A4Shard123.record15863 = true := by
  decide

def missing15864 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19279347879992360960
theorem maskCheck15864 :
    checkMaskFor missing15864 StrongPackedBucketN12A4Shard123.record15864 = true := by
  decide

def missing15865 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19495520662106144768
theorem maskCheck15865 :
    checkMaskFor missing15865 StrongPackedBucketN12A4Shard123.record15865 = true := by
  decide

def missing15866 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20288154196523352064
theorem maskCheck15866 :
    checkMaskFor missing15866 StrongPackedBucketN12A4Shard123.record15866 = true := by
  decide

def missing15867 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20360211790561280000
theorem maskCheck15867 :
    checkMaskFor missing15867 StrongPackedBucketN12A4Shard123.record15867 = true := by
  decide

def missing15868 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20612413369694027776
theorem maskCheck15868 :
    checkMaskFor missing15868 StrongPackedBucketN12A4Shard123.record15868 = true := by
  decide

def missing15869 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22521939611699118080
theorem maskCheck15869 :
    checkMaskFor missing15869 StrongPackedBucketN12A4Shard123.record15869 = true := by
  decide

def missing15870 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22630026002756009984
theorem maskCheck15870 :
    checkMaskFor missing15870 StrongPackedBucketN12A4Shard123.record15870 = true := by
  decide

def missing15871 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23314573146116325376
theorem maskCheck15871 :
    checkMaskFor missing15871 StrongPackedBucketN12A4Shard123.record15871 = true := by
  decide

def missing15744_15745 : List (BitVec (edgeCount 12)) :=
  [missing15744]
abbrev records15744_15745 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15744]
theorem aligned15744_15745 :
    AlignedValid 12 4 missing15744_15745 records15744_15745 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15744
    maskCheck15744 AlignedValid.nil

def missing15745_15746 : List (BitVec (edgeCount 12)) :=
  [missing15745]
abbrev records15745_15746 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15745]
theorem aligned15745_15746 :
    AlignedValid 12 4 missing15745_15746 records15745_15746 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15745
    maskCheck15745 AlignedValid.nil

def missing15744_15746 : List (BitVec (edgeCount 12)) :=
  missing15744_15745 ++ missing15745_15746
abbrev records15744_15746 : List Blob :=
  records15744_15745 ++ records15745_15746
theorem aligned15744_15746 :
    AlignedValid 12 4 missing15744_15746 records15744_15746 :=
  aligned15744_15745.append aligned15745_15746

def missing15746_15747 : List (BitVec (edgeCount 12)) :=
  [missing15746]
abbrev records15746_15747 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15746]
theorem aligned15746_15747 :
    AlignedValid 12 4 missing15746_15747 records15746_15747 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15746
    maskCheck15746 AlignedValid.nil

def missing15747_15748 : List (BitVec (edgeCount 12)) :=
  [missing15747]
abbrev records15747_15748 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15747]
theorem aligned15747_15748 :
    AlignedValid 12 4 missing15747_15748 records15747_15748 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15747
    maskCheck15747 AlignedValid.nil

def missing15746_15748 : List (BitVec (edgeCount 12)) :=
  missing15746_15747 ++ missing15747_15748
abbrev records15746_15748 : List Blob :=
  records15746_15747 ++ records15747_15748
theorem aligned15746_15748 :
    AlignedValid 12 4 missing15746_15748 records15746_15748 :=
  aligned15746_15747.append aligned15747_15748

def missing15744_15748 : List (BitVec (edgeCount 12)) :=
  missing15744_15746 ++ missing15746_15748
abbrev records15744_15748 : List Blob :=
  records15744_15746 ++ records15746_15748
theorem aligned15744_15748 :
    AlignedValid 12 4 missing15744_15748 records15744_15748 :=
  aligned15744_15746.append aligned15746_15748

def missing15748_15749 : List (BitVec (edgeCount 12)) :=
  [missing15748]
abbrev records15748_15749 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15748]
theorem aligned15748_15749 :
    AlignedValid 12 4 missing15748_15749 records15748_15749 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15748
    maskCheck15748 AlignedValid.nil

def missing15749_15750 : List (BitVec (edgeCount 12)) :=
  [missing15749]
abbrev records15749_15750 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15749]
theorem aligned15749_15750 :
    AlignedValid 12 4 missing15749_15750 records15749_15750 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15749
    maskCheck15749 AlignedValid.nil

def missing15748_15750 : List (BitVec (edgeCount 12)) :=
  missing15748_15749 ++ missing15749_15750
abbrev records15748_15750 : List Blob :=
  records15748_15749 ++ records15749_15750
theorem aligned15748_15750 :
    AlignedValid 12 4 missing15748_15750 records15748_15750 :=
  aligned15748_15749.append aligned15749_15750

def missing15750_15751 : List (BitVec (edgeCount 12)) :=
  [missing15750]
abbrev records15750_15751 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15750]
theorem aligned15750_15751 :
    AlignedValid 12 4 missing15750_15751 records15750_15751 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15750
    maskCheck15750 AlignedValid.nil

def missing15751_15752 : List (BitVec (edgeCount 12)) :=
  [missing15751]
abbrev records15751_15752 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15751]
theorem aligned15751_15752 :
    AlignedValid 12 4 missing15751_15752 records15751_15752 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15751
    maskCheck15751 AlignedValid.nil

def missing15750_15752 : List (BitVec (edgeCount 12)) :=
  missing15750_15751 ++ missing15751_15752
abbrev records15750_15752 : List Blob :=
  records15750_15751 ++ records15751_15752
theorem aligned15750_15752 :
    AlignedValid 12 4 missing15750_15752 records15750_15752 :=
  aligned15750_15751.append aligned15751_15752

def missing15748_15752 : List (BitVec (edgeCount 12)) :=
  missing15748_15750 ++ missing15750_15752
abbrev records15748_15752 : List Blob :=
  records15748_15750 ++ records15750_15752
theorem aligned15748_15752 :
    AlignedValid 12 4 missing15748_15752 records15748_15752 :=
  aligned15748_15750.append aligned15750_15752

def missing15744_15752 : List (BitVec (edgeCount 12)) :=
  missing15744_15748 ++ missing15748_15752
abbrev records15744_15752 : List Blob :=
  records15744_15748 ++ records15748_15752
theorem aligned15744_15752 :
    AlignedValid 12 4 missing15744_15752 records15744_15752 :=
  aligned15744_15748.append aligned15748_15752

def missing15752_15753 : List (BitVec (edgeCount 12)) :=
  [missing15752]
abbrev records15752_15753 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15752]
theorem aligned15752_15753 :
    AlignedValid 12 4 missing15752_15753 records15752_15753 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15752
    maskCheck15752 AlignedValid.nil

def missing15753_15754 : List (BitVec (edgeCount 12)) :=
  [missing15753]
abbrev records15753_15754 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15753]
theorem aligned15753_15754 :
    AlignedValid 12 4 missing15753_15754 records15753_15754 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15753
    maskCheck15753 AlignedValid.nil

def missing15752_15754 : List (BitVec (edgeCount 12)) :=
  missing15752_15753 ++ missing15753_15754
abbrev records15752_15754 : List Blob :=
  records15752_15753 ++ records15753_15754
theorem aligned15752_15754 :
    AlignedValid 12 4 missing15752_15754 records15752_15754 :=
  aligned15752_15753.append aligned15753_15754

def missing15754_15755 : List (BitVec (edgeCount 12)) :=
  [missing15754]
abbrev records15754_15755 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15754]
theorem aligned15754_15755 :
    AlignedValid 12 4 missing15754_15755 records15754_15755 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15754
    maskCheck15754 AlignedValid.nil

def missing15755_15756 : List (BitVec (edgeCount 12)) :=
  [missing15755]
abbrev records15755_15756 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15755]
theorem aligned15755_15756 :
    AlignedValid 12 4 missing15755_15756 records15755_15756 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15755
    maskCheck15755 AlignedValid.nil

def missing15754_15756 : List (BitVec (edgeCount 12)) :=
  missing15754_15755 ++ missing15755_15756
abbrev records15754_15756 : List Blob :=
  records15754_15755 ++ records15755_15756
theorem aligned15754_15756 :
    AlignedValid 12 4 missing15754_15756 records15754_15756 :=
  aligned15754_15755.append aligned15755_15756

def missing15752_15756 : List (BitVec (edgeCount 12)) :=
  missing15752_15754 ++ missing15754_15756
abbrev records15752_15756 : List Blob :=
  records15752_15754 ++ records15754_15756
theorem aligned15752_15756 :
    AlignedValid 12 4 missing15752_15756 records15752_15756 :=
  aligned15752_15754.append aligned15754_15756

def missing15756_15757 : List (BitVec (edgeCount 12)) :=
  [missing15756]
abbrev records15756_15757 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15756]
theorem aligned15756_15757 :
    AlignedValid 12 4 missing15756_15757 records15756_15757 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15756
    maskCheck15756 AlignedValid.nil

def missing15757_15758 : List (BitVec (edgeCount 12)) :=
  [missing15757]
abbrev records15757_15758 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15757]
theorem aligned15757_15758 :
    AlignedValid 12 4 missing15757_15758 records15757_15758 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15757
    maskCheck15757 AlignedValid.nil

def missing15756_15758 : List (BitVec (edgeCount 12)) :=
  missing15756_15757 ++ missing15757_15758
abbrev records15756_15758 : List Blob :=
  records15756_15757 ++ records15757_15758
theorem aligned15756_15758 :
    AlignedValid 12 4 missing15756_15758 records15756_15758 :=
  aligned15756_15757.append aligned15757_15758

def missing15758_15759 : List (BitVec (edgeCount 12)) :=
  [missing15758]
abbrev records15758_15759 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15758]
theorem aligned15758_15759 :
    AlignedValid 12 4 missing15758_15759 records15758_15759 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15758
    maskCheck15758 AlignedValid.nil

def missing15759_15760 : List (BitVec (edgeCount 12)) :=
  [missing15759]
abbrev records15759_15760 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15759]
theorem aligned15759_15760 :
    AlignedValid 12 4 missing15759_15760 records15759_15760 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15759
    maskCheck15759 AlignedValid.nil

def missing15758_15760 : List (BitVec (edgeCount 12)) :=
  missing15758_15759 ++ missing15759_15760
abbrev records15758_15760 : List Blob :=
  records15758_15759 ++ records15759_15760
theorem aligned15758_15760 :
    AlignedValid 12 4 missing15758_15760 records15758_15760 :=
  aligned15758_15759.append aligned15759_15760

def missing15756_15760 : List (BitVec (edgeCount 12)) :=
  missing15756_15758 ++ missing15758_15760
abbrev records15756_15760 : List Blob :=
  records15756_15758 ++ records15758_15760
theorem aligned15756_15760 :
    AlignedValid 12 4 missing15756_15760 records15756_15760 :=
  aligned15756_15758.append aligned15758_15760

def missing15752_15760 : List (BitVec (edgeCount 12)) :=
  missing15752_15756 ++ missing15756_15760
abbrev records15752_15760 : List Blob :=
  records15752_15756 ++ records15756_15760
theorem aligned15752_15760 :
    AlignedValid 12 4 missing15752_15760 records15752_15760 :=
  aligned15752_15756.append aligned15756_15760

def missing15744_15760 : List (BitVec (edgeCount 12)) :=
  missing15744_15752 ++ missing15752_15760
abbrev records15744_15760 : List Blob :=
  records15744_15752 ++ records15752_15760
theorem aligned15744_15760 :
    AlignedValid 12 4 missing15744_15760 records15744_15760 :=
  aligned15744_15752.append aligned15752_15760

def missing15760_15761 : List (BitVec (edgeCount 12)) :=
  [missing15760]
abbrev records15760_15761 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15760]
theorem aligned15760_15761 :
    AlignedValid 12 4 missing15760_15761 records15760_15761 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15760
    maskCheck15760 AlignedValid.nil

def missing15761_15762 : List (BitVec (edgeCount 12)) :=
  [missing15761]
abbrev records15761_15762 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15761]
theorem aligned15761_15762 :
    AlignedValid 12 4 missing15761_15762 records15761_15762 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15761
    maskCheck15761 AlignedValid.nil

def missing15760_15762 : List (BitVec (edgeCount 12)) :=
  missing15760_15761 ++ missing15761_15762
abbrev records15760_15762 : List Blob :=
  records15760_15761 ++ records15761_15762
theorem aligned15760_15762 :
    AlignedValid 12 4 missing15760_15762 records15760_15762 :=
  aligned15760_15761.append aligned15761_15762

def missing15762_15763 : List (BitVec (edgeCount 12)) :=
  [missing15762]
abbrev records15762_15763 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15762]
theorem aligned15762_15763 :
    AlignedValid 12 4 missing15762_15763 records15762_15763 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15762
    maskCheck15762 AlignedValid.nil

def missing15763_15764 : List (BitVec (edgeCount 12)) :=
  [missing15763]
abbrev records15763_15764 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15763]
theorem aligned15763_15764 :
    AlignedValid 12 4 missing15763_15764 records15763_15764 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15763
    maskCheck15763 AlignedValid.nil

def missing15762_15764 : List (BitVec (edgeCount 12)) :=
  missing15762_15763 ++ missing15763_15764
abbrev records15762_15764 : List Blob :=
  records15762_15763 ++ records15763_15764
theorem aligned15762_15764 :
    AlignedValid 12 4 missing15762_15764 records15762_15764 :=
  aligned15762_15763.append aligned15763_15764

def missing15760_15764 : List (BitVec (edgeCount 12)) :=
  missing15760_15762 ++ missing15762_15764
abbrev records15760_15764 : List Blob :=
  records15760_15762 ++ records15762_15764
theorem aligned15760_15764 :
    AlignedValid 12 4 missing15760_15764 records15760_15764 :=
  aligned15760_15762.append aligned15762_15764

def missing15764_15765 : List (BitVec (edgeCount 12)) :=
  [missing15764]
abbrev records15764_15765 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15764]
theorem aligned15764_15765 :
    AlignedValid 12 4 missing15764_15765 records15764_15765 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15764
    maskCheck15764 AlignedValid.nil

def missing15765_15766 : List (BitVec (edgeCount 12)) :=
  [missing15765]
abbrev records15765_15766 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15765]
theorem aligned15765_15766 :
    AlignedValid 12 4 missing15765_15766 records15765_15766 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15765
    maskCheck15765 AlignedValid.nil

def missing15764_15766 : List (BitVec (edgeCount 12)) :=
  missing15764_15765 ++ missing15765_15766
abbrev records15764_15766 : List Blob :=
  records15764_15765 ++ records15765_15766
theorem aligned15764_15766 :
    AlignedValid 12 4 missing15764_15766 records15764_15766 :=
  aligned15764_15765.append aligned15765_15766

def missing15766_15767 : List (BitVec (edgeCount 12)) :=
  [missing15766]
abbrev records15766_15767 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15766]
theorem aligned15766_15767 :
    AlignedValid 12 4 missing15766_15767 records15766_15767 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15766
    maskCheck15766 AlignedValid.nil

def missing15767_15768 : List (BitVec (edgeCount 12)) :=
  [missing15767]
abbrev records15767_15768 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15767]
theorem aligned15767_15768 :
    AlignedValid 12 4 missing15767_15768 records15767_15768 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15767
    maskCheck15767 AlignedValid.nil

def missing15766_15768 : List (BitVec (edgeCount 12)) :=
  missing15766_15767 ++ missing15767_15768
abbrev records15766_15768 : List Blob :=
  records15766_15767 ++ records15767_15768
theorem aligned15766_15768 :
    AlignedValid 12 4 missing15766_15768 records15766_15768 :=
  aligned15766_15767.append aligned15767_15768

def missing15764_15768 : List (BitVec (edgeCount 12)) :=
  missing15764_15766 ++ missing15766_15768
abbrev records15764_15768 : List Blob :=
  records15764_15766 ++ records15766_15768
theorem aligned15764_15768 :
    AlignedValid 12 4 missing15764_15768 records15764_15768 :=
  aligned15764_15766.append aligned15766_15768

def missing15760_15768 : List (BitVec (edgeCount 12)) :=
  missing15760_15764 ++ missing15764_15768
abbrev records15760_15768 : List Blob :=
  records15760_15764 ++ records15764_15768
theorem aligned15760_15768 :
    AlignedValid 12 4 missing15760_15768 records15760_15768 :=
  aligned15760_15764.append aligned15764_15768

def missing15768_15769 : List (BitVec (edgeCount 12)) :=
  [missing15768]
abbrev records15768_15769 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15768]
theorem aligned15768_15769 :
    AlignedValid 12 4 missing15768_15769 records15768_15769 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15768
    maskCheck15768 AlignedValid.nil

def missing15769_15770 : List (BitVec (edgeCount 12)) :=
  [missing15769]
abbrev records15769_15770 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15769]
theorem aligned15769_15770 :
    AlignedValid 12 4 missing15769_15770 records15769_15770 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15769
    maskCheck15769 AlignedValid.nil

def missing15768_15770 : List (BitVec (edgeCount 12)) :=
  missing15768_15769 ++ missing15769_15770
abbrev records15768_15770 : List Blob :=
  records15768_15769 ++ records15769_15770
theorem aligned15768_15770 :
    AlignedValid 12 4 missing15768_15770 records15768_15770 :=
  aligned15768_15769.append aligned15769_15770

def missing15770_15771 : List (BitVec (edgeCount 12)) :=
  [missing15770]
abbrev records15770_15771 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15770]
theorem aligned15770_15771 :
    AlignedValid 12 4 missing15770_15771 records15770_15771 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15770
    maskCheck15770 AlignedValid.nil

def missing15771_15772 : List (BitVec (edgeCount 12)) :=
  [missing15771]
abbrev records15771_15772 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15771]
theorem aligned15771_15772 :
    AlignedValid 12 4 missing15771_15772 records15771_15772 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15771
    maskCheck15771 AlignedValid.nil

def missing15770_15772 : List (BitVec (edgeCount 12)) :=
  missing15770_15771 ++ missing15771_15772
abbrev records15770_15772 : List Blob :=
  records15770_15771 ++ records15771_15772
theorem aligned15770_15772 :
    AlignedValid 12 4 missing15770_15772 records15770_15772 :=
  aligned15770_15771.append aligned15771_15772

def missing15768_15772 : List (BitVec (edgeCount 12)) :=
  missing15768_15770 ++ missing15770_15772
abbrev records15768_15772 : List Blob :=
  records15768_15770 ++ records15770_15772
theorem aligned15768_15772 :
    AlignedValid 12 4 missing15768_15772 records15768_15772 :=
  aligned15768_15770.append aligned15770_15772

def missing15772_15773 : List (BitVec (edgeCount 12)) :=
  [missing15772]
abbrev records15772_15773 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15772]
theorem aligned15772_15773 :
    AlignedValid 12 4 missing15772_15773 records15772_15773 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15772
    maskCheck15772 AlignedValid.nil

def missing15773_15774 : List (BitVec (edgeCount 12)) :=
  [missing15773]
abbrev records15773_15774 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15773]
theorem aligned15773_15774 :
    AlignedValid 12 4 missing15773_15774 records15773_15774 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15773
    maskCheck15773 AlignedValid.nil

def missing15772_15774 : List (BitVec (edgeCount 12)) :=
  missing15772_15773 ++ missing15773_15774
abbrev records15772_15774 : List Blob :=
  records15772_15773 ++ records15773_15774
theorem aligned15772_15774 :
    AlignedValid 12 4 missing15772_15774 records15772_15774 :=
  aligned15772_15773.append aligned15773_15774

def missing15774_15775 : List (BitVec (edgeCount 12)) :=
  [missing15774]
abbrev records15774_15775 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15774]
theorem aligned15774_15775 :
    AlignedValid 12 4 missing15774_15775 records15774_15775 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15774
    maskCheck15774 AlignedValid.nil

def missing15775_15776 : List (BitVec (edgeCount 12)) :=
  [missing15775]
abbrev records15775_15776 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15775]
theorem aligned15775_15776 :
    AlignedValid 12 4 missing15775_15776 records15775_15776 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15775
    maskCheck15775 AlignedValid.nil

def missing15774_15776 : List (BitVec (edgeCount 12)) :=
  missing15774_15775 ++ missing15775_15776
abbrev records15774_15776 : List Blob :=
  records15774_15775 ++ records15775_15776
theorem aligned15774_15776 :
    AlignedValid 12 4 missing15774_15776 records15774_15776 :=
  aligned15774_15775.append aligned15775_15776

def missing15772_15776 : List (BitVec (edgeCount 12)) :=
  missing15772_15774 ++ missing15774_15776
abbrev records15772_15776 : List Blob :=
  records15772_15774 ++ records15774_15776
theorem aligned15772_15776 :
    AlignedValid 12 4 missing15772_15776 records15772_15776 :=
  aligned15772_15774.append aligned15774_15776

def missing15768_15776 : List (BitVec (edgeCount 12)) :=
  missing15768_15772 ++ missing15772_15776
abbrev records15768_15776 : List Blob :=
  records15768_15772 ++ records15772_15776
theorem aligned15768_15776 :
    AlignedValid 12 4 missing15768_15776 records15768_15776 :=
  aligned15768_15772.append aligned15772_15776

def missing15760_15776 : List (BitVec (edgeCount 12)) :=
  missing15760_15768 ++ missing15768_15776
abbrev records15760_15776 : List Blob :=
  records15760_15768 ++ records15768_15776
theorem aligned15760_15776 :
    AlignedValid 12 4 missing15760_15776 records15760_15776 :=
  aligned15760_15768.append aligned15768_15776

def missing15744_15776 : List (BitVec (edgeCount 12)) :=
  missing15744_15760 ++ missing15760_15776
abbrev records15744_15776 : List Blob :=
  records15744_15760 ++ records15760_15776
theorem aligned15744_15776 :
    AlignedValid 12 4 missing15744_15776 records15744_15776 :=
  aligned15744_15760.append aligned15760_15776

def missing15776_15777 : List (BitVec (edgeCount 12)) :=
  [missing15776]
abbrev records15776_15777 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15776]
theorem aligned15776_15777 :
    AlignedValid 12 4 missing15776_15777 records15776_15777 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15776
    maskCheck15776 AlignedValid.nil

def missing15777_15778 : List (BitVec (edgeCount 12)) :=
  [missing15777]
abbrev records15777_15778 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15777]
theorem aligned15777_15778 :
    AlignedValid 12 4 missing15777_15778 records15777_15778 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15777
    maskCheck15777 AlignedValid.nil

def missing15776_15778 : List (BitVec (edgeCount 12)) :=
  missing15776_15777 ++ missing15777_15778
abbrev records15776_15778 : List Blob :=
  records15776_15777 ++ records15777_15778
theorem aligned15776_15778 :
    AlignedValid 12 4 missing15776_15778 records15776_15778 :=
  aligned15776_15777.append aligned15777_15778

def missing15778_15779 : List (BitVec (edgeCount 12)) :=
  [missing15778]
abbrev records15778_15779 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15778]
theorem aligned15778_15779 :
    AlignedValid 12 4 missing15778_15779 records15778_15779 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15778
    maskCheck15778 AlignedValid.nil

def missing15779_15780 : List (BitVec (edgeCount 12)) :=
  [missing15779]
abbrev records15779_15780 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15779]
theorem aligned15779_15780 :
    AlignedValid 12 4 missing15779_15780 records15779_15780 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15779
    maskCheck15779 AlignedValid.nil

def missing15778_15780 : List (BitVec (edgeCount 12)) :=
  missing15778_15779 ++ missing15779_15780
abbrev records15778_15780 : List Blob :=
  records15778_15779 ++ records15779_15780
theorem aligned15778_15780 :
    AlignedValid 12 4 missing15778_15780 records15778_15780 :=
  aligned15778_15779.append aligned15779_15780

def missing15776_15780 : List (BitVec (edgeCount 12)) :=
  missing15776_15778 ++ missing15778_15780
abbrev records15776_15780 : List Blob :=
  records15776_15778 ++ records15778_15780
theorem aligned15776_15780 :
    AlignedValid 12 4 missing15776_15780 records15776_15780 :=
  aligned15776_15778.append aligned15778_15780

def missing15780_15781 : List (BitVec (edgeCount 12)) :=
  [missing15780]
abbrev records15780_15781 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15780]
theorem aligned15780_15781 :
    AlignedValid 12 4 missing15780_15781 records15780_15781 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15780
    maskCheck15780 AlignedValid.nil

def missing15781_15782 : List (BitVec (edgeCount 12)) :=
  [missing15781]
abbrev records15781_15782 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15781]
theorem aligned15781_15782 :
    AlignedValid 12 4 missing15781_15782 records15781_15782 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15781
    maskCheck15781 AlignedValid.nil

def missing15780_15782 : List (BitVec (edgeCount 12)) :=
  missing15780_15781 ++ missing15781_15782
abbrev records15780_15782 : List Blob :=
  records15780_15781 ++ records15781_15782
theorem aligned15780_15782 :
    AlignedValid 12 4 missing15780_15782 records15780_15782 :=
  aligned15780_15781.append aligned15781_15782

def missing15782_15783 : List (BitVec (edgeCount 12)) :=
  [missing15782]
abbrev records15782_15783 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15782]
theorem aligned15782_15783 :
    AlignedValid 12 4 missing15782_15783 records15782_15783 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15782
    maskCheck15782 AlignedValid.nil

def missing15783_15784 : List (BitVec (edgeCount 12)) :=
  [missing15783]
abbrev records15783_15784 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15783]
theorem aligned15783_15784 :
    AlignedValid 12 4 missing15783_15784 records15783_15784 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15783
    maskCheck15783 AlignedValid.nil

def missing15782_15784 : List (BitVec (edgeCount 12)) :=
  missing15782_15783 ++ missing15783_15784
abbrev records15782_15784 : List Blob :=
  records15782_15783 ++ records15783_15784
theorem aligned15782_15784 :
    AlignedValid 12 4 missing15782_15784 records15782_15784 :=
  aligned15782_15783.append aligned15783_15784

def missing15780_15784 : List (BitVec (edgeCount 12)) :=
  missing15780_15782 ++ missing15782_15784
abbrev records15780_15784 : List Blob :=
  records15780_15782 ++ records15782_15784
theorem aligned15780_15784 :
    AlignedValid 12 4 missing15780_15784 records15780_15784 :=
  aligned15780_15782.append aligned15782_15784

def missing15776_15784 : List (BitVec (edgeCount 12)) :=
  missing15776_15780 ++ missing15780_15784
abbrev records15776_15784 : List Blob :=
  records15776_15780 ++ records15780_15784
theorem aligned15776_15784 :
    AlignedValid 12 4 missing15776_15784 records15776_15784 :=
  aligned15776_15780.append aligned15780_15784

def missing15784_15785 : List (BitVec (edgeCount 12)) :=
  [missing15784]
abbrev records15784_15785 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15784]
theorem aligned15784_15785 :
    AlignedValid 12 4 missing15784_15785 records15784_15785 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15784
    maskCheck15784 AlignedValid.nil

def missing15785_15786 : List (BitVec (edgeCount 12)) :=
  [missing15785]
abbrev records15785_15786 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15785]
theorem aligned15785_15786 :
    AlignedValid 12 4 missing15785_15786 records15785_15786 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15785
    maskCheck15785 AlignedValid.nil

def missing15784_15786 : List (BitVec (edgeCount 12)) :=
  missing15784_15785 ++ missing15785_15786
abbrev records15784_15786 : List Blob :=
  records15784_15785 ++ records15785_15786
theorem aligned15784_15786 :
    AlignedValid 12 4 missing15784_15786 records15784_15786 :=
  aligned15784_15785.append aligned15785_15786

def missing15786_15787 : List (BitVec (edgeCount 12)) :=
  [missing15786]
abbrev records15786_15787 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15786]
theorem aligned15786_15787 :
    AlignedValid 12 4 missing15786_15787 records15786_15787 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15786
    maskCheck15786 AlignedValid.nil

def missing15787_15788 : List (BitVec (edgeCount 12)) :=
  [missing15787]
abbrev records15787_15788 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15787]
theorem aligned15787_15788 :
    AlignedValid 12 4 missing15787_15788 records15787_15788 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15787
    maskCheck15787 AlignedValid.nil

def missing15786_15788 : List (BitVec (edgeCount 12)) :=
  missing15786_15787 ++ missing15787_15788
abbrev records15786_15788 : List Blob :=
  records15786_15787 ++ records15787_15788
theorem aligned15786_15788 :
    AlignedValid 12 4 missing15786_15788 records15786_15788 :=
  aligned15786_15787.append aligned15787_15788

def missing15784_15788 : List (BitVec (edgeCount 12)) :=
  missing15784_15786 ++ missing15786_15788
abbrev records15784_15788 : List Blob :=
  records15784_15786 ++ records15786_15788
theorem aligned15784_15788 :
    AlignedValid 12 4 missing15784_15788 records15784_15788 :=
  aligned15784_15786.append aligned15786_15788

def missing15788_15789 : List (BitVec (edgeCount 12)) :=
  [missing15788]
abbrev records15788_15789 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15788]
theorem aligned15788_15789 :
    AlignedValid 12 4 missing15788_15789 records15788_15789 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15788
    maskCheck15788 AlignedValid.nil

def missing15789_15790 : List (BitVec (edgeCount 12)) :=
  [missing15789]
abbrev records15789_15790 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15789]
theorem aligned15789_15790 :
    AlignedValid 12 4 missing15789_15790 records15789_15790 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15789
    maskCheck15789 AlignedValid.nil

def missing15788_15790 : List (BitVec (edgeCount 12)) :=
  missing15788_15789 ++ missing15789_15790
abbrev records15788_15790 : List Blob :=
  records15788_15789 ++ records15789_15790
theorem aligned15788_15790 :
    AlignedValid 12 4 missing15788_15790 records15788_15790 :=
  aligned15788_15789.append aligned15789_15790

def missing15790_15791 : List (BitVec (edgeCount 12)) :=
  [missing15790]
abbrev records15790_15791 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15790]
theorem aligned15790_15791 :
    AlignedValid 12 4 missing15790_15791 records15790_15791 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15790
    maskCheck15790 AlignedValid.nil

def missing15791_15792 : List (BitVec (edgeCount 12)) :=
  [missing15791]
abbrev records15791_15792 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15791]
theorem aligned15791_15792 :
    AlignedValid 12 4 missing15791_15792 records15791_15792 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15791
    maskCheck15791 AlignedValid.nil

def missing15790_15792 : List (BitVec (edgeCount 12)) :=
  missing15790_15791 ++ missing15791_15792
abbrev records15790_15792 : List Blob :=
  records15790_15791 ++ records15791_15792
theorem aligned15790_15792 :
    AlignedValid 12 4 missing15790_15792 records15790_15792 :=
  aligned15790_15791.append aligned15791_15792

def missing15788_15792 : List (BitVec (edgeCount 12)) :=
  missing15788_15790 ++ missing15790_15792
abbrev records15788_15792 : List Blob :=
  records15788_15790 ++ records15790_15792
theorem aligned15788_15792 :
    AlignedValid 12 4 missing15788_15792 records15788_15792 :=
  aligned15788_15790.append aligned15790_15792

def missing15784_15792 : List (BitVec (edgeCount 12)) :=
  missing15784_15788 ++ missing15788_15792
abbrev records15784_15792 : List Blob :=
  records15784_15788 ++ records15788_15792
theorem aligned15784_15792 :
    AlignedValid 12 4 missing15784_15792 records15784_15792 :=
  aligned15784_15788.append aligned15788_15792

def missing15776_15792 : List (BitVec (edgeCount 12)) :=
  missing15776_15784 ++ missing15784_15792
abbrev records15776_15792 : List Blob :=
  records15776_15784 ++ records15784_15792
theorem aligned15776_15792 :
    AlignedValid 12 4 missing15776_15792 records15776_15792 :=
  aligned15776_15784.append aligned15784_15792

def missing15792_15793 : List (BitVec (edgeCount 12)) :=
  [missing15792]
abbrev records15792_15793 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15792]
theorem aligned15792_15793 :
    AlignedValid 12 4 missing15792_15793 records15792_15793 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15792
    maskCheck15792 AlignedValid.nil

def missing15793_15794 : List (BitVec (edgeCount 12)) :=
  [missing15793]
abbrev records15793_15794 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15793]
theorem aligned15793_15794 :
    AlignedValid 12 4 missing15793_15794 records15793_15794 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15793
    maskCheck15793 AlignedValid.nil

def missing15792_15794 : List (BitVec (edgeCount 12)) :=
  missing15792_15793 ++ missing15793_15794
abbrev records15792_15794 : List Blob :=
  records15792_15793 ++ records15793_15794
theorem aligned15792_15794 :
    AlignedValid 12 4 missing15792_15794 records15792_15794 :=
  aligned15792_15793.append aligned15793_15794

def missing15794_15795 : List (BitVec (edgeCount 12)) :=
  [missing15794]
abbrev records15794_15795 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15794]
theorem aligned15794_15795 :
    AlignedValid 12 4 missing15794_15795 records15794_15795 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15794
    maskCheck15794 AlignedValid.nil

def missing15795_15796 : List (BitVec (edgeCount 12)) :=
  [missing15795]
abbrev records15795_15796 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15795]
theorem aligned15795_15796 :
    AlignedValid 12 4 missing15795_15796 records15795_15796 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15795
    maskCheck15795 AlignedValid.nil

def missing15794_15796 : List (BitVec (edgeCount 12)) :=
  missing15794_15795 ++ missing15795_15796
abbrev records15794_15796 : List Blob :=
  records15794_15795 ++ records15795_15796
theorem aligned15794_15796 :
    AlignedValid 12 4 missing15794_15796 records15794_15796 :=
  aligned15794_15795.append aligned15795_15796

def missing15792_15796 : List (BitVec (edgeCount 12)) :=
  missing15792_15794 ++ missing15794_15796
abbrev records15792_15796 : List Blob :=
  records15792_15794 ++ records15794_15796
theorem aligned15792_15796 :
    AlignedValid 12 4 missing15792_15796 records15792_15796 :=
  aligned15792_15794.append aligned15794_15796

def missing15796_15797 : List (BitVec (edgeCount 12)) :=
  [missing15796]
abbrev records15796_15797 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15796]
theorem aligned15796_15797 :
    AlignedValid 12 4 missing15796_15797 records15796_15797 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15796
    maskCheck15796 AlignedValid.nil

def missing15797_15798 : List (BitVec (edgeCount 12)) :=
  [missing15797]
abbrev records15797_15798 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15797]
theorem aligned15797_15798 :
    AlignedValid 12 4 missing15797_15798 records15797_15798 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15797
    maskCheck15797 AlignedValid.nil

def missing15796_15798 : List (BitVec (edgeCount 12)) :=
  missing15796_15797 ++ missing15797_15798
abbrev records15796_15798 : List Blob :=
  records15796_15797 ++ records15797_15798
theorem aligned15796_15798 :
    AlignedValid 12 4 missing15796_15798 records15796_15798 :=
  aligned15796_15797.append aligned15797_15798

def missing15798_15799 : List (BitVec (edgeCount 12)) :=
  [missing15798]
abbrev records15798_15799 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15798]
theorem aligned15798_15799 :
    AlignedValid 12 4 missing15798_15799 records15798_15799 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15798
    maskCheck15798 AlignedValid.nil

def missing15799_15800 : List (BitVec (edgeCount 12)) :=
  [missing15799]
abbrev records15799_15800 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15799]
theorem aligned15799_15800 :
    AlignedValid 12 4 missing15799_15800 records15799_15800 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15799
    maskCheck15799 AlignedValid.nil

def missing15798_15800 : List (BitVec (edgeCount 12)) :=
  missing15798_15799 ++ missing15799_15800
abbrev records15798_15800 : List Blob :=
  records15798_15799 ++ records15799_15800
theorem aligned15798_15800 :
    AlignedValid 12 4 missing15798_15800 records15798_15800 :=
  aligned15798_15799.append aligned15799_15800

def missing15796_15800 : List (BitVec (edgeCount 12)) :=
  missing15796_15798 ++ missing15798_15800
abbrev records15796_15800 : List Blob :=
  records15796_15798 ++ records15798_15800
theorem aligned15796_15800 :
    AlignedValid 12 4 missing15796_15800 records15796_15800 :=
  aligned15796_15798.append aligned15798_15800

def missing15792_15800 : List (BitVec (edgeCount 12)) :=
  missing15792_15796 ++ missing15796_15800
abbrev records15792_15800 : List Blob :=
  records15792_15796 ++ records15796_15800
theorem aligned15792_15800 :
    AlignedValid 12 4 missing15792_15800 records15792_15800 :=
  aligned15792_15796.append aligned15796_15800

def missing15800_15801 : List (BitVec (edgeCount 12)) :=
  [missing15800]
abbrev records15800_15801 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15800]
theorem aligned15800_15801 :
    AlignedValid 12 4 missing15800_15801 records15800_15801 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15800
    maskCheck15800 AlignedValid.nil

def missing15801_15802 : List (BitVec (edgeCount 12)) :=
  [missing15801]
abbrev records15801_15802 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15801]
theorem aligned15801_15802 :
    AlignedValid 12 4 missing15801_15802 records15801_15802 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15801
    maskCheck15801 AlignedValid.nil

def missing15800_15802 : List (BitVec (edgeCount 12)) :=
  missing15800_15801 ++ missing15801_15802
abbrev records15800_15802 : List Blob :=
  records15800_15801 ++ records15801_15802
theorem aligned15800_15802 :
    AlignedValid 12 4 missing15800_15802 records15800_15802 :=
  aligned15800_15801.append aligned15801_15802

def missing15802_15803 : List (BitVec (edgeCount 12)) :=
  [missing15802]
abbrev records15802_15803 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15802]
theorem aligned15802_15803 :
    AlignedValid 12 4 missing15802_15803 records15802_15803 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15802
    maskCheck15802 AlignedValid.nil

def missing15803_15804 : List (BitVec (edgeCount 12)) :=
  [missing15803]
abbrev records15803_15804 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15803]
theorem aligned15803_15804 :
    AlignedValid 12 4 missing15803_15804 records15803_15804 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15803
    maskCheck15803 AlignedValid.nil

def missing15802_15804 : List (BitVec (edgeCount 12)) :=
  missing15802_15803 ++ missing15803_15804
abbrev records15802_15804 : List Blob :=
  records15802_15803 ++ records15803_15804
theorem aligned15802_15804 :
    AlignedValid 12 4 missing15802_15804 records15802_15804 :=
  aligned15802_15803.append aligned15803_15804

def missing15800_15804 : List (BitVec (edgeCount 12)) :=
  missing15800_15802 ++ missing15802_15804
abbrev records15800_15804 : List Blob :=
  records15800_15802 ++ records15802_15804
theorem aligned15800_15804 :
    AlignedValid 12 4 missing15800_15804 records15800_15804 :=
  aligned15800_15802.append aligned15802_15804

def missing15804_15805 : List (BitVec (edgeCount 12)) :=
  [missing15804]
abbrev records15804_15805 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15804]
theorem aligned15804_15805 :
    AlignedValid 12 4 missing15804_15805 records15804_15805 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15804
    maskCheck15804 AlignedValid.nil

def missing15805_15806 : List (BitVec (edgeCount 12)) :=
  [missing15805]
abbrev records15805_15806 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15805]
theorem aligned15805_15806 :
    AlignedValid 12 4 missing15805_15806 records15805_15806 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15805
    maskCheck15805 AlignedValid.nil

def missing15804_15806 : List (BitVec (edgeCount 12)) :=
  missing15804_15805 ++ missing15805_15806
abbrev records15804_15806 : List Blob :=
  records15804_15805 ++ records15805_15806
theorem aligned15804_15806 :
    AlignedValid 12 4 missing15804_15806 records15804_15806 :=
  aligned15804_15805.append aligned15805_15806

def missing15806_15807 : List (BitVec (edgeCount 12)) :=
  [missing15806]
abbrev records15806_15807 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15806]
theorem aligned15806_15807 :
    AlignedValid 12 4 missing15806_15807 records15806_15807 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15806
    maskCheck15806 AlignedValid.nil

def missing15807_15808 : List (BitVec (edgeCount 12)) :=
  [missing15807]
abbrev records15807_15808 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15807]
theorem aligned15807_15808 :
    AlignedValid 12 4 missing15807_15808 records15807_15808 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15807
    maskCheck15807 AlignedValid.nil

def missing15806_15808 : List (BitVec (edgeCount 12)) :=
  missing15806_15807 ++ missing15807_15808
abbrev records15806_15808 : List Blob :=
  records15806_15807 ++ records15807_15808
theorem aligned15806_15808 :
    AlignedValid 12 4 missing15806_15808 records15806_15808 :=
  aligned15806_15807.append aligned15807_15808

def missing15804_15808 : List (BitVec (edgeCount 12)) :=
  missing15804_15806 ++ missing15806_15808
abbrev records15804_15808 : List Blob :=
  records15804_15806 ++ records15806_15808
theorem aligned15804_15808 :
    AlignedValid 12 4 missing15804_15808 records15804_15808 :=
  aligned15804_15806.append aligned15806_15808

def missing15800_15808 : List (BitVec (edgeCount 12)) :=
  missing15800_15804 ++ missing15804_15808
abbrev records15800_15808 : List Blob :=
  records15800_15804 ++ records15804_15808
theorem aligned15800_15808 :
    AlignedValid 12 4 missing15800_15808 records15800_15808 :=
  aligned15800_15804.append aligned15804_15808

def missing15792_15808 : List (BitVec (edgeCount 12)) :=
  missing15792_15800 ++ missing15800_15808
abbrev records15792_15808 : List Blob :=
  records15792_15800 ++ records15800_15808
theorem aligned15792_15808 :
    AlignedValid 12 4 missing15792_15808 records15792_15808 :=
  aligned15792_15800.append aligned15800_15808

def missing15776_15808 : List (BitVec (edgeCount 12)) :=
  missing15776_15792 ++ missing15792_15808
abbrev records15776_15808 : List Blob :=
  records15776_15792 ++ records15792_15808
theorem aligned15776_15808 :
    AlignedValid 12 4 missing15776_15808 records15776_15808 :=
  aligned15776_15792.append aligned15792_15808

def missing15744_15808 : List (BitVec (edgeCount 12)) :=
  missing15744_15776 ++ missing15776_15808
abbrev records15744_15808 : List Blob :=
  records15744_15776 ++ records15776_15808
theorem aligned15744_15808 :
    AlignedValid 12 4 missing15744_15808 records15744_15808 :=
  aligned15744_15776.append aligned15776_15808

def missing15808_15809 : List (BitVec (edgeCount 12)) :=
  [missing15808]
abbrev records15808_15809 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15808]
theorem aligned15808_15809 :
    AlignedValid 12 4 missing15808_15809 records15808_15809 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15808
    maskCheck15808 AlignedValid.nil

def missing15809_15810 : List (BitVec (edgeCount 12)) :=
  [missing15809]
abbrev records15809_15810 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15809]
theorem aligned15809_15810 :
    AlignedValid 12 4 missing15809_15810 records15809_15810 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15809
    maskCheck15809 AlignedValid.nil

def missing15808_15810 : List (BitVec (edgeCount 12)) :=
  missing15808_15809 ++ missing15809_15810
abbrev records15808_15810 : List Blob :=
  records15808_15809 ++ records15809_15810
theorem aligned15808_15810 :
    AlignedValid 12 4 missing15808_15810 records15808_15810 :=
  aligned15808_15809.append aligned15809_15810

def missing15810_15811 : List (BitVec (edgeCount 12)) :=
  [missing15810]
abbrev records15810_15811 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15810]
theorem aligned15810_15811 :
    AlignedValid 12 4 missing15810_15811 records15810_15811 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15810
    maskCheck15810 AlignedValid.nil

def missing15811_15812 : List (BitVec (edgeCount 12)) :=
  [missing15811]
abbrev records15811_15812 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15811]
theorem aligned15811_15812 :
    AlignedValid 12 4 missing15811_15812 records15811_15812 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15811
    maskCheck15811 AlignedValid.nil

def missing15810_15812 : List (BitVec (edgeCount 12)) :=
  missing15810_15811 ++ missing15811_15812
abbrev records15810_15812 : List Blob :=
  records15810_15811 ++ records15811_15812
theorem aligned15810_15812 :
    AlignedValid 12 4 missing15810_15812 records15810_15812 :=
  aligned15810_15811.append aligned15811_15812

def missing15808_15812 : List (BitVec (edgeCount 12)) :=
  missing15808_15810 ++ missing15810_15812
abbrev records15808_15812 : List Blob :=
  records15808_15810 ++ records15810_15812
theorem aligned15808_15812 :
    AlignedValid 12 4 missing15808_15812 records15808_15812 :=
  aligned15808_15810.append aligned15810_15812

def missing15812_15813 : List (BitVec (edgeCount 12)) :=
  [missing15812]
abbrev records15812_15813 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15812]
theorem aligned15812_15813 :
    AlignedValid 12 4 missing15812_15813 records15812_15813 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15812
    maskCheck15812 AlignedValid.nil

def missing15813_15814 : List (BitVec (edgeCount 12)) :=
  [missing15813]
abbrev records15813_15814 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15813]
theorem aligned15813_15814 :
    AlignedValid 12 4 missing15813_15814 records15813_15814 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15813
    maskCheck15813 AlignedValid.nil

def missing15812_15814 : List (BitVec (edgeCount 12)) :=
  missing15812_15813 ++ missing15813_15814
abbrev records15812_15814 : List Blob :=
  records15812_15813 ++ records15813_15814
theorem aligned15812_15814 :
    AlignedValid 12 4 missing15812_15814 records15812_15814 :=
  aligned15812_15813.append aligned15813_15814

def missing15814_15815 : List (BitVec (edgeCount 12)) :=
  [missing15814]
abbrev records15814_15815 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15814]
theorem aligned15814_15815 :
    AlignedValid 12 4 missing15814_15815 records15814_15815 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15814
    maskCheck15814 AlignedValid.nil

def missing15815_15816 : List (BitVec (edgeCount 12)) :=
  [missing15815]
abbrev records15815_15816 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15815]
theorem aligned15815_15816 :
    AlignedValid 12 4 missing15815_15816 records15815_15816 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15815
    maskCheck15815 AlignedValid.nil

def missing15814_15816 : List (BitVec (edgeCount 12)) :=
  missing15814_15815 ++ missing15815_15816
abbrev records15814_15816 : List Blob :=
  records15814_15815 ++ records15815_15816
theorem aligned15814_15816 :
    AlignedValid 12 4 missing15814_15816 records15814_15816 :=
  aligned15814_15815.append aligned15815_15816

def missing15812_15816 : List (BitVec (edgeCount 12)) :=
  missing15812_15814 ++ missing15814_15816
abbrev records15812_15816 : List Blob :=
  records15812_15814 ++ records15814_15816
theorem aligned15812_15816 :
    AlignedValid 12 4 missing15812_15816 records15812_15816 :=
  aligned15812_15814.append aligned15814_15816

def missing15808_15816 : List (BitVec (edgeCount 12)) :=
  missing15808_15812 ++ missing15812_15816
abbrev records15808_15816 : List Blob :=
  records15808_15812 ++ records15812_15816
theorem aligned15808_15816 :
    AlignedValid 12 4 missing15808_15816 records15808_15816 :=
  aligned15808_15812.append aligned15812_15816

def missing15816_15817 : List (BitVec (edgeCount 12)) :=
  [missing15816]
abbrev records15816_15817 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15816]
theorem aligned15816_15817 :
    AlignedValid 12 4 missing15816_15817 records15816_15817 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15816
    maskCheck15816 AlignedValid.nil

def missing15817_15818 : List (BitVec (edgeCount 12)) :=
  [missing15817]
abbrev records15817_15818 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15817]
theorem aligned15817_15818 :
    AlignedValid 12 4 missing15817_15818 records15817_15818 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15817
    maskCheck15817 AlignedValid.nil

def missing15816_15818 : List (BitVec (edgeCount 12)) :=
  missing15816_15817 ++ missing15817_15818
abbrev records15816_15818 : List Blob :=
  records15816_15817 ++ records15817_15818
theorem aligned15816_15818 :
    AlignedValid 12 4 missing15816_15818 records15816_15818 :=
  aligned15816_15817.append aligned15817_15818

def missing15818_15819 : List (BitVec (edgeCount 12)) :=
  [missing15818]
abbrev records15818_15819 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15818]
theorem aligned15818_15819 :
    AlignedValid 12 4 missing15818_15819 records15818_15819 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15818
    maskCheck15818 AlignedValid.nil

def missing15819_15820 : List (BitVec (edgeCount 12)) :=
  [missing15819]
abbrev records15819_15820 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15819]
theorem aligned15819_15820 :
    AlignedValid 12 4 missing15819_15820 records15819_15820 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15819
    maskCheck15819 AlignedValid.nil

def missing15818_15820 : List (BitVec (edgeCount 12)) :=
  missing15818_15819 ++ missing15819_15820
abbrev records15818_15820 : List Blob :=
  records15818_15819 ++ records15819_15820
theorem aligned15818_15820 :
    AlignedValid 12 4 missing15818_15820 records15818_15820 :=
  aligned15818_15819.append aligned15819_15820

def missing15816_15820 : List (BitVec (edgeCount 12)) :=
  missing15816_15818 ++ missing15818_15820
abbrev records15816_15820 : List Blob :=
  records15816_15818 ++ records15818_15820
theorem aligned15816_15820 :
    AlignedValid 12 4 missing15816_15820 records15816_15820 :=
  aligned15816_15818.append aligned15818_15820

def missing15820_15821 : List (BitVec (edgeCount 12)) :=
  [missing15820]
abbrev records15820_15821 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15820]
theorem aligned15820_15821 :
    AlignedValid 12 4 missing15820_15821 records15820_15821 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15820
    maskCheck15820 AlignedValid.nil

def missing15821_15822 : List (BitVec (edgeCount 12)) :=
  [missing15821]
abbrev records15821_15822 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15821]
theorem aligned15821_15822 :
    AlignedValid 12 4 missing15821_15822 records15821_15822 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15821
    maskCheck15821 AlignedValid.nil

def missing15820_15822 : List (BitVec (edgeCount 12)) :=
  missing15820_15821 ++ missing15821_15822
abbrev records15820_15822 : List Blob :=
  records15820_15821 ++ records15821_15822
theorem aligned15820_15822 :
    AlignedValid 12 4 missing15820_15822 records15820_15822 :=
  aligned15820_15821.append aligned15821_15822

def missing15822_15823 : List (BitVec (edgeCount 12)) :=
  [missing15822]
abbrev records15822_15823 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15822]
theorem aligned15822_15823 :
    AlignedValid 12 4 missing15822_15823 records15822_15823 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15822
    maskCheck15822 AlignedValid.nil

def missing15823_15824 : List (BitVec (edgeCount 12)) :=
  [missing15823]
abbrev records15823_15824 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15823]
theorem aligned15823_15824 :
    AlignedValid 12 4 missing15823_15824 records15823_15824 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15823
    maskCheck15823 AlignedValid.nil

def missing15822_15824 : List (BitVec (edgeCount 12)) :=
  missing15822_15823 ++ missing15823_15824
abbrev records15822_15824 : List Blob :=
  records15822_15823 ++ records15823_15824
theorem aligned15822_15824 :
    AlignedValid 12 4 missing15822_15824 records15822_15824 :=
  aligned15822_15823.append aligned15823_15824

def missing15820_15824 : List (BitVec (edgeCount 12)) :=
  missing15820_15822 ++ missing15822_15824
abbrev records15820_15824 : List Blob :=
  records15820_15822 ++ records15822_15824
theorem aligned15820_15824 :
    AlignedValid 12 4 missing15820_15824 records15820_15824 :=
  aligned15820_15822.append aligned15822_15824

def missing15816_15824 : List (BitVec (edgeCount 12)) :=
  missing15816_15820 ++ missing15820_15824
abbrev records15816_15824 : List Blob :=
  records15816_15820 ++ records15820_15824
theorem aligned15816_15824 :
    AlignedValid 12 4 missing15816_15824 records15816_15824 :=
  aligned15816_15820.append aligned15820_15824

def missing15808_15824 : List (BitVec (edgeCount 12)) :=
  missing15808_15816 ++ missing15816_15824
abbrev records15808_15824 : List Blob :=
  records15808_15816 ++ records15816_15824
theorem aligned15808_15824 :
    AlignedValid 12 4 missing15808_15824 records15808_15824 :=
  aligned15808_15816.append aligned15816_15824

def missing15824_15825 : List (BitVec (edgeCount 12)) :=
  [missing15824]
abbrev records15824_15825 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15824]
theorem aligned15824_15825 :
    AlignedValid 12 4 missing15824_15825 records15824_15825 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15824
    maskCheck15824 AlignedValid.nil

def missing15825_15826 : List (BitVec (edgeCount 12)) :=
  [missing15825]
abbrev records15825_15826 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15825]
theorem aligned15825_15826 :
    AlignedValid 12 4 missing15825_15826 records15825_15826 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15825
    maskCheck15825 AlignedValid.nil

def missing15824_15826 : List (BitVec (edgeCount 12)) :=
  missing15824_15825 ++ missing15825_15826
abbrev records15824_15826 : List Blob :=
  records15824_15825 ++ records15825_15826
theorem aligned15824_15826 :
    AlignedValid 12 4 missing15824_15826 records15824_15826 :=
  aligned15824_15825.append aligned15825_15826

def missing15826_15827 : List (BitVec (edgeCount 12)) :=
  [missing15826]
abbrev records15826_15827 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15826]
theorem aligned15826_15827 :
    AlignedValid 12 4 missing15826_15827 records15826_15827 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15826
    maskCheck15826 AlignedValid.nil

def missing15827_15828 : List (BitVec (edgeCount 12)) :=
  [missing15827]
abbrev records15827_15828 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15827]
theorem aligned15827_15828 :
    AlignedValid 12 4 missing15827_15828 records15827_15828 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15827
    maskCheck15827 AlignedValid.nil

def missing15826_15828 : List (BitVec (edgeCount 12)) :=
  missing15826_15827 ++ missing15827_15828
abbrev records15826_15828 : List Blob :=
  records15826_15827 ++ records15827_15828
theorem aligned15826_15828 :
    AlignedValid 12 4 missing15826_15828 records15826_15828 :=
  aligned15826_15827.append aligned15827_15828

def missing15824_15828 : List (BitVec (edgeCount 12)) :=
  missing15824_15826 ++ missing15826_15828
abbrev records15824_15828 : List Blob :=
  records15824_15826 ++ records15826_15828
theorem aligned15824_15828 :
    AlignedValid 12 4 missing15824_15828 records15824_15828 :=
  aligned15824_15826.append aligned15826_15828

def missing15828_15829 : List (BitVec (edgeCount 12)) :=
  [missing15828]
abbrev records15828_15829 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15828]
theorem aligned15828_15829 :
    AlignedValid 12 4 missing15828_15829 records15828_15829 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15828
    maskCheck15828 AlignedValid.nil

def missing15829_15830 : List (BitVec (edgeCount 12)) :=
  [missing15829]
abbrev records15829_15830 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15829]
theorem aligned15829_15830 :
    AlignedValid 12 4 missing15829_15830 records15829_15830 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15829
    maskCheck15829 AlignedValid.nil

def missing15828_15830 : List (BitVec (edgeCount 12)) :=
  missing15828_15829 ++ missing15829_15830
abbrev records15828_15830 : List Blob :=
  records15828_15829 ++ records15829_15830
theorem aligned15828_15830 :
    AlignedValid 12 4 missing15828_15830 records15828_15830 :=
  aligned15828_15829.append aligned15829_15830

def missing15830_15831 : List (BitVec (edgeCount 12)) :=
  [missing15830]
abbrev records15830_15831 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15830]
theorem aligned15830_15831 :
    AlignedValid 12 4 missing15830_15831 records15830_15831 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15830
    maskCheck15830 AlignedValid.nil

def missing15831_15832 : List (BitVec (edgeCount 12)) :=
  [missing15831]
abbrev records15831_15832 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15831]
theorem aligned15831_15832 :
    AlignedValid 12 4 missing15831_15832 records15831_15832 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15831
    maskCheck15831 AlignedValid.nil

def missing15830_15832 : List (BitVec (edgeCount 12)) :=
  missing15830_15831 ++ missing15831_15832
abbrev records15830_15832 : List Blob :=
  records15830_15831 ++ records15831_15832
theorem aligned15830_15832 :
    AlignedValid 12 4 missing15830_15832 records15830_15832 :=
  aligned15830_15831.append aligned15831_15832

def missing15828_15832 : List (BitVec (edgeCount 12)) :=
  missing15828_15830 ++ missing15830_15832
abbrev records15828_15832 : List Blob :=
  records15828_15830 ++ records15830_15832
theorem aligned15828_15832 :
    AlignedValid 12 4 missing15828_15832 records15828_15832 :=
  aligned15828_15830.append aligned15830_15832

def missing15824_15832 : List (BitVec (edgeCount 12)) :=
  missing15824_15828 ++ missing15828_15832
abbrev records15824_15832 : List Blob :=
  records15824_15828 ++ records15828_15832
theorem aligned15824_15832 :
    AlignedValid 12 4 missing15824_15832 records15824_15832 :=
  aligned15824_15828.append aligned15828_15832

def missing15832_15833 : List (BitVec (edgeCount 12)) :=
  [missing15832]
abbrev records15832_15833 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15832]
theorem aligned15832_15833 :
    AlignedValid 12 4 missing15832_15833 records15832_15833 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15832
    maskCheck15832 AlignedValid.nil

def missing15833_15834 : List (BitVec (edgeCount 12)) :=
  [missing15833]
abbrev records15833_15834 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15833]
theorem aligned15833_15834 :
    AlignedValid 12 4 missing15833_15834 records15833_15834 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15833
    maskCheck15833 AlignedValid.nil

def missing15832_15834 : List (BitVec (edgeCount 12)) :=
  missing15832_15833 ++ missing15833_15834
abbrev records15832_15834 : List Blob :=
  records15832_15833 ++ records15833_15834
theorem aligned15832_15834 :
    AlignedValid 12 4 missing15832_15834 records15832_15834 :=
  aligned15832_15833.append aligned15833_15834

def missing15834_15835 : List (BitVec (edgeCount 12)) :=
  [missing15834]
abbrev records15834_15835 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15834]
theorem aligned15834_15835 :
    AlignedValid 12 4 missing15834_15835 records15834_15835 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15834
    maskCheck15834 AlignedValid.nil

def missing15835_15836 : List (BitVec (edgeCount 12)) :=
  [missing15835]
abbrev records15835_15836 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15835]
theorem aligned15835_15836 :
    AlignedValid 12 4 missing15835_15836 records15835_15836 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15835
    maskCheck15835 AlignedValid.nil

def missing15834_15836 : List (BitVec (edgeCount 12)) :=
  missing15834_15835 ++ missing15835_15836
abbrev records15834_15836 : List Blob :=
  records15834_15835 ++ records15835_15836
theorem aligned15834_15836 :
    AlignedValid 12 4 missing15834_15836 records15834_15836 :=
  aligned15834_15835.append aligned15835_15836

def missing15832_15836 : List (BitVec (edgeCount 12)) :=
  missing15832_15834 ++ missing15834_15836
abbrev records15832_15836 : List Blob :=
  records15832_15834 ++ records15834_15836
theorem aligned15832_15836 :
    AlignedValid 12 4 missing15832_15836 records15832_15836 :=
  aligned15832_15834.append aligned15834_15836

def missing15836_15837 : List (BitVec (edgeCount 12)) :=
  [missing15836]
abbrev records15836_15837 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15836]
theorem aligned15836_15837 :
    AlignedValid 12 4 missing15836_15837 records15836_15837 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15836
    maskCheck15836 AlignedValid.nil

def missing15837_15838 : List (BitVec (edgeCount 12)) :=
  [missing15837]
abbrev records15837_15838 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15837]
theorem aligned15837_15838 :
    AlignedValid 12 4 missing15837_15838 records15837_15838 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15837
    maskCheck15837 AlignedValid.nil

def missing15836_15838 : List (BitVec (edgeCount 12)) :=
  missing15836_15837 ++ missing15837_15838
abbrev records15836_15838 : List Blob :=
  records15836_15837 ++ records15837_15838
theorem aligned15836_15838 :
    AlignedValid 12 4 missing15836_15838 records15836_15838 :=
  aligned15836_15837.append aligned15837_15838

def missing15838_15839 : List (BitVec (edgeCount 12)) :=
  [missing15838]
abbrev records15838_15839 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15838]
theorem aligned15838_15839 :
    AlignedValid 12 4 missing15838_15839 records15838_15839 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15838
    maskCheck15838 AlignedValid.nil

def missing15839_15840 : List (BitVec (edgeCount 12)) :=
  [missing15839]
abbrev records15839_15840 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15839]
theorem aligned15839_15840 :
    AlignedValid 12 4 missing15839_15840 records15839_15840 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15839
    maskCheck15839 AlignedValid.nil

def missing15838_15840 : List (BitVec (edgeCount 12)) :=
  missing15838_15839 ++ missing15839_15840
abbrev records15838_15840 : List Blob :=
  records15838_15839 ++ records15839_15840
theorem aligned15838_15840 :
    AlignedValid 12 4 missing15838_15840 records15838_15840 :=
  aligned15838_15839.append aligned15839_15840

def missing15836_15840 : List (BitVec (edgeCount 12)) :=
  missing15836_15838 ++ missing15838_15840
abbrev records15836_15840 : List Blob :=
  records15836_15838 ++ records15838_15840
theorem aligned15836_15840 :
    AlignedValid 12 4 missing15836_15840 records15836_15840 :=
  aligned15836_15838.append aligned15838_15840

def missing15832_15840 : List (BitVec (edgeCount 12)) :=
  missing15832_15836 ++ missing15836_15840
abbrev records15832_15840 : List Blob :=
  records15832_15836 ++ records15836_15840
theorem aligned15832_15840 :
    AlignedValid 12 4 missing15832_15840 records15832_15840 :=
  aligned15832_15836.append aligned15836_15840

def missing15824_15840 : List (BitVec (edgeCount 12)) :=
  missing15824_15832 ++ missing15832_15840
abbrev records15824_15840 : List Blob :=
  records15824_15832 ++ records15832_15840
theorem aligned15824_15840 :
    AlignedValid 12 4 missing15824_15840 records15824_15840 :=
  aligned15824_15832.append aligned15832_15840

def missing15808_15840 : List (BitVec (edgeCount 12)) :=
  missing15808_15824 ++ missing15824_15840
abbrev records15808_15840 : List Blob :=
  records15808_15824 ++ records15824_15840
theorem aligned15808_15840 :
    AlignedValid 12 4 missing15808_15840 records15808_15840 :=
  aligned15808_15824.append aligned15824_15840

def missing15840_15841 : List (BitVec (edgeCount 12)) :=
  [missing15840]
abbrev records15840_15841 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15840]
theorem aligned15840_15841 :
    AlignedValid 12 4 missing15840_15841 records15840_15841 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15840
    maskCheck15840 AlignedValid.nil

def missing15841_15842 : List (BitVec (edgeCount 12)) :=
  [missing15841]
abbrev records15841_15842 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15841]
theorem aligned15841_15842 :
    AlignedValid 12 4 missing15841_15842 records15841_15842 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15841
    maskCheck15841 AlignedValid.nil

def missing15840_15842 : List (BitVec (edgeCount 12)) :=
  missing15840_15841 ++ missing15841_15842
abbrev records15840_15842 : List Blob :=
  records15840_15841 ++ records15841_15842
theorem aligned15840_15842 :
    AlignedValid 12 4 missing15840_15842 records15840_15842 :=
  aligned15840_15841.append aligned15841_15842

def missing15842_15843 : List (BitVec (edgeCount 12)) :=
  [missing15842]
abbrev records15842_15843 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15842]
theorem aligned15842_15843 :
    AlignedValid 12 4 missing15842_15843 records15842_15843 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15842
    maskCheck15842 AlignedValid.nil

def missing15843_15844 : List (BitVec (edgeCount 12)) :=
  [missing15843]
abbrev records15843_15844 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15843]
theorem aligned15843_15844 :
    AlignedValid 12 4 missing15843_15844 records15843_15844 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15843
    maskCheck15843 AlignedValid.nil

def missing15842_15844 : List (BitVec (edgeCount 12)) :=
  missing15842_15843 ++ missing15843_15844
abbrev records15842_15844 : List Blob :=
  records15842_15843 ++ records15843_15844
theorem aligned15842_15844 :
    AlignedValid 12 4 missing15842_15844 records15842_15844 :=
  aligned15842_15843.append aligned15843_15844

def missing15840_15844 : List (BitVec (edgeCount 12)) :=
  missing15840_15842 ++ missing15842_15844
abbrev records15840_15844 : List Blob :=
  records15840_15842 ++ records15842_15844
theorem aligned15840_15844 :
    AlignedValid 12 4 missing15840_15844 records15840_15844 :=
  aligned15840_15842.append aligned15842_15844

def missing15844_15845 : List (BitVec (edgeCount 12)) :=
  [missing15844]
abbrev records15844_15845 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15844]
theorem aligned15844_15845 :
    AlignedValid 12 4 missing15844_15845 records15844_15845 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15844
    maskCheck15844 AlignedValid.nil

def missing15845_15846 : List (BitVec (edgeCount 12)) :=
  [missing15845]
abbrev records15845_15846 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15845]
theorem aligned15845_15846 :
    AlignedValid 12 4 missing15845_15846 records15845_15846 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15845
    maskCheck15845 AlignedValid.nil

def missing15844_15846 : List (BitVec (edgeCount 12)) :=
  missing15844_15845 ++ missing15845_15846
abbrev records15844_15846 : List Blob :=
  records15844_15845 ++ records15845_15846
theorem aligned15844_15846 :
    AlignedValid 12 4 missing15844_15846 records15844_15846 :=
  aligned15844_15845.append aligned15845_15846

def missing15846_15847 : List (BitVec (edgeCount 12)) :=
  [missing15846]
abbrev records15846_15847 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15846]
theorem aligned15846_15847 :
    AlignedValid 12 4 missing15846_15847 records15846_15847 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15846
    maskCheck15846 AlignedValid.nil

def missing15847_15848 : List (BitVec (edgeCount 12)) :=
  [missing15847]
abbrev records15847_15848 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15847]
theorem aligned15847_15848 :
    AlignedValid 12 4 missing15847_15848 records15847_15848 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15847
    maskCheck15847 AlignedValid.nil

def missing15846_15848 : List (BitVec (edgeCount 12)) :=
  missing15846_15847 ++ missing15847_15848
abbrev records15846_15848 : List Blob :=
  records15846_15847 ++ records15847_15848
theorem aligned15846_15848 :
    AlignedValid 12 4 missing15846_15848 records15846_15848 :=
  aligned15846_15847.append aligned15847_15848

def missing15844_15848 : List (BitVec (edgeCount 12)) :=
  missing15844_15846 ++ missing15846_15848
abbrev records15844_15848 : List Blob :=
  records15844_15846 ++ records15846_15848
theorem aligned15844_15848 :
    AlignedValid 12 4 missing15844_15848 records15844_15848 :=
  aligned15844_15846.append aligned15846_15848

def missing15840_15848 : List (BitVec (edgeCount 12)) :=
  missing15840_15844 ++ missing15844_15848
abbrev records15840_15848 : List Blob :=
  records15840_15844 ++ records15844_15848
theorem aligned15840_15848 :
    AlignedValid 12 4 missing15840_15848 records15840_15848 :=
  aligned15840_15844.append aligned15844_15848

def missing15848_15849 : List (BitVec (edgeCount 12)) :=
  [missing15848]
abbrev records15848_15849 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15848]
theorem aligned15848_15849 :
    AlignedValid 12 4 missing15848_15849 records15848_15849 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15848
    maskCheck15848 AlignedValid.nil

def missing15849_15850 : List (BitVec (edgeCount 12)) :=
  [missing15849]
abbrev records15849_15850 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15849]
theorem aligned15849_15850 :
    AlignedValid 12 4 missing15849_15850 records15849_15850 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15849
    maskCheck15849 AlignedValid.nil

def missing15848_15850 : List (BitVec (edgeCount 12)) :=
  missing15848_15849 ++ missing15849_15850
abbrev records15848_15850 : List Blob :=
  records15848_15849 ++ records15849_15850
theorem aligned15848_15850 :
    AlignedValid 12 4 missing15848_15850 records15848_15850 :=
  aligned15848_15849.append aligned15849_15850

def missing15850_15851 : List (BitVec (edgeCount 12)) :=
  [missing15850]
abbrev records15850_15851 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15850]
theorem aligned15850_15851 :
    AlignedValid 12 4 missing15850_15851 records15850_15851 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15850
    maskCheck15850 AlignedValid.nil

def missing15851_15852 : List (BitVec (edgeCount 12)) :=
  [missing15851]
abbrev records15851_15852 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15851]
theorem aligned15851_15852 :
    AlignedValid 12 4 missing15851_15852 records15851_15852 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15851
    maskCheck15851 AlignedValid.nil

def missing15850_15852 : List (BitVec (edgeCount 12)) :=
  missing15850_15851 ++ missing15851_15852
abbrev records15850_15852 : List Blob :=
  records15850_15851 ++ records15851_15852
theorem aligned15850_15852 :
    AlignedValid 12 4 missing15850_15852 records15850_15852 :=
  aligned15850_15851.append aligned15851_15852

def missing15848_15852 : List (BitVec (edgeCount 12)) :=
  missing15848_15850 ++ missing15850_15852
abbrev records15848_15852 : List Blob :=
  records15848_15850 ++ records15850_15852
theorem aligned15848_15852 :
    AlignedValid 12 4 missing15848_15852 records15848_15852 :=
  aligned15848_15850.append aligned15850_15852

def missing15852_15853 : List (BitVec (edgeCount 12)) :=
  [missing15852]
abbrev records15852_15853 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15852]
theorem aligned15852_15853 :
    AlignedValid 12 4 missing15852_15853 records15852_15853 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15852
    maskCheck15852 AlignedValid.nil

def missing15853_15854 : List (BitVec (edgeCount 12)) :=
  [missing15853]
abbrev records15853_15854 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15853]
theorem aligned15853_15854 :
    AlignedValid 12 4 missing15853_15854 records15853_15854 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15853
    maskCheck15853 AlignedValid.nil

def missing15852_15854 : List (BitVec (edgeCount 12)) :=
  missing15852_15853 ++ missing15853_15854
abbrev records15852_15854 : List Blob :=
  records15852_15853 ++ records15853_15854
theorem aligned15852_15854 :
    AlignedValid 12 4 missing15852_15854 records15852_15854 :=
  aligned15852_15853.append aligned15853_15854

def missing15854_15855 : List (BitVec (edgeCount 12)) :=
  [missing15854]
abbrev records15854_15855 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15854]
theorem aligned15854_15855 :
    AlignedValid 12 4 missing15854_15855 records15854_15855 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15854
    maskCheck15854 AlignedValid.nil

def missing15855_15856 : List (BitVec (edgeCount 12)) :=
  [missing15855]
abbrev records15855_15856 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15855]
theorem aligned15855_15856 :
    AlignedValid 12 4 missing15855_15856 records15855_15856 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15855
    maskCheck15855 AlignedValid.nil

def missing15854_15856 : List (BitVec (edgeCount 12)) :=
  missing15854_15855 ++ missing15855_15856
abbrev records15854_15856 : List Blob :=
  records15854_15855 ++ records15855_15856
theorem aligned15854_15856 :
    AlignedValid 12 4 missing15854_15856 records15854_15856 :=
  aligned15854_15855.append aligned15855_15856

def missing15852_15856 : List (BitVec (edgeCount 12)) :=
  missing15852_15854 ++ missing15854_15856
abbrev records15852_15856 : List Blob :=
  records15852_15854 ++ records15854_15856
theorem aligned15852_15856 :
    AlignedValid 12 4 missing15852_15856 records15852_15856 :=
  aligned15852_15854.append aligned15854_15856

def missing15848_15856 : List (BitVec (edgeCount 12)) :=
  missing15848_15852 ++ missing15852_15856
abbrev records15848_15856 : List Blob :=
  records15848_15852 ++ records15852_15856
theorem aligned15848_15856 :
    AlignedValid 12 4 missing15848_15856 records15848_15856 :=
  aligned15848_15852.append aligned15852_15856

def missing15840_15856 : List (BitVec (edgeCount 12)) :=
  missing15840_15848 ++ missing15848_15856
abbrev records15840_15856 : List Blob :=
  records15840_15848 ++ records15848_15856
theorem aligned15840_15856 :
    AlignedValid 12 4 missing15840_15856 records15840_15856 :=
  aligned15840_15848.append aligned15848_15856

def missing15856_15857 : List (BitVec (edgeCount 12)) :=
  [missing15856]
abbrev records15856_15857 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15856]
theorem aligned15856_15857 :
    AlignedValid 12 4 missing15856_15857 records15856_15857 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15856
    maskCheck15856 AlignedValid.nil

def missing15857_15858 : List (BitVec (edgeCount 12)) :=
  [missing15857]
abbrev records15857_15858 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15857]
theorem aligned15857_15858 :
    AlignedValid 12 4 missing15857_15858 records15857_15858 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15857
    maskCheck15857 AlignedValid.nil

def missing15856_15858 : List (BitVec (edgeCount 12)) :=
  missing15856_15857 ++ missing15857_15858
abbrev records15856_15858 : List Blob :=
  records15856_15857 ++ records15857_15858
theorem aligned15856_15858 :
    AlignedValid 12 4 missing15856_15858 records15856_15858 :=
  aligned15856_15857.append aligned15857_15858

def missing15858_15859 : List (BitVec (edgeCount 12)) :=
  [missing15858]
abbrev records15858_15859 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15858]
theorem aligned15858_15859 :
    AlignedValid 12 4 missing15858_15859 records15858_15859 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15858
    maskCheck15858 AlignedValid.nil

def missing15859_15860 : List (BitVec (edgeCount 12)) :=
  [missing15859]
abbrev records15859_15860 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15859]
theorem aligned15859_15860 :
    AlignedValid 12 4 missing15859_15860 records15859_15860 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15859
    maskCheck15859 AlignedValid.nil

def missing15858_15860 : List (BitVec (edgeCount 12)) :=
  missing15858_15859 ++ missing15859_15860
abbrev records15858_15860 : List Blob :=
  records15858_15859 ++ records15859_15860
theorem aligned15858_15860 :
    AlignedValid 12 4 missing15858_15860 records15858_15860 :=
  aligned15858_15859.append aligned15859_15860

def missing15856_15860 : List (BitVec (edgeCount 12)) :=
  missing15856_15858 ++ missing15858_15860
abbrev records15856_15860 : List Blob :=
  records15856_15858 ++ records15858_15860
theorem aligned15856_15860 :
    AlignedValid 12 4 missing15856_15860 records15856_15860 :=
  aligned15856_15858.append aligned15858_15860

def missing15860_15861 : List (BitVec (edgeCount 12)) :=
  [missing15860]
abbrev records15860_15861 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15860]
theorem aligned15860_15861 :
    AlignedValid 12 4 missing15860_15861 records15860_15861 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15860
    maskCheck15860 AlignedValid.nil

def missing15861_15862 : List (BitVec (edgeCount 12)) :=
  [missing15861]
abbrev records15861_15862 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15861]
theorem aligned15861_15862 :
    AlignedValid 12 4 missing15861_15862 records15861_15862 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15861
    maskCheck15861 AlignedValid.nil

def missing15860_15862 : List (BitVec (edgeCount 12)) :=
  missing15860_15861 ++ missing15861_15862
abbrev records15860_15862 : List Blob :=
  records15860_15861 ++ records15861_15862
theorem aligned15860_15862 :
    AlignedValid 12 4 missing15860_15862 records15860_15862 :=
  aligned15860_15861.append aligned15861_15862

def missing15862_15863 : List (BitVec (edgeCount 12)) :=
  [missing15862]
abbrev records15862_15863 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15862]
theorem aligned15862_15863 :
    AlignedValid 12 4 missing15862_15863 records15862_15863 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15862
    maskCheck15862 AlignedValid.nil

def missing15863_15864 : List (BitVec (edgeCount 12)) :=
  [missing15863]
abbrev records15863_15864 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15863]
theorem aligned15863_15864 :
    AlignedValid 12 4 missing15863_15864 records15863_15864 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15863
    maskCheck15863 AlignedValid.nil

def missing15862_15864 : List (BitVec (edgeCount 12)) :=
  missing15862_15863 ++ missing15863_15864
abbrev records15862_15864 : List Blob :=
  records15862_15863 ++ records15863_15864
theorem aligned15862_15864 :
    AlignedValid 12 4 missing15862_15864 records15862_15864 :=
  aligned15862_15863.append aligned15863_15864

def missing15860_15864 : List (BitVec (edgeCount 12)) :=
  missing15860_15862 ++ missing15862_15864
abbrev records15860_15864 : List Blob :=
  records15860_15862 ++ records15862_15864
theorem aligned15860_15864 :
    AlignedValid 12 4 missing15860_15864 records15860_15864 :=
  aligned15860_15862.append aligned15862_15864

def missing15856_15864 : List (BitVec (edgeCount 12)) :=
  missing15856_15860 ++ missing15860_15864
abbrev records15856_15864 : List Blob :=
  records15856_15860 ++ records15860_15864
theorem aligned15856_15864 :
    AlignedValid 12 4 missing15856_15864 records15856_15864 :=
  aligned15856_15860.append aligned15860_15864

def missing15864_15865 : List (BitVec (edgeCount 12)) :=
  [missing15864]
abbrev records15864_15865 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15864]
theorem aligned15864_15865 :
    AlignedValid 12 4 missing15864_15865 records15864_15865 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15864
    maskCheck15864 AlignedValid.nil

def missing15865_15866 : List (BitVec (edgeCount 12)) :=
  [missing15865]
abbrev records15865_15866 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15865]
theorem aligned15865_15866 :
    AlignedValid 12 4 missing15865_15866 records15865_15866 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15865
    maskCheck15865 AlignedValid.nil

def missing15864_15866 : List (BitVec (edgeCount 12)) :=
  missing15864_15865 ++ missing15865_15866
abbrev records15864_15866 : List Blob :=
  records15864_15865 ++ records15865_15866
theorem aligned15864_15866 :
    AlignedValid 12 4 missing15864_15866 records15864_15866 :=
  aligned15864_15865.append aligned15865_15866

def missing15866_15867 : List (BitVec (edgeCount 12)) :=
  [missing15866]
abbrev records15866_15867 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15866]
theorem aligned15866_15867 :
    AlignedValid 12 4 missing15866_15867 records15866_15867 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15866
    maskCheck15866 AlignedValid.nil

def missing15867_15868 : List (BitVec (edgeCount 12)) :=
  [missing15867]
abbrev records15867_15868 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15867]
theorem aligned15867_15868 :
    AlignedValid 12 4 missing15867_15868 records15867_15868 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15867
    maskCheck15867 AlignedValid.nil

def missing15866_15868 : List (BitVec (edgeCount 12)) :=
  missing15866_15867 ++ missing15867_15868
abbrev records15866_15868 : List Blob :=
  records15866_15867 ++ records15867_15868
theorem aligned15866_15868 :
    AlignedValid 12 4 missing15866_15868 records15866_15868 :=
  aligned15866_15867.append aligned15867_15868

def missing15864_15868 : List (BitVec (edgeCount 12)) :=
  missing15864_15866 ++ missing15866_15868
abbrev records15864_15868 : List Blob :=
  records15864_15866 ++ records15866_15868
theorem aligned15864_15868 :
    AlignedValid 12 4 missing15864_15868 records15864_15868 :=
  aligned15864_15866.append aligned15866_15868

def missing15868_15869 : List (BitVec (edgeCount 12)) :=
  [missing15868]
abbrev records15868_15869 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15868]
theorem aligned15868_15869 :
    AlignedValid 12 4 missing15868_15869 records15868_15869 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15868
    maskCheck15868 AlignedValid.nil

def missing15869_15870 : List (BitVec (edgeCount 12)) :=
  [missing15869]
abbrev records15869_15870 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15869]
theorem aligned15869_15870 :
    AlignedValid 12 4 missing15869_15870 records15869_15870 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15869
    maskCheck15869 AlignedValid.nil

def missing15868_15870 : List (BitVec (edgeCount 12)) :=
  missing15868_15869 ++ missing15869_15870
abbrev records15868_15870 : List Blob :=
  records15868_15869 ++ records15869_15870
theorem aligned15868_15870 :
    AlignedValid 12 4 missing15868_15870 records15868_15870 :=
  aligned15868_15869.append aligned15869_15870

def missing15870_15871 : List (BitVec (edgeCount 12)) :=
  [missing15870]
abbrev records15870_15871 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15870]
theorem aligned15870_15871 :
    AlignedValid 12 4 missing15870_15871 records15870_15871 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15870
    maskCheck15870 AlignedValid.nil

def missing15871_15872 : List (BitVec (edgeCount 12)) :=
  [missing15871]
abbrev records15871_15872 : List Blob :=
  [StrongPackedBucketN12A4Shard123.record15871]
theorem aligned15871_15872 :
    AlignedValid 12 4 missing15871_15872 records15871_15872 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard123.check15871
    maskCheck15871 AlignedValid.nil

def missing15870_15872 : List (BitVec (edgeCount 12)) :=
  missing15870_15871 ++ missing15871_15872
abbrev records15870_15872 : List Blob :=
  records15870_15871 ++ records15871_15872
theorem aligned15870_15872 :
    AlignedValid 12 4 missing15870_15872 records15870_15872 :=
  aligned15870_15871.append aligned15871_15872

def missing15868_15872 : List (BitVec (edgeCount 12)) :=
  missing15868_15870 ++ missing15870_15872
abbrev records15868_15872 : List Blob :=
  records15868_15870 ++ records15870_15872
theorem aligned15868_15872 :
    AlignedValid 12 4 missing15868_15872 records15868_15872 :=
  aligned15868_15870.append aligned15870_15872

def missing15864_15872 : List (BitVec (edgeCount 12)) :=
  missing15864_15868 ++ missing15868_15872
abbrev records15864_15872 : List Blob :=
  records15864_15868 ++ records15868_15872
theorem aligned15864_15872 :
    AlignedValid 12 4 missing15864_15872 records15864_15872 :=
  aligned15864_15868.append aligned15868_15872

def missing15856_15872 : List (BitVec (edgeCount 12)) :=
  missing15856_15864 ++ missing15864_15872
abbrev records15856_15872 : List Blob :=
  records15856_15864 ++ records15864_15872
theorem aligned15856_15872 :
    AlignedValid 12 4 missing15856_15872 records15856_15872 :=
  aligned15856_15864.append aligned15864_15872

def missing15840_15872 : List (BitVec (edgeCount 12)) :=
  missing15840_15856 ++ missing15856_15872
abbrev records15840_15872 : List Blob :=
  records15840_15856 ++ records15856_15872
theorem aligned15840_15872 :
    AlignedValid 12 4 missing15840_15872 records15840_15872 :=
  aligned15840_15856.append aligned15856_15872

def missing15808_15872 : List (BitVec (edgeCount 12)) :=
  missing15808_15840 ++ missing15840_15872
abbrev records15808_15872 : List Blob :=
  records15808_15840 ++ records15840_15872
theorem aligned15808_15872 :
    AlignedValid 12 4 missing15808_15872 records15808_15872 :=
  aligned15808_15840.append aligned15840_15872

def missing15744_15872 : List (BitVec (edgeCount 12)) :=
  missing15744_15808 ++ missing15808_15872
abbrev records15744_15872 : List Blob :=
  records15744_15808 ++ records15808_15872
theorem aligned15744_15872 :
    AlignedValid 12 4 missing15744_15872 records15744_15872 :=
  aligned15744_15808.append aligned15808_15872

abbrev missing : List (BitVec (edgeCount 12)) := missing15744_15872
abbrev records : List Blob := records15744_15872
theorem aligned : AlignedValid 12 4 missing records := aligned15744_15872

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard123
