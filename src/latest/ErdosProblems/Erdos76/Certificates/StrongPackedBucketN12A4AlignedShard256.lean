/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard256

/-! Decode-only alignment checks for n=12, a=4, records 32768--32895. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard256

open PackedBucketCertificate

def missing32768 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28287320985299877888
theorem maskCheck32768 :
    checkMaskFor missing32768 StrongPackedBucketN12A4Shard256.record32768 = true := by
  decide

def missing32769 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41726062273373437952
theorem maskCheck32769 :
    checkMaskFor missing32769 StrongPackedBucketN12A4Shard256.record32769 = true := by
  decide

def missing32770 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46337748291800825856
theorem maskCheck32770 :
    checkMaskFor missing32770 StrongPackedBucketN12A4Shard256.record32770 = true := by
  decide

def missing32771 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50805319122152357888
theorem maskCheck32771 :
    checkMaskFor missing32771 StrongPackedBucketN12A4Shard256.record32771 = true := by
  decide

def missing32772 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 545288018185977856
theorem maskCheck32772 :
    checkMaskFor missing32772 StrongPackedBucketN12A4Shard256.record32772 = true := by
  decide

def missing32773 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 833518394337689600
theorem maskCheck32773 :
    checkMaskFor missing32773 StrongPackedBucketN12A4Shard256.record32773 = true := by
  decide

def missing32774 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 977633582413545472
theorem maskCheck32774 :
    checkMaskFor missing32774 StrongPackedBucketN12A4Shard256.record32774 = true := by
  decide

def missing32775 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1049691176451473408
theorem maskCheck32775 :
    checkMaskFor missing32775 StrongPackedBucketN12A4Shard256.record32775 = true := by
  decide

def missing32776 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1085719973470437376
theorem maskCheck32776 :
    checkMaskFor missing32776 StrongPackedBucketN12A4Shard256.record32776 = true := by
  decide

def missing32777 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1842324710868680704
theorem maskCheck32777 :
    checkMaskFor missing32777 StrongPackedBucketN12A4Shard256.record32777 = true := by
  decide

def missing32778 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1914382304906608640
theorem maskCheck32778 :
    checkMaskFor missing32778 StrongPackedBucketN12A4Shard256.record32778 = true := by
  decide

def missing32779 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1950411101925572608
theorem maskCheck32779 :
    checkMaskFor missing32779 StrongPackedBucketN12A4Shard256.record32779 = true := by
  decide

def missing32780 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2058497492982464512
theorem maskCheck32780 :
    checkMaskFor missing32780 StrongPackedBucketN12A4Shard256.record32780 = true := by
  decide

def missing32781 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2094526290001428480
theorem maskCheck32781 :
    checkMaskFor missing32781 StrongPackedBucketN12A4Shard256.record32781 = true := by
  decide

def missing32782 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2166583884039356416
theorem maskCheck32782 :
    checkMaskFor missing32782 StrongPackedBucketN12A4Shard256.record32782 = true := by
  decide

def missing32783 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2562900651247960064
theorem maskCheck32783 :
    checkMaskFor missing32783 StrongPackedBucketN12A4Shard256.record32783 = true := by
  decide

def missing32784 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2707015839323815936
theorem maskCheck32784 :
    checkMaskFor missing32784 StrongPackedBucketN12A4Shard256.record32784 = true := by
  decide

def missing32785 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2779073433361743872
theorem maskCheck32785 :
    checkMaskFor missing32785 StrongPackedBucketN12A4Shard256.record32785 = true := by
  decide

def missing32786 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2815102230380707840
theorem maskCheck32786 :
    checkMaskFor missing32786 StrongPackedBucketN12A4Shard256.record32786 = true := by
  decide

def missing32787 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2995246215475527680
theorem maskCheck32787 :
    checkMaskFor missing32787 StrongPackedBucketN12A4Shard256.record32787 = true := by
  decide

def missing32788 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3067303809513455616
theorem maskCheck32788 :
    checkMaskFor missing32788 StrongPackedBucketN12A4Shard256.record32788 = true := by
  decide

def missing32789 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3103332606532419584
theorem maskCheck32789 :
    checkMaskFor missing32789 StrongPackedBucketN12A4Shard256.record32789 = true := by
  decide

def missing32790 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3211418997589311488
theorem maskCheck32790 :
    checkMaskFor missing32790 StrongPackedBucketN12A4Shard256.record32790 = true := by
  decide

def missing32791 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3247447794608275456
theorem maskCheck32791 :
    checkMaskFor missing32791 StrongPackedBucketN12A4Shard256.record32791 = true := by
  decide

def missing32792 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3319505388646203392
theorem maskCheck32792 :
    checkMaskFor missing32792 StrongPackedBucketN12A4Shard256.record32792 = true := by
  decide

def missing32793 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4076110126044446720
theorem maskCheck32793 :
    checkMaskFor missing32793 StrongPackedBucketN12A4Shard256.record32793 = true := by
  decide

def missing32794 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4112138923063410688
theorem maskCheck32794 :
    checkMaskFor missing32794 StrongPackedBucketN12A4Shard256.record32794 = true := by
  decide

def missing32795 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4184196517101338624
theorem maskCheck32795 :
    checkMaskFor missing32795 StrongPackedBucketN12A4Shard256.record32795 = true := by
  decide

def missing32796 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4328311705177194496
theorem maskCheck32796 :
    checkMaskFor missing32796 StrongPackedBucketN12A4Shard256.record32796 = true := by
  decide

def missing32797 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4868743660461654016
theorem maskCheck32797 :
    checkMaskFor missing32797 StrongPackedBucketN12A4Shard256.record32797 = true := by
  decide

def missing32798 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5012858848537509888
theorem maskCheck32798 :
    checkMaskFor missing32798 StrongPackedBucketN12A4Shard256.record32798 = true := by
  decide

def missing32799 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5120945239594401792
theorem maskCheck32799 :
    checkMaskFor missing32799 StrongPackedBucketN12A4Shard256.record32799 = true := by
  decide

def missing32800 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5301089224689221632
theorem maskCheck32800 :
    checkMaskFor missing32800 StrongPackedBucketN12A4Shard256.record32800 = true := by
  decide

def missing32801 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5409175615746113536
theorem maskCheck32801 :
    checkMaskFor missing32801 StrongPackedBucketN12A4Shard256.record32801 = true := by
  decide

def missing32802 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5553290803821969408
theorem maskCheck32802 :
    checkMaskFor missing32802 StrongPackedBucketN12A4Shard256.record32802 = true := by
  decide

def missing32803 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6417981932277104640
theorem maskCheck32803 :
    checkMaskFor missing32803 StrongPackedBucketN12A4Shard256.record32803 = true := by
  decide

def missing32804 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7030471481599492096
theorem maskCheck32804 :
    checkMaskFor missing32804 StrongPackedBucketN12A4Shard256.record32804 = true := by
  decide

def missing32805 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7138557872656384000
theorem maskCheck32805 :
    checkMaskFor missing32805 StrongPackedBucketN12A4Shard256.record32805 = true := by
  decide

def missing32806 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7282673060732239872
theorem maskCheck32806 :
    checkMaskFor missing32806 StrongPackedBucketN12A4Shard256.record32806 = true := by
  decide

def missing32807 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7570903436883951616
theorem maskCheck32807 :
    checkMaskFor missing32807 StrongPackedBucketN12A4Shard256.record32807 = true := by
  decide

def missing32808 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9480429678889041920
theorem maskCheck32808 :
    checkMaskFor missing32808 StrongPackedBucketN12A4Shard256.record32808 = true := by
  decide

def missing32809 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9696602461002825728
theorem maskCheck32809 :
    checkMaskFor missing32809 StrongPackedBucketN12A4Shard256.record32809 = true := by
  decide

def missing32810 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9732631258021789696
theorem maskCheck32810 :
    checkMaskFor missing32810 StrongPackedBucketN12A4Shard256.record32810 = true := by
  decide

def missing32811 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9984832837154537472
theorem maskCheck32811 :
    checkMaskFor missing32811 StrongPackedBucketN12A4Shard256.record32811 = true := by
  decide

def missing32812 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10020861634173501440
theorem maskCheck32812 :
    checkMaskFor missing32812 StrongPackedBucketN12A4Shard256.record32812 = true := by
  decide

def missing32813 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10237034416287285248
theorem maskCheck32813 :
    checkMaskFor missing32813 StrongPackedBucketN12A4Shard256.record32813 = true := by
  decide

def missing32814 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11101725544742420480
theorem maskCheck32814 :
    checkMaskFor missing32814 StrongPackedBucketN12A4Shard256.record32814 = true := by
  decide

def missing32815 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11714215094064807936
theorem maskCheck32815 :
    checkMaskFor missing32815 StrongPackedBucketN12A4Shard256.record32815 = true := by
  decide

def missing32816 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11750243891083771904
theorem maskCheck32816 :
    checkMaskFor missing32816 StrongPackedBucketN12A4Shard256.record32816 = true := by
  decide

def missing32817 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11966416673197555712
theorem maskCheck32817 :
    checkMaskFor missing32817 StrongPackedBucketN12A4Shard256.record32817 = true := by
  decide

def missing32818 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12254647049349267456
theorem maskCheck32818 :
    checkMaskFor missing32818 StrongPackedBucketN12A4Shard256.record32818 = true := by
  decide

def missing32819 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14056086900297465856
theorem maskCheck32819 :
    checkMaskFor missing32819 StrongPackedBucketN12A4Shard256.record32819 = true := by
  decide

def missing32820 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18703801715743817728
theorem maskCheck32820 :
    checkMaskFor missing32820 StrongPackedBucketN12A4Shard256.record32820 = true := by
  decide

def missing32821 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18847916903819673600
theorem maskCheck32821 :
    checkMaskFor missing32821 StrongPackedBucketN12A4Shard256.record32821 = true := by
  decide

def missing32822 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18919974497857601536
theorem maskCheck32822 :
    checkMaskFor missing32822 StrongPackedBucketN12A4Shard256.record32822 = true := by
  decide

def missing32823 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18956003294876565504
theorem maskCheck32823 :
    checkMaskFor missing32823 StrongPackedBucketN12A4Shard256.record32823 = true := by
  decide

def missing32824 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19136147279971385344
theorem maskCheck32824 :
    checkMaskFor missing32824 StrongPackedBucketN12A4Shard256.record32824 = true := by
  decide

def missing32825 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19208204874009313280
theorem maskCheck32825 :
    checkMaskFor missing32825 StrongPackedBucketN12A4Shard256.record32825 = true := by
  decide

def missing32826 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19244233671028277248
theorem maskCheck32826 :
    checkMaskFor missing32826 StrongPackedBucketN12A4Shard256.record32826 = true := by
  decide

def missing32827 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19352320062085169152
theorem maskCheck32827 :
    checkMaskFor missing32827 StrongPackedBucketN12A4Shard256.record32827 = true := by
  decide

def missing32828 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19388348859104133120
theorem maskCheck32828 :
    checkMaskFor missing32828 StrongPackedBucketN12A4Shard256.record32828 = true := by
  decide

def missing32829 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19460406453142061056
theorem maskCheck32829 :
    checkMaskFor missing32829 StrongPackedBucketN12A4Shard256.record32829 = true := by
  decide

def missing32830 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20217011190540304384
theorem maskCheck32830 :
    checkMaskFor missing32830 StrongPackedBucketN12A4Shard256.record32830 = true := by
  decide

def missing32831 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20253039987559268352
theorem maskCheck32831 :
    checkMaskFor missing32831 StrongPackedBucketN12A4Shard256.record32831 = true := by
  decide

def missing32832 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20325097581597196288
theorem maskCheck32832 :
    checkMaskFor missing32832 StrongPackedBucketN12A4Shard256.record32832 = true := by
  decide

def missing32833 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20469212769673052160
theorem maskCheck32833 :
    checkMaskFor missing32833 StrongPackedBucketN12A4Shard256.record32833 = true := by
  decide

def missing32834 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20865529536881655808
theorem maskCheck32834 :
    checkMaskFor missing32834 StrongPackedBucketN12A4Shard256.record32834 = true := by
  decide

def missing32835 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20937587130919583744
theorem maskCheck32835 :
    checkMaskFor missing32835 StrongPackedBucketN12A4Shard256.record32835 = true := by
  decide

def missing32836 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20973615927938547712
theorem maskCheck32836 :
    checkMaskFor missing32836 StrongPackedBucketN12A4Shard256.record32836 = true := by
  decide

def missing32837 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21081702318995439616
theorem maskCheck32837 :
    checkMaskFor missing32837 StrongPackedBucketN12A4Shard256.record32837 = true := by
  decide

def missing32838 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21117731116014403584
theorem maskCheck32838 :
    checkMaskFor missing32838 StrongPackedBucketN12A4Shard256.record32838 = true := by
  decide

def missing32839 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21189788710052331520
theorem maskCheck32839 :
    checkMaskFor missing32839 StrongPackedBucketN12A4Shard256.record32839 = true := by
  decide

def missing32840 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21369932695147151360
theorem maskCheck32840 :
    checkMaskFor missing32840 StrongPackedBucketN12A4Shard256.record32840 = true := by
  decide

def missing32841 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21405961492166115328
theorem maskCheck32841 :
    checkMaskFor missing32841 StrongPackedBucketN12A4Shard256.record32841 = true := by
  decide

def missing32842 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21478019086204043264
theorem maskCheck32842 :
    checkMaskFor missing32842 StrongPackedBucketN12A4Shard256.record32842 = true := by
  decide

def missing32843 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21622134274279899136
theorem maskCheck32843 :
    checkMaskFor missing32843 StrongPackedBucketN12A4Shard256.record32843 = true := by
  decide

def missing32844 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22486825402735034368
theorem maskCheck32844 :
    checkMaskFor missing32844 StrongPackedBucketN12A4Shard256.record32844 = true := by
  decide

def missing32845 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23171372546095349760
theorem maskCheck32845 :
    checkMaskFor missing32845 StrongPackedBucketN12A4Shard256.record32845 = true := by
  decide

def missing32846 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23279458937152241664
theorem maskCheck32846 :
    checkMaskFor missing32846 StrongPackedBucketN12A4Shard256.record32846 = true := by
  decide

def missing32847 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23423574125228097536
theorem maskCheck32847 :
    checkMaskFor missing32847 StrongPackedBucketN12A4Shard256.record32847 = true := by
  decide

def missing32848 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23711804501379809280
theorem maskCheck32848 :
    checkMaskFor missing32848 StrongPackedBucketN12A4Shard256.record32848 = true := by
  decide

def missing32849 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25441186758290079744
theorem maskCheck32849 :
    checkMaskFor missing32849 StrongPackedBucketN12A4Shard256.record32849 = true := by
  decide

def missing32850 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27855116158560665600
theorem maskCheck32850 :
    checkMaskFor missing32850 StrongPackedBucketN12A4Shard256.record32850 = true := by
  decide

def missing32851 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27891144955579629568
theorem maskCheck32851 :
    checkMaskFor missing32851 StrongPackedBucketN12A4Shard256.record32851 = true := by
  decide

def missing32852 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28107317737693413376
theorem maskCheck32852 :
    checkMaskFor missing32852 StrongPackedBucketN12A4Shard256.record32852 = true := by
  decide

def missing32853 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28395548113845125120
theorem maskCheck32853 :
    checkMaskFor missing32853 StrongPackedBucketN12A4Shard256.record32853 = true := by
  decide

def missing32854 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30124930370755395584
theorem maskCheck32854 :
    checkMaskFor missing32854 StrongPackedBucketN12A4Shard256.record32854 = true := by
  decide

def missing32855 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41726203010861793280
theorem maskCheck32855 :
    checkMaskFor missing32855 StrongPackedBucketN12A4Shard256.record32855 = true := by
  decide

def missing32856 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41870318198937649152
theorem maskCheck32856 :
    checkMaskFor missing32856 StrongPackedBucketN12A4Shard256.record32856 = true := by
  decide

def missing32857 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43887930831999631360
theorem maskCheck32857 :
    checkMaskFor missing32857 StrongPackedBucketN12A4Shard256.record32857 = true := by
  decide

def missing32858 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46337889029289181184
theorem maskCheck32858 :
    checkMaskFor missing32858 StrongPackedBucketN12A4Shard256.record32858 = true := by
  decide

def missing32859 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46554061811402964992
theorem maskCheck32859 :
    checkMaskFor missing32859 StrongPackedBucketN12A4Shard256.record32859 = true := by
  decide

def missing32860 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48571674444464947200
theorem maskCheck32860 :
    checkMaskFor missing32860 StrongPackedBucketN12A4Shard256.record32860 = true := by
  decide

def missing32861 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 545569493162688512
theorem maskCheck32861 :
    checkMaskFor missing32861 StrongPackedBucketN12A4Shard256.record32861 = true := by
  decide

def missing32862 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 833799869314400256
theorem maskCheck32862 :
    checkMaskFor missing32862 StrongPackedBucketN12A4Shard256.record32862 = true := by
  decide

def missing32863 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 977915057390256128
theorem maskCheck32863 :
    checkMaskFor missing32863 StrongPackedBucketN12A4Shard256.record32863 = true := by
  decide

def missing32864 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1049972651428184064
theorem maskCheck32864 :
    checkMaskFor missing32864 StrongPackedBucketN12A4Shard256.record32864 = true := by
  decide

def missing32865 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1086001448447148032
theorem maskCheck32865 :
    checkMaskFor missing32865 StrongPackedBucketN12A4Shard256.record32865 = true := by
  decide

def missing32866 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1410260621617823744
theorem maskCheck32866 :
    checkMaskFor missing32866 StrongPackedBucketN12A4Shard256.record32866 = true := by
  decide

def missing32867 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1554375809693679616
theorem maskCheck32867 :
    checkMaskFor missing32867 StrongPackedBucketN12A4Shard256.record32867 = true := by
  decide

def missing32868 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1626433403731607552
theorem maskCheck32868 :
    checkMaskFor missing32868 StrongPackedBucketN12A4Shard256.record32868 = true := by
  decide

def missing32869 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1662462200750571520
theorem maskCheck32869 :
    checkMaskFor missing32869 StrongPackedBucketN12A4Shard256.record32869 = true := by
  decide

def missing32870 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1842606185845391360
theorem maskCheck32870 :
    checkMaskFor missing32870 StrongPackedBucketN12A4Shard256.record32870 = true := by
  decide

def missing32871 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1914663779883319296
theorem maskCheck32871 :
    checkMaskFor missing32871 StrongPackedBucketN12A4Shard256.record32871 = true := by
  decide

def missing32872 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1950692576902283264
theorem maskCheck32872 :
    checkMaskFor missing32872 StrongPackedBucketN12A4Shard256.record32872 = true := by
  decide

def missing32873 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2058778967959175168
theorem maskCheck32873 :
    checkMaskFor missing32873 StrongPackedBucketN12A4Shard256.record32873 = true := by
  decide

def missing32874 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2094807764978139136
theorem maskCheck32874 :
    checkMaskFor missing32874 StrongPackedBucketN12A4Shard256.record32874 = true := by
  decide

def missing32875 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2166865359016067072
theorem maskCheck32875 :
    checkMaskFor missing32875 StrongPackedBucketN12A4Shard256.record32875 = true := by
  decide

def missing32876 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2563182126224670720
theorem maskCheck32876 :
    checkMaskFor missing32876 StrongPackedBucketN12A4Shard256.record32876 = true := by
  decide

def missing32877 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2707297314300526592
theorem maskCheck32877 :
    checkMaskFor missing32877 StrongPackedBucketN12A4Shard256.record32877 = true := by
  decide

def missing32878 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2779354908338454528
theorem maskCheck32878 :
    checkMaskFor missing32878 StrongPackedBucketN12A4Shard256.record32878 = true := by
  decide

def missing32879 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2815383705357418496
theorem maskCheck32879 :
    checkMaskFor missing32879 StrongPackedBucketN12A4Shard256.record32879 = true := by
  decide

def missing32880 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2995527690452238336
theorem maskCheck32880 :
    checkMaskFor missing32880 StrongPackedBucketN12A4Shard256.record32880 = true := by
  decide

def missing32881 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3067585284490166272
theorem maskCheck32881 :
    checkMaskFor missing32881 StrongPackedBucketN12A4Shard256.record32881 = true := by
  decide

def missing32882 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3211700472566022144
theorem maskCheck32882 :
    checkMaskFor missing32882 StrongPackedBucketN12A4Shard256.record32882 = true := by
  decide

def missing32883 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3247729269584986112
theorem maskCheck32883 :
    checkMaskFor missing32883 StrongPackedBucketN12A4Shard256.record32883 = true := by
  decide

def missing32884 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3319786863622914048
theorem maskCheck32884 :
    checkMaskFor missing32884 StrongPackedBucketN12A4Shard256.record32884 = true := by
  decide

def missing32885 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3571988442755661824
theorem maskCheck32885 :
    checkMaskFor missing32885 StrongPackedBucketN12A4Shard256.record32885 = true := by
  decide

def missing32886 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3644046036793589760
theorem maskCheck32886 :
    checkMaskFor missing32886 StrongPackedBucketN12A4Shard256.record32886 = true := by
  decide

def missing32887 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3788161224869445632
theorem maskCheck32887 :
    checkMaskFor missing32887 StrongPackedBucketN12A4Shard256.record32887 = true := by
  decide

def missing32888 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3824190021888409600
theorem maskCheck32888 :
    checkMaskFor missing32888 StrongPackedBucketN12A4Shard256.record32888 = true := by
  decide

def missing32889 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3896247615926337536
theorem maskCheck32889 :
    checkMaskFor missing32889 StrongPackedBucketN12A4Shard256.record32889 = true := by
  decide

def missing32890 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4076391601021157376
theorem maskCheck32890 :
    checkMaskFor missing32890 StrongPackedBucketN12A4Shard256.record32890 = true := by
  decide

def missing32891 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4328593180153905152
theorem maskCheck32891 :
    checkMaskFor missing32891 StrongPackedBucketN12A4Shard256.record32891 = true := by
  decide

def missing32892 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4869025135438364672
theorem maskCheck32892 :
    checkMaskFor missing32892 StrongPackedBucketN12A4Shard256.record32892 = true := by
  decide

def missing32893 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5013140323514220544
theorem maskCheck32893 :
    checkMaskFor missing32893 StrongPackedBucketN12A4Shard256.record32893 = true := by
  decide

def missing32894 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5121226714571112448
theorem maskCheck32894 :
    checkMaskFor missing32894 StrongPackedBucketN12A4Shard256.record32894 = true := by
  decide

def missing32895 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5301370699665932288
theorem maskCheck32895 :
    checkMaskFor missing32895 StrongPackedBucketN12A4Shard256.record32895 = true := by
  decide

def missing32768_32769 : List (BitVec (edgeCount 12)) :=
  [missing32768]
abbrev records32768_32769 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32768]
theorem aligned32768_32769 :
    AlignedValid 12 4 missing32768_32769 records32768_32769 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32768
    maskCheck32768 AlignedValid.nil

def missing32769_32770 : List (BitVec (edgeCount 12)) :=
  [missing32769]
abbrev records32769_32770 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32769]
theorem aligned32769_32770 :
    AlignedValid 12 4 missing32769_32770 records32769_32770 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32769
    maskCheck32769 AlignedValid.nil

def missing32768_32770 : List (BitVec (edgeCount 12)) :=
  missing32768_32769 ++ missing32769_32770
abbrev records32768_32770 : List Blob :=
  records32768_32769 ++ records32769_32770
theorem aligned32768_32770 :
    AlignedValid 12 4 missing32768_32770 records32768_32770 :=
  aligned32768_32769.append aligned32769_32770

def missing32770_32771 : List (BitVec (edgeCount 12)) :=
  [missing32770]
abbrev records32770_32771 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32770]
theorem aligned32770_32771 :
    AlignedValid 12 4 missing32770_32771 records32770_32771 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32770
    maskCheck32770 AlignedValid.nil

def missing32771_32772 : List (BitVec (edgeCount 12)) :=
  [missing32771]
abbrev records32771_32772 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32771]
theorem aligned32771_32772 :
    AlignedValid 12 4 missing32771_32772 records32771_32772 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32771
    maskCheck32771 AlignedValid.nil

def missing32770_32772 : List (BitVec (edgeCount 12)) :=
  missing32770_32771 ++ missing32771_32772
abbrev records32770_32772 : List Blob :=
  records32770_32771 ++ records32771_32772
theorem aligned32770_32772 :
    AlignedValid 12 4 missing32770_32772 records32770_32772 :=
  aligned32770_32771.append aligned32771_32772

def missing32768_32772 : List (BitVec (edgeCount 12)) :=
  missing32768_32770 ++ missing32770_32772
abbrev records32768_32772 : List Blob :=
  records32768_32770 ++ records32770_32772
theorem aligned32768_32772 :
    AlignedValid 12 4 missing32768_32772 records32768_32772 :=
  aligned32768_32770.append aligned32770_32772

def missing32772_32773 : List (BitVec (edgeCount 12)) :=
  [missing32772]
abbrev records32772_32773 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32772]
theorem aligned32772_32773 :
    AlignedValid 12 4 missing32772_32773 records32772_32773 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32772
    maskCheck32772 AlignedValid.nil

def missing32773_32774 : List (BitVec (edgeCount 12)) :=
  [missing32773]
abbrev records32773_32774 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32773]
theorem aligned32773_32774 :
    AlignedValid 12 4 missing32773_32774 records32773_32774 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32773
    maskCheck32773 AlignedValid.nil

def missing32772_32774 : List (BitVec (edgeCount 12)) :=
  missing32772_32773 ++ missing32773_32774
abbrev records32772_32774 : List Blob :=
  records32772_32773 ++ records32773_32774
theorem aligned32772_32774 :
    AlignedValid 12 4 missing32772_32774 records32772_32774 :=
  aligned32772_32773.append aligned32773_32774

def missing32774_32775 : List (BitVec (edgeCount 12)) :=
  [missing32774]
abbrev records32774_32775 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32774]
theorem aligned32774_32775 :
    AlignedValid 12 4 missing32774_32775 records32774_32775 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32774
    maskCheck32774 AlignedValid.nil

def missing32775_32776 : List (BitVec (edgeCount 12)) :=
  [missing32775]
abbrev records32775_32776 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32775]
theorem aligned32775_32776 :
    AlignedValid 12 4 missing32775_32776 records32775_32776 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32775
    maskCheck32775 AlignedValid.nil

def missing32774_32776 : List (BitVec (edgeCount 12)) :=
  missing32774_32775 ++ missing32775_32776
abbrev records32774_32776 : List Blob :=
  records32774_32775 ++ records32775_32776
theorem aligned32774_32776 :
    AlignedValid 12 4 missing32774_32776 records32774_32776 :=
  aligned32774_32775.append aligned32775_32776

def missing32772_32776 : List (BitVec (edgeCount 12)) :=
  missing32772_32774 ++ missing32774_32776
abbrev records32772_32776 : List Blob :=
  records32772_32774 ++ records32774_32776
theorem aligned32772_32776 :
    AlignedValid 12 4 missing32772_32776 records32772_32776 :=
  aligned32772_32774.append aligned32774_32776

def missing32768_32776 : List (BitVec (edgeCount 12)) :=
  missing32768_32772 ++ missing32772_32776
abbrev records32768_32776 : List Blob :=
  records32768_32772 ++ records32772_32776
theorem aligned32768_32776 :
    AlignedValid 12 4 missing32768_32776 records32768_32776 :=
  aligned32768_32772.append aligned32772_32776

def missing32776_32777 : List (BitVec (edgeCount 12)) :=
  [missing32776]
abbrev records32776_32777 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32776]
theorem aligned32776_32777 :
    AlignedValid 12 4 missing32776_32777 records32776_32777 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32776
    maskCheck32776 AlignedValid.nil

def missing32777_32778 : List (BitVec (edgeCount 12)) :=
  [missing32777]
abbrev records32777_32778 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32777]
theorem aligned32777_32778 :
    AlignedValid 12 4 missing32777_32778 records32777_32778 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32777
    maskCheck32777 AlignedValid.nil

def missing32776_32778 : List (BitVec (edgeCount 12)) :=
  missing32776_32777 ++ missing32777_32778
abbrev records32776_32778 : List Blob :=
  records32776_32777 ++ records32777_32778
theorem aligned32776_32778 :
    AlignedValid 12 4 missing32776_32778 records32776_32778 :=
  aligned32776_32777.append aligned32777_32778

def missing32778_32779 : List (BitVec (edgeCount 12)) :=
  [missing32778]
abbrev records32778_32779 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32778]
theorem aligned32778_32779 :
    AlignedValid 12 4 missing32778_32779 records32778_32779 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32778
    maskCheck32778 AlignedValid.nil

def missing32779_32780 : List (BitVec (edgeCount 12)) :=
  [missing32779]
abbrev records32779_32780 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32779]
theorem aligned32779_32780 :
    AlignedValid 12 4 missing32779_32780 records32779_32780 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32779
    maskCheck32779 AlignedValid.nil

def missing32778_32780 : List (BitVec (edgeCount 12)) :=
  missing32778_32779 ++ missing32779_32780
abbrev records32778_32780 : List Blob :=
  records32778_32779 ++ records32779_32780
theorem aligned32778_32780 :
    AlignedValid 12 4 missing32778_32780 records32778_32780 :=
  aligned32778_32779.append aligned32779_32780

def missing32776_32780 : List (BitVec (edgeCount 12)) :=
  missing32776_32778 ++ missing32778_32780
abbrev records32776_32780 : List Blob :=
  records32776_32778 ++ records32778_32780
theorem aligned32776_32780 :
    AlignedValid 12 4 missing32776_32780 records32776_32780 :=
  aligned32776_32778.append aligned32778_32780

def missing32780_32781 : List (BitVec (edgeCount 12)) :=
  [missing32780]
abbrev records32780_32781 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32780]
theorem aligned32780_32781 :
    AlignedValid 12 4 missing32780_32781 records32780_32781 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32780
    maskCheck32780 AlignedValid.nil

def missing32781_32782 : List (BitVec (edgeCount 12)) :=
  [missing32781]
abbrev records32781_32782 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32781]
theorem aligned32781_32782 :
    AlignedValid 12 4 missing32781_32782 records32781_32782 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32781
    maskCheck32781 AlignedValid.nil

def missing32780_32782 : List (BitVec (edgeCount 12)) :=
  missing32780_32781 ++ missing32781_32782
abbrev records32780_32782 : List Blob :=
  records32780_32781 ++ records32781_32782
theorem aligned32780_32782 :
    AlignedValid 12 4 missing32780_32782 records32780_32782 :=
  aligned32780_32781.append aligned32781_32782

def missing32782_32783 : List (BitVec (edgeCount 12)) :=
  [missing32782]
abbrev records32782_32783 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32782]
theorem aligned32782_32783 :
    AlignedValid 12 4 missing32782_32783 records32782_32783 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32782
    maskCheck32782 AlignedValid.nil

def missing32783_32784 : List (BitVec (edgeCount 12)) :=
  [missing32783]
abbrev records32783_32784 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32783]
theorem aligned32783_32784 :
    AlignedValid 12 4 missing32783_32784 records32783_32784 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32783
    maskCheck32783 AlignedValid.nil

def missing32782_32784 : List (BitVec (edgeCount 12)) :=
  missing32782_32783 ++ missing32783_32784
abbrev records32782_32784 : List Blob :=
  records32782_32783 ++ records32783_32784
theorem aligned32782_32784 :
    AlignedValid 12 4 missing32782_32784 records32782_32784 :=
  aligned32782_32783.append aligned32783_32784

def missing32780_32784 : List (BitVec (edgeCount 12)) :=
  missing32780_32782 ++ missing32782_32784
abbrev records32780_32784 : List Blob :=
  records32780_32782 ++ records32782_32784
theorem aligned32780_32784 :
    AlignedValid 12 4 missing32780_32784 records32780_32784 :=
  aligned32780_32782.append aligned32782_32784

def missing32776_32784 : List (BitVec (edgeCount 12)) :=
  missing32776_32780 ++ missing32780_32784
abbrev records32776_32784 : List Blob :=
  records32776_32780 ++ records32780_32784
theorem aligned32776_32784 :
    AlignedValid 12 4 missing32776_32784 records32776_32784 :=
  aligned32776_32780.append aligned32780_32784

def missing32768_32784 : List (BitVec (edgeCount 12)) :=
  missing32768_32776 ++ missing32776_32784
abbrev records32768_32784 : List Blob :=
  records32768_32776 ++ records32776_32784
theorem aligned32768_32784 :
    AlignedValid 12 4 missing32768_32784 records32768_32784 :=
  aligned32768_32776.append aligned32776_32784

def missing32784_32785 : List (BitVec (edgeCount 12)) :=
  [missing32784]
abbrev records32784_32785 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32784]
theorem aligned32784_32785 :
    AlignedValid 12 4 missing32784_32785 records32784_32785 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32784
    maskCheck32784 AlignedValid.nil

def missing32785_32786 : List (BitVec (edgeCount 12)) :=
  [missing32785]
abbrev records32785_32786 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32785]
theorem aligned32785_32786 :
    AlignedValid 12 4 missing32785_32786 records32785_32786 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32785
    maskCheck32785 AlignedValid.nil

def missing32784_32786 : List (BitVec (edgeCount 12)) :=
  missing32784_32785 ++ missing32785_32786
abbrev records32784_32786 : List Blob :=
  records32784_32785 ++ records32785_32786
theorem aligned32784_32786 :
    AlignedValid 12 4 missing32784_32786 records32784_32786 :=
  aligned32784_32785.append aligned32785_32786

def missing32786_32787 : List (BitVec (edgeCount 12)) :=
  [missing32786]
abbrev records32786_32787 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32786]
theorem aligned32786_32787 :
    AlignedValid 12 4 missing32786_32787 records32786_32787 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32786
    maskCheck32786 AlignedValid.nil

def missing32787_32788 : List (BitVec (edgeCount 12)) :=
  [missing32787]
abbrev records32787_32788 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32787]
theorem aligned32787_32788 :
    AlignedValid 12 4 missing32787_32788 records32787_32788 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32787
    maskCheck32787 AlignedValid.nil

def missing32786_32788 : List (BitVec (edgeCount 12)) :=
  missing32786_32787 ++ missing32787_32788
abbrev records32786_32788 : List Blob :=
  records32786_32787 ++ records32787_32788
theorem aligned32786_32788 :
    AlignedValid 12 4 missing32786_32788 records32786_32788 :=
  aligned32786_32787.append aligned32787_32788

def missing32784_32788 : List (BitVec (edgeCount 12)) :=
  missing32784_32786 ++ missing32786_32788
abbrev records32784_32788 : List Blob :=
  records32784_32786 ++ records32786_32788
theorem aligned32784_32788 :
    AlignedValid 12 4 missing32784_32788 records32784_32788 :=
  aligned32784_32786.append aligned32786_32788

def missing32788_32789 : List (BitVec (edgeCount 12)) :=
  [missing32788]
abbrev records32788_32789 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32788]
theorem aligned32788_32789 :
    AlignedValid 12 4 missing32788_32789 records32788_32789 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32788
    maskCheck32788 AlignedValid.nil

def missing32789_32790 : List (BitVec (edgeCount 12)) :=
  [missing32789]
abbrev records32789_32790 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32789]
theorem aligned32789_32790 :
    AlignedValid 12 4 missing32789_32790 records32789_32790 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32789
    maskCheck32789 AlignedValid.nil

def missing32788_32790 : List (BitVec (edgeCount 12)) :=
  missing32788_32789 ++ missing32789_32790
abbrev records32788_32790 : List Blob :=
  records32788_32789 ++ records32789_32790
theorem aligned32788_32790 :
    AlignedValid 12 4 missing32788_32790 records32788_32790 :=
  aligned32788_32789.append aligned32789_32790

def missing32790_32791 : List (BitVec (edgeCount 12)) :=
  [missing32790]
abbrev records32790_32791 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32790]
theorem aligned32790_32791 :
    AlignedValid 12 4 missing32790_32791 records32790_32791 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32790
    maskCheck32790 AlignedValid.nil

def missing32791_32792 : List (BitVec (edgeCount 12)) :=
  [missing32791]
abbrev records32791_32792 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32791]
theorem aligned32791_32792 :
    AlignedValid 12 4 missing32791_32792 records32791_32792 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32791
    maskCheck32791 AlignedValid.nil

def missing32790_32792 : List (BitVec (edgeCount 12)) :=
  missing32790_32791 ++ missing32791_32792
abbrev records32790_32792 : List Blob :=
  records32790_32791 ++ records32791_32792
theorem aligned32790_32792 :
    AlignedValid 12 4 missing32790_32792 records32790_32792 :=
  aligned32790_32791.append aligned32791_32792

def missing32788_32792 : List (BitVec (edgeCount 12)) :=
  missing32788_32790 ++ missing32790_32792
abbrev records32788_32792 : List Blob :=
  records32788_32790 ++ records32790_32792
theorem aligned32788_32792 :
    AlignedValid 12 4 missing32788_32792 records32788_32792 :=
  aligned32788_32790.append aligned32790_32792

def missing32784_32792 : List (BitVec (edgeCount 12)) :=
  missing32784_32788 ++ missing32788_32792
abbrev records32784_32792 : List Blob :=
  records32784_32788 ++ records32788_32792
theorem aligned32784_32792 :
    AlignedValid 12 4 missing32784_32792 records32784_32792 :=
  aligned32784_32788.append aligned32788_32792

def missing32792_32793 : List (BitVec (edgeCount 12)) :=
  [missing32792]
abbrev records32792_32793 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32792]
theorem aligned32792_32793 :
    AlignedValid 12 4 missing32792_32793 records32792_32793 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32792
    maskCheck32792 AlignedValid.nil

def missing32793_32794 : List (BitVec (edgeCount 12)) :=
  [missing32793]
abbrev records32793_32794 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32793]
theorem aligned32793_32794 :
    AlignedValid 12 4 missing32793_32794 records32793_32794 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32793
    maskCheck32793 AlignedValid.nil

def missing32792_32794 : List (BitVec (edgeCount 12)) :=
  missing32792_32793 ++ missing32793_32794
abbrev records32792_32794 : List Blob :=
  records32792_32793 ++ records32793_32794
theorem aligned32792_32794 :
    AlignedValid 12 4 missing32792_32794 records32792_32794 :=
  aligned32792_32793.append aligned32793_32794

def missing32794_32795 : List (BitVec (edgeCount 12)) :=
  [missing32794]
abbrev records32794_32795 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32794]
theorem aligned32794_32795 :
    AlignedValid 12 4 missing32794_32795 records32794_32795 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32794
    maskCheck32794 AlignedValid.nil

def missing32795_32796 : List (BitVec (edgeCount 12)) :=
  [missing32795]
abbrev records32795_32796 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32795]
theorem aligned32795_32796 :
    AlignedValid 12 4 missing32795_32796 records32795_32796 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32795
    maskCheck32795 AlignedValid.nil

def missing32794_32796 : List (BitVec (edgeCount 12)) :=
  missing32794_32795 ++ missing32795_32796
abbrev records32794_32796 : List Blob :=
  records32794_32795 ++ records32795_32796
theorem aligned32794_32796 :
    AlignedValid 12 4 missing32794_32796 records32794_32796 :=
  aligned32794_32795.append aligned32795_32796

def missing32792_32796 : List (BitVec (edgeCount 12)) :=
  missing32792_32794 ++ missing32794_32796
abbrev records32792_32796 : List Blob :=
  records32792_32794 ++ records32794_32796
theorem aligned32792_32796 :
    AlignedValid 12 4 missing32792_32796 records32792_32796 :=
  aligned32792_32794.append aligned32794_32796

def missing32796_32797 : List (BitVec (edgeCount 12)) :=
  [missing32796]
abbrev records32796_32797 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32796]
theorem aligned32796_32797 :
    AlignedValid 12 4 missing32796_32797 records32796_32797 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32796
    maskCheck32796 AlignedValid.nil

def missing32797_32798 : List (BitVec (edgeCount 12)) :=
  [missing32797]
abbrev records32797_32798 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32797]
theorem aligned32797_32798 :
    AlignedValid 12 4 missing32797_32798 records32797_32798 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32797
    maskCheck32797 AlignedValid.nil

def missing32796_32798 : List (BitVec (edgeCount 12)) :=
  missing32796_32797 ++ missing32797_32798
abbrev records32796_32798 : List Blob :=
  records32796_32797 ++ records32797_32798
theorem aligned32796_32798 :
    AlignedValid 12 4 missing32796_32798 records32796_32798 :=
  aligned32796_32797.append aligned32797_32798

def missing32798_32799 : List (BitVec (edgeCount 12)) :=
  [missing32798]
abbrev records32798_32799 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32798]
theorem aligned32798_32799 :
    AlignedValid 12 4 missing32798_32799 records32798_32799 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32798
    maskCheck32798 AlignedValid.nil

def missing32799_32800 : List (BitVec (edgeCount 12)) :=
  [missing32799]
abbrev records32799_32800 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32799]
theorem aligned32799_32800 :
    AlignedValid 12 4 missing32799_32800 records32799_32800 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32799
    maskCheck32799 AlignedValid.nil

def missing32798_32800 : List (BitVec (edgeCount 12)) :=
  missing32798_32799 ++ missing32799_32800
abbrev records32798_32800 : List Blob :=
  records32798_32799 ++ records32799_32800
theorem aligned32798_32800 :
    AlignedValid 12 4 missing32798_32800 records32798_32800 :=
  aligned32798_32799.append aligned32799_32800

def missing32796_32800 : List (BitVec (edgeCount 12)) :=
  missing32796_32798 ++ missing32798_32800
abbrev records32796_32800 : List Blob :=
  records32796_32798 ++ records32798_32800
theorem aligned32796_32800 :
    AlignedValid 12 4 missing32796_32800 records32796_32800 :=
  aligned32796_32798.append aligned32798_32800

def missing32792_32800 : List (BitVec (edgeCount 12)) :=
  missing32792_32796 ++ missing32796_32800
abbrev records32792_32800 : List Blob :=
  records32792_32796 ++ records32796_32800
theorem aligned32792_32800 :
    AlignedValid 12 4 missing32792_32800 records32792_32800 :=
  aligned32792_32796.append aligned32796_32800

def missing32784_32800 : List (BitVec (edgeCount 12)) :=
  missing32784_32792 ++ missing32792_32800
abbrev records32784_32800 : List Blob :=
  records32784_32792 ++ records32792_32800
theorem aligned32784_32800 :
    AlignedValid 12 4 missing32784_32800 records32784_32800 :=
  aligned32784_32792.append aligned32792_32800

def missing32768_32800 : List (BitVec (edgeCount 12)) :=
  missing32768_32784 ++ missing32784_32800
abbrev records32768_32800 : List Blob :=
  records32768_32784 ++ records32784_32800
theorem aligned32768_32800 :
    AlignedValid 12 4 missing32768_32800 records32768_32800 :=
  aligned32768_32784.append aligned32784_32800

def missing32800_32801 : List (BitVec (edgeCount 12)) :=
  [missing32800]
abbrev records32800_32801 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32800]
theorem aligned32800_32801 :
    AlignedValid 12 4 missing32800_32801 records32800_32801 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32800
    maskCheck32800 AlignedValid.nil

def missing32801_32802 : List (BitVec (edgeCount 12)) :=
  [missing32801]
abbrev records32801_32802 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32801]
theorem aligned32801_32802 :
    AlignedValid 12 4 missing32801_32802 records32801_32802 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32801
    maskCheck32801 AlignedValid.nil

def missing32800_32802 : List (BitVec (edgeCount 12)) :=
  missing32800_32801 ++ missing32801_32802
abbrev records32800_32802 : List Blob :=
  records32800_32801 ++ records32801_32802
theorem aligned32800_32802 :
    AlignedValid 12 4 missing32800_32802 records32800_32802 :=
  aligned32800_32801.append aligned32801_32802

def missing32802_32803 : List (BitVec (edgeCount 12)) :=
  [missing32802]
abbrev records32802_32803 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32802]
theorem aligned32802_32803 :
    AlignedValid 12 4 missing32802_32803 records32802_32803 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32802
    maskCheck32802 AlignedValid.nil

def missing32803_32804 : List (BitVec (edgeCount 12)) :=
  [missing32803]
abbrev records32803_32804 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32803]
theorem aligned32803_32804 :
    AlignedValid 12 4 missing32803_32804 records32803_32804 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32803
    maskCheck32803 AlignedValid.nil

def missing32802_32804 : List (BitVec (edgeCount 12)) :=
  missing32802_32803 ++ missing32803_32804
abbrev records32802_32804 : List Blob :=
  records32802_32803 ++ records32803_32804
theorem aligned32802_32804 :
    AlignedValid 12 4 missing32802_32804 records32802_32804 :=
  aligned32802_32803.append aligned32803_32804

def missing32800_32804 : List (BitVec (edgeCount 12)) :=
  missing32800_32802 ++ missing32802_32804
abbrev records32800_32804 : List Blob :=
  records32800_32802 ++ records32802_32804
theorem aligned32800_32804 :
    AlignedValid 12 4 missing32800_32804 records32800_32804 :=
  aligned32800_32802.append aligned32802_32804

def missing32804_32805 : List (BitVec (edgeCount 12)) :=
  [missing32804]
abbrev records32804_32805 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32804]
theorem aligned32804_32805 :
    AlignedValid 12 4 missing32804_32805 records32804_32805 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32804
    maskCheck32804 AlignedValid.nil

def missing32805_32806 : List (BitVec (edgeCount 12)) :=
  [missing32805]
abbrev records32805_32806 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32805]
theorem aligned32805_32806 :
    AlignedValid 12 4 missing32805_32806 records32805_32806 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32805
    maskCheck32805 AlignedValid.nil

def missing32804_32806 : List (BitVec (edgeCount 12)) :=
  missing32804_32805 ++ missing32805_32806
abbrev records32804_32806 : List Blob :=
  records32804_32805 ++ records32805_32806
theorem aligned32804_32806 :
    AlignedValid 12 4 missing32804_32806 records32804_32806 :=
  aligned32804_32805.append aligned32805_32806

def missing32806_32807 : List (BitVec (edgeCount 12)) :=
  [missing32806]
abbrev records32806_32807 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32806]
theorem aligned32806_32807 :
    AlignedValid 12 4 missing32806_32807 records32806_32807 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32806
    maskCheck32806 AlignedValid.nil

def missing32807_32808 : List (BitVec (edgeCount 12)) :=
  [missing32807]
abbrev records32807_32808 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32807]
theorem aligned32807_32808 :
    AlignedValid 12 4 missing32807_32808 records32807_32808 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32807
    maskCheck32807 AlignedValid.nil

def missing32806_32808 : List (BitVec (edgeCount 12)) :=
  missing32806_32807 ++ missing32807_32808
abbrev records32806_32808 : List Blob :=
  records32806_32807 ++ records32807_32808
theorem aligned32806_32808 :
    AlignedValid 12 4 missing32806_32808 records32806_32808 :=
  aligned32806_32807.append aligned32807_32808

def missing32804_32808 : List (BitVec (edgeCount 12)) :=
  missing32804_32806 ++ missing32806_32808
abbrev records32804_32808 : List Blob :=
  records32804_32806 ++ records32806_32808
theorem aligned32804_32808 :
    AlignedValid 12 4 missing32804_32808 records32804_32808 :=
  aligned32804_32806.append aligned32806_32808

def missing32800_32808 : List (BitVec (edgeCount 12)) :=
  missing32800_32804 ++ missing32804_32808
abbrev records32800_32808 : List Blob :=
  records32800_32804 ++ records32804_32808
theorem aligned32800_32808 :
    AlignedValid 12 4 missing32800_32808 records32800_32808 :=
  aligned32800_32804.append aligned32804_32808

def missing32808_32809 : List (BitVec (edgeCount 12)) :=
  [missing32808]
abbrev records32808_32809 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32808]
theorem aligned32808_32809 :
    AlignedValid 12 4 missing32808_32809 records32808_32809 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32808
    maskCheck32808 AlignedValid.nil

def missing32809_32810 : List (BitVec (edgeCount 12)) :=
  [missing32809]
abbrev records32809_32810 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32809]
theorem aligned32809_32810 :
    AlignedValid 12 4 missing32809_32810 records32809_32810 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32809
    maskCheck32809 AlignedValid.nil

def missing32808_32810 : List (BitVec (edgeCount 12)) :=
  missing32808_32809 ++ missing32809_32810
abbrev records32808_32810 : List Blob :=
  records32808_32809 ++ records32809_32810
theorem aligned32808_32810 :
    AlignedValid 12 4 missing32808_32810 records32808_32810 :=
  aligned32808_32809.append aligned32809_32810

def missing32810_32811 : List (BitVec (edgeCount 12)) :=
  [missing32810]
abbrev records32810_32811 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32810]
theorem aligned32810_32811 :
    AlignedValid 12 4 missing32810_32811 records32810_32811 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32810
    maskCheck32810 AlignedValid.nil

def missing32811_32812 : List (BitVec (edgeCount 12)) :=
  [missing32811]
abbrev records32811_32812 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32811]
theorem aligned32811_32812 :
    AlignedValid 12 4 missing32811_32812 records32811_32812 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32811
    maskCheck32811 AlignedValid.nil

def missing32810_32812 : List (BitVec (edgeCount 12)) :=
  missing32810_32811 ++ missing32811_32812
abbrev records32810_32812 : List Blob :=
  records32810_32811 ++ records32811_32812
theorem aligned32810_32812 :
    AlignedValid 12 4 missing32810_32812 records32810_32812 :=
  aligned32810_32811.append aligned32811_32812

def missing32808_32812 : List (BitVec (edgeCount 12)) :=
  missing32808_32810 ++ missing32810_32812
abbrev records32808_32812 : List Blob :=
  records32808_32810 ++ records32810_32812
theorem aligned32808_32812 :
    AlignedValid 12 4 missing32808_32812 records32808_32812 :=
  aligned32808_32810.append aligned32810_32812

def missing32812_32813 : List (BitVec (edgeCount 12)) :=
  [missing32812]
abbrev records32812_32813 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32812]
theorem aligned32812_32813 :
    AlignedValid 12 4 missing32812_32813 records32812_32813 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32812
    maskCheck32812 AlignedValid.nil

def missing32813_32814 : List (BitVec (edgeCount 12)) :=
  [missing32813]
abbrev records32813_32814 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32813]
theorem aligned32813_32814 :
    AlignedValid 12 4 missing32813_32814 records32813_32814 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32813
    maskCheck32813 AlignedValid.nil

def missing32812_32814 : List (BitVec (edgeCount 12)) :=
  missing32812_32813 ++ missing32813_32814
abbrev records32812_32814 : List Blob :=
  records32812_32813 ++ records32813_32814
theorem aligned32812_32814 :
    AlignedValid 12 4 missing32812_32814 records32812_32814 :=
  aligned32812_32813.append aligned32813_32814

def missing32814_32815 : List (BitVec (edgeCount 12)) :=
  [missing32814]
abbrev records32814_32815 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32814]
theorem aligned32814_32815 :
    AlignedValid 12 4 missing32814_32815 records32814_32815 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32814
    maskCheck32814 AlignedValid.nil

def missing32815_32816 : List (BitVec (edgeCount 12)) :=
  [missing32815]
abbrev records32815_32816 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32815]
theorem aligned32815_32816 :
    AlignedValid 12 4 missing32815_32816 records32815_32816 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32815
    maskCheck32815 AlignedValid.nil

def missing32814_32816 : List (BitVec (edgeCount 12)) :=
  missing32814_32815 ++ missing32815_32816
abbrev records32814_32816 : List Blob :=
  records32814_32815 ++ records32815_32816
theorem aligned32814_32816 :
    AlignedValid 12 4 missing32814_32816 records32814_32816 :=
  aligned32814_32815.append aligned32815_32816

def missing32812_32816 : List (BitVec (edgeCount 12)) :=
  missing32812_32814 ++ missing32814_32816
abbrev records32812_32816 : List Blob :=
  records32812_32814 ++ records32814_32816
theorem aligned32812_32816 :
    AlignedValid 12 4 missing32812_32816 records32812_32816 :=
  aligned32812_32814.append aligned32814_32816

def missing32808_32816 : List (BitVec (edgeCount 12)) :=
  missing32808_32812 ++ missing32812_32816
abbrev records32808_32816 : List Blob :=
  records32808_32812 ++ records32812_32816
theorem aligned32808_32816 :
    AlignedValid 12 4 missing32808_32816 records32808_32816 :=
  aligned32808_32812.append aligned32812_32816

def missing32800_32816 : List (BitVec (edgeCount 12)) :=
  missing32800_32808 ++ missing32808_32816
abbrev records32800_32816 : List Blob :=
  records32800_32808 ++ records32808_32816
theorem aligned32800_32816 :
    AlignedValid 12 4 missing32800_32816 records32800_32816 :=
  aligned32800_32808.append aligned32808_32816

def missing32816_32817 : List (BitVec (edgeCount 12)) :=
  [missing32816]
abbrev records32816_32817 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32816]
theorem aligned32816_32817 :
    AlignedValid 12 4 missing32816_32817 records32816_32817 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32816
    maskCheck32816 AlignedValid.nil

def missing32817_32818 : List (BitVec (edgeCount 12)) :=
  [missing32817]
abbrev records32817_32818 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32817]
theorem aligned32817_32818 :
    AlignedValid 12 4 missing32817_32818 records32817_32818 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32817
    maskCheck32817 AlignedValid.nil

def missing32816_32818 : List (BitVec (edgeCount 12)) :=
  missing32816_32817 ++ missing32817_32818
abbrev records32816_32818 : List Blob :=
  records32816_32817 ++ records32817_32818
theorem aligned32816_32818 :
    AlignedValid 12 4 missing32816_32818 records32816_32818 :=
  aligned32816_32817.append aligned32817_32818

def missing32818_32819 : List (BitVec (edgeCount 12)) :=
  [missing32818]
abbrev records32818_32819 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32818]
theorem aligned32818_32819 :
    AlignedValid 12 4 missing32818_32819 records32818_32819 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32818
    maskCheck32818 AlignedValid.nil

def missing32819_32820 : List (BitVec (edgeCount 12)) :=
  [missing32819]
abbrev records32819_32820 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32819]
theorem aligned32819_32820 :
    AlignedValid 12 4 missing32819_32820 records32819_32820 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32819
    maskCheck32819 AlignedValid.nil

def missing32818_32820 : List (BitVec (edgeCount 12)) :=
  missing32818_32819 ++ missing32819_32820
abbrev records32818_32820 : List Blob :=
  records32818_32819 ++ records32819_32820
theorem aligned32818_32820 :
    AlignedValid 12 4 missing32818_32820 records32818_32820 :=
  aligned32818_32819.append aligned32819_32820

def missing32816_32820 : List (BitVec (edgeCount 12)) :=
  missing32816_32818 ++ missing32818_32820
abbrev records32816_32820 : List Blob :=
  records32816_32818 ++ records32818_32820
theorem aligned32816_32820 :
    AlignedValid 12 4 missing32816_32820 records32816_32820 :=
  aligned32816_32818.append aligned32818_32820

def missing32820_32821 : List (BitVec (edgeCount 12)) :=
  [missing32820]
abbrev records32820_32821 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32820]
theorem aligned32820_32821 :
    AlignedValid 12 4 missing32820_32821 records32820_32821 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32820
    maskCheck32820 AlignedValid.nil

def missing32821_32822 : List (BitVec (edgeCount 12)) :=
  [missing32821]
abbrev records32821_32822 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32821]
theorem aligned32821_32822 :
    AlignedValid 12 4 missing32821_32822 records32821_32822 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32821
    maskCheck32821 AlignedValid.nil

def missing32820_32822 : List (BitVec (edgeCount 12)) :=
  missing32820_32821 ++ missing32821_32822
abbrev records32820_32822 : List Blob :=
  records32820_32821 ++ records32821_32822
theorem aligned32820_32822 :
    AlignedValid 12 4 missing32820_32822 records32820_32822 :=
  aligned32820_32821.append aligned32821_32822

def missing32822_32823 : List (BitVec (edgeCount 12)) :=
  [missing32822]
abbrev records32822_32823 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32822]
theorem aligned32822_32823 :
    AlignedValid 12 4 missing32822_32823 records32822_32823 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32822
    maskCheck32822 AlignedValid.nil

def missing32823_32824 : List (BitVec (edgeCount 12)) :=
  [missing32823]
abbrev records32823_32824 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32823]
theorem aligned32823_32824 :
    AlignedValid 12 4 missing32823_32824 records32823_32824 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32823
    maskCheck32823 AlignedValid.nil

def missing32822_32824 : List (BitVec (edgeCount 12)) :=
  missing32822_32823 ++ missing32823_32824
abbrev records32822_32824 : List Blob :=
  records32822_32823 ++ records32823_32824
theorem aligned32822_32824 :
    AlignedValid 12 4 missing32822_32824 records32822_32824 :=
  aligned32822_32823.append aligned32823_32824

def missing32820_32824 : List (BitVec (edgeCount 12)) :=
  missing32820_32822 ++ missing32822_32824
abbrev records32820_32824 : List Blob :=
  records32820_32822 ++ records32822_32824
theorem aligned32820_32824 :
    AlignedValid 12 4 missing32820_32824 records32820_32824 :=
  aligned32820_32822.append aligned32822_32824

def missing32816_32824 : List (BitVec (edgeCount 12)) :=
  missing32816_32820 ++ missing32820_32824
abbrev records32816_32824 : List Blob :=
  records32816_32820 ++ records32820_32824
theorem aligned32816_32824 :
    AlignedValid 12 4 missing32816_32824 records32816_32824 :=
  aligned32816_32820.append aligned32820_32824

def missing32824_32825 : List (BitVec (edgeCount 12)) :=
  [missing32824]
abbrev records32824_32825 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32824]
theorem aligned32824_32825 :
    AlignedValid 12 4 missing32824_32825 records32824_32825 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32824
    maskCheck32824 AlignedValid.nil

def missing32825_32826 : List (BitVec (edgeCount 12)) :=
  [missing32825]
abbrev records32825_32826 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32825]
theorem aligned32825_32826 :
    AlignedValid 12 4 missing32825_32826 records32825_32826 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32825
    maskCheck32825 AlignedValid.nil

def missing32824_32826 : List (BitVec (edgeCount 12)) :=
  missing32824_32825 ++ missing32825_32826
abbrev records32824_32826 : List Blob :=
  records32824_32825 ++ records32825_32826
theorem aligned32824_32826 :
    AlignedValid 12 4 missing32824_32826 records32824_32826 :=
  aligned32824_32825.append aligned32825_32826

def missing32826_32827 : List (BitVec (edgeCount 12)) :=
  [missing32826]
abbrev records32826_32827 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32826]
theorem aligned32826_32827 :
    AlignedValid 12 4 missing32826_32827 records32826_32827 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32826
    maskCheck32826 AlignedValid.nil

def missing32827_32828 : List (BitVec (edgeCount 12)) :=
  [missing32827]
abbrev records32827_32828 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32827]
theorem aligned32827_32828 :
    AlignedValid 12 4 missing32827_32828 records32827_32828 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32827
    maskCheck32827 AlignedValid.nil

def missing32826_32828 : List (BitVec (edgeCount 12)) :=
  missing32826_32827 ++ missing32827_32828
abbrev records32826_32828 : List Blob :=
  records32826_32827 ++ records32827_32828
theorem aligned32826_32828 :
    AlignedValid 12 4 missing32826_32828 records32826_32828 :=
  aligned32826_32827.append aligned32827_32828

def missing32824_32828 : List (BitVec (edgeCount 12)) :=
  missing32824_32826 ++ missing32826_32828
abbrev records32824_32828 : List Blob :=
  records32824_32826 ++ records32826_32828
theorem aligned32824_32828 :
    AlignedValid 12 4 missing32824_32828 records32824_32828 :=
  aligned32824_32826.append aligned32826_32828

def missing32828_32829 : List (BitVec (edgeCount 12)) :=
  [missing32828]
abbrev records32828_32829 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32828]
theorem aligned32828_32829 :
    AlignedValid 12 4 missing32828_32829 records32828_32829 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32828
    maskCheck32828 AlignedValid.nil

def missing32829_32830 : List (BitVec (edgeCount 12)) :=
  [missing32829]
abbrev records32829_32830 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32829]
theorem aligned32829_32830 :
    AlignedValid 12 4 missing32829_32830 records32829_32830 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32829
    maskCheck32829 AlignedValid.nil

def missing32828_32830 : List (BitVec (edgeCount 12)) :=
  missing32828_32829 ++ missing32829_32830
abbrev records32828_32830 : List Blob :=
  records32828_32829 ++ records32829_32830
theorem aligned32828_32830 :
    AlignedValid 12 4 missing32828_32830 records32828_32830 :=
  aligned32828_32829.append aligned32829_32830

def missing32830_32831 : List (BitVec (edgeCount 12)) :=
  [missing32830]
abbrev records32830_32831 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32830]
theorem aligned32830_32831 :
    AlignedValid 12 4 missing32830_32831 records32830_32831 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32830
    maskCheck32830 AlignedValid.nil

def missing32831_32832 : List (BitVec (edgeCount 12)) :=
  [missing32831]
abbrev records32831_32832 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32831]
theorem aligned32831_32832 :
    AlignedValid 12 4 missing32831_32832 records32831_32832 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32831
    maskCheck32831 AlignedValid.nil

def missing32830_32832 : List (BitVec (edgeCount 12)) :=
  missing32830_32831 ++ missing32831_32832
abbrev records32830_32832 : List Blob :=
  records32830_32831 ++ records32831_32832
theorem aligned32830_32832 :
    AlignedValid 12 4 missing32830_32832 records32830_32832 :=
  aligned32830_32831.append aligned32831_32832

def missing32828_32832 : List (BitVec (edgeCount 12)) :=
  missing32828_32830 ++ missing32830_32832
abbrev records32828_32832 : List Blob :=
  records32828_32830 ++ records32830_32832
theorem aligned32828_32832 :
    AlignedValid 12 4 missing32828_32832 records32828_32832 :=
  aligned32828_32830.append aligned32830_32832

def missing32824_32832 : List (BitVec (edgeCount 12)) :=
  missing32824_32828 ++ missing32828_32832
abbrev records32824_32832 : List Blob :=
  records32824_32828 ++ records32828_32832
theorem aligned32824_32832 :
    AlignedValid 12 4 missing32824_32832 records32824_32832 :=
  aligned32824_32828.append aligned32828_32832

def missing32816_32832 : List (BitVec (edgeCount 12)) :=
  missing32816_32824 ++ missing32824_32832
abbrev records32816_32832 : List Blob :=
  records32816_32824 ++ records32824_32832
theorem aligned32816_32832 :
    AlignedValid 12 4 missing32816_32832 records32816_32832 :=
  aligned32816_32824.append aligned32824_32832

def missing32800_32832 : List (BitVec (edgeCount 12)) :=
  missing32800_32816 ++ missing32816_32832
abbrev records32800_32832 : List Blob :=
  records32800_32816 ++ records32816_32832
theorem aligned32800_32832 :
    AlignedValid 12 4 missing32800_32832 records32800_32832 :=
  aligned32800_32816.append aligned32816_32832

def missing32768_32832 : List (BitVec (edgeCount 12)) :=
  missing32768_32800 ++ missing32800_32832
abbrev records32768_32832 : List Blob :=
  records32768_32800 ++ records32800_32832
theorem aligned32768_32832 :
    AlignedValid 12 4 missing32768_32832 records32768_32832 :=
  aligned32768_32800.append aligned32800_32832

def missing32832_32833 : List (BitVec (edgeCount 12)) :=
  [missing32832]
abbrev records32832_32833 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32832]
theorem aligned32832_32833 :
    AlignedValid 12 4 missing32832_32833 records32832_32833 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32832
    maskCheck32832 AlignedValid.nil

def missing32833_32834 : List (BitVec (edgeCount 12)) :=
  [missing32833]
abbrev records32833_32834 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32833]
theorem aligned32833_32834 :
    AlignedValid 12 4 missing32833_32834 records32833_32834 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32833
    maskCheck32833 AlignedValid.nil

def missing32832_32834 : List (BitVec (edgeCount 12)) :=
  missing32832_32833 ++ missing32833_32834
abbrev records32832_32834 : List Blob :=
  records32832_32833 ++ records32833_32834
theorem aligned32832_32834 :
    AlignedValid 12 4 missing32832_32834 records32832_32834 :=
  aligned32832_32833.append aligned32833_32834

def missing32834_32835 : List (BitVec (edgeCount 12)) :=
  [missing32834]
abbrev records32834_32835 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32834]
theorem aligned32834_32835 :
    AlignedValid 12 4 missing32834_32835 records32834_32835 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32834
    maskCheck32834 AlignedValid.nil

def missing32835_32836 : List (BitVec (edgeCount 12)) :=
  [missing32835]
abbrev records32835_32836 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32835]
theorem aligned32835_32836 :
    AlignedValid 12 4 missing32835_32836 records32835_32836 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32835
    maskCheck32835 AlignedValid.nil

def missing32834_32836 : List (BitVec (edgeCount 12)) :=
  missing32834_32835 ++ missing32835_32836
abbrev records32834_32836 : List Blob :=
  records32834_32835 ++ records32835_32836
theorem aligned32834_32836 :
    AlignedValid 12 4 missing32834_32836 records32834_32836 :=
  aligned32834_32835.append aligned32835_32836

def missing32832_32836 : List (BitVec (edgeCount 12)) :=
  missing32832_32834 ++ missing32834_32836
abbrev records32832_32836 : List Blob :=
  records32832_32834 ++ records32834_32836
theorem aligned32832_32836 :
    AlignedValid 12 4 missing32832_32836 records32832_32836 :=
  aligned32832_32834.append aligned32834_32836

def missing32836_32837 : List (BitVec (edgeCount 12)) :=
  [missing32836]
abbrev records32836_32837 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32836]
theorem aligned32836_32837 :
    AlignedValid 12 4 missing32836_32837 records32836_32837 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32836
    maskCheck32836 AlignedValid.nil

def missing32837_32838 : List (BitVec (edgeCount 12)) :=
  [missing32837]
abbrev records32837_32838 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32837]
theorem aligned32837_32838 :
    AlignedValid 12 4 missing32837_32838 records32837_32838 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32837
    maskCheck32837 AlignedValid.nil

def missing32836_32838 : List (BitVec (edgeCount 12)) :=
  missing32836_32837 ++ missing32837_32838
abbrev records32836_32838 : List Blob :=
  records32836_32837 ++ records32837_32838
theorem aligned32836_32838 :
    AlignedValid 12 4 missing32836_32838 records32836_32838 :=
  aligned32836_32837.append aligned32837_32838

def missing32838_32839 : List (BitVec (edgeCount 12)) :=
  [missing32838]
abbrev records32838_32839 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32838]
theorem aligned32838_32839 :
    AlignedValid 12 4 missing32838_32839 records32838_32839 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32838
    maskCheck32838 AlignedValid.nil

def missing32839_32840 : List (BitVec (edgeCount 12)) :=
  [missing32839]
abbrev records32839_32840 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32839]
theorem aligned32839_32840 :
    AlignedValid 12 4 missing32839_32840 records32839_32840 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32839
    maskCheck32839 AlignedValid.nil

def missing32838_32840 : List (BitVec (edgeCount 12)) :=
  missing32838_32839 ++ missing32839_32840
abbrev records32838_32840 : List Blob :=
  records32838_32839 ++ records32839_32840
theorem aligned32838_32840 :
    AlignedValid 12 4 missing32838_32840 records32838_32840 :=
  aligned32838_32839.append aligned32839_32840

def missing32836_32840 : List (BitVec (edgeCount 12)) :=
  missing32836_32838 ++ missing32838_32840
abbrev records32836_32840 : List Blob :=
  records32836_32838 ++ records32838_32840
theorem aligned32836_32840 :
    AlignedValid 12 4 missing32836_32840 records32836_32840 :=
  aligned32836_32838.append aligned32838_32840

def missing32832_32840 : List (BitVec (edgeCount 12)) :=
  missing32832_32836 ++ missing32836_32840
abbrev records32832_32840 : List Blob :=
  records32832_32836 ++ records32836_32840
theorem aligned32832_32840 :
    AlignedValid 12 4 missing32832_32840 records32832_32840 :=
  aligned32832_32836.append aligned32836_32840

def missing32840_32841 : List (BitVec (edgeCount 12)) :=
  [missing32840]
abbrev records32840_32841 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32840]
theorem aligned32840_32841 :
    AlignedValid 12 4 missing32840_32841 records32840_32841 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32840
    maskCheck32840 AlignedValid.nil

def missing32841_32842 : List (BitVec (edgeCount 12)) :=
  [missing32841]
abbrev records32841_32842 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32841]
theorem aligned32841_32842 :
    AlignedValid 12 4 missing32841_32842 records32841_32842 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32841
    maskCheck32841 AlignedValid.nil

def missing32840_32842 : List (BitVec (edgeCount 12)) :=
  missing32840_32841 ++ missing32841_32842
abbrev records32840_32842 : List Blob :=
  records32840_32841 ++ records32841_32842
theorem aligned32840_32842 :
    AlignedValid 12 4 missing32840_32842 records32840_32842 :=
  aligned32840_32841.append aligned32841_32842

def missing32842_32843 : List (BitVec (edgeCount 12)) :=
  [missing32842]
abbrev records32842_32843 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32842]
theorem aligned32842_32843 :
    AlignedValid 12 4 missing32842_32843 records32842_32843 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32842
    maskCheck32842 AlignedValid.nil

def missing32843_32844 : List (BitVec (edgeCount 12)) :=
  [missing32843]
abbrev records32843_32844 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32843]
theorem aligned32843_32844 :
    AlignedValid 12 4 missing32843_32844 records32843_32844 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32843
    maskCheck32843 AlignedValid.nil

def missing32842_32844 : List (BitVec (edgeCount 12)) :=
  missing32842_32843 ++ missing32843_32844
abbrev records32842_32844 : List Blob :=
  records32842_32843 ++ records32843_32844
theorem aligned32842_32844 :
    AlignedValid 12 4 missing32842_32844 records32842_32844 :=
  aligned32842_32843.append aligned32843_32844

def missing32840_32844 : List (BitVec (edgeCount 12)) :=
  missing32840_32842 ++ missing32842_32844
abbrev records32840_32844 : List Blob :=
  records32840_32842 ++ records32842_32844
theorem aligned32840_32844 :
    AlignedValid 12 4 missing32840_32844 records32840_32844 :=
  aligned32840_32842.append aligned32842_32844

def missing32844_32845 : List (BitVec (edgeCount 12)) :=
  [missing32844]
abbrev records32844_32845 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32844]
theorem aligned32844_32845 :
    AlignedValid 12 4 missing32844_32845 records32844_32845 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32844
    maskCheck32844 AlignedValid.nil

def missing32845_32846 : List (BitVec (edgeCount 12)) :=
  [missing32845]
abbrev records32845_32846 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32845]
theorem aligned32845_32846 :
    AlignedValid 12 4 missing32845_32846 records32845_32846 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32845
    maskCheck32845 AlignedValid.nil

def missing32844_32846 : List (BitVec (edgeCount 12)) :=
  missing32844_32845 ++ missing32845_32846
abbrev records32844_32846 : List Blob :=
  records32844_32845 ++ records32845_32846
theorem aligned32844_32846 :
    AlignedValid 12 4 missing32844_32846 records32844_32846 :=
  aligned32844_32845.append aligned32845_32846

def missing32846_32847 : List (BitVec (edgeCount 12)) :=
  [missing32846]
abbrev records32846_32847 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32846]
theorem aligned32846_32847 :
    AlignedValid 12 4 missing32846_32847 records32846_32847 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32846
    maskCheck32846 AlignedValid.nil

def missing32847_32848 : List (BitVec (edgeCount 12)) :=
  [missing32847]
abbrev records32847_32848 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32847]
theorem aligned32847_32848 :
    AlignedValid 12 4 missing32847_32848 records32847_32848 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32847
    maskCheck32847 AlignedValid.nil

def missing32846_32848 : List (BitVec (edgeCount 12)) :=
  missing32846_32847 ++ missing32847_32848
abbrev records32846_32848 : List Blob :=
  records32846_32847 ++ records32847_32848
theorem aligned32846_32848 :
    AlignedValid 12 4 missing32846_32848 records32846_32848 :=
  aligned32846_32847.append aligned32847_32848

def missing32844_32848 : List (BitVec (edgeCount 12)) :=
  missing32844_32846 ++ missing32846_32848
abbrev records32844_32848 : List Blob :=
  records32844_32846 ++ records32846_32848
theorem aligned32844_32848 :
    AlignedValid 12 4 missing32844_32848 records32844_32848 :=
  aligned32844_32846.append aligned32846_32848

def missing32840_32848 : List (BitVec (edgeCount 12)) :=
  missing32840_32844 ++ missing32844_32848
abbrev records32840_32848 : List Blob :=
  records32840_32844 ++ records32844_32848
theorem aligned32840_32848 :
    AlignedValid 12 4 missing32840_32848 records32840_32848 :=
  aligned32840_32844.append aligned32844_32848

def missing32832_32848 : List (BitVec (edgeCount 12)) :=
  missing32832_32840 ++ missing32840_32848
abbrev records32832_32848 : List Blob :=
  records32832_32840 ++ records32840_32848
theorem aligned32832_32848 :
    AlignedValid 12 4 missing32832_32848 records32832_32848 :=
  aligned32832_32840.append aligned32840_32848

def missing32848_32849 : List (BitVec (edgeCount 12)) :=
  [missing32848]
abbrev records32848_32849 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32848]
theorem aligned32848_32849 :
    AlignedValid 12 4 missing32848_32849 records32848_32849 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32848
    maskCheck32848 AlignedValid.nil

def missing32849_32850 : List (BitVec (edgeCount 12)) :=
  [missing32849]
abbrev records32849_32850 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32849]
theorem aligned32849_32850 :
    AlignedValid 12 4 missing32849_32850 records32849_32850 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32849
    maskCheck32849 AlignedValid.nil

def missing32848_32850 : List (BitVec (edgeCount 12)) :=
  missing32848_32849 ++ missing32849_32850
abbrev records32848_32850 : List Blob :=
  records32848_32849 ++ records32849_32850
theorem aligned32848_32850 :
    AlignedValid 12 4 missing32848_32850 records32848_32850 :=
  aligned32848_32849.append aligned32849_32850

def missing32850_32851 : List (BitVec (edgeCount 12)) :=
  [missing32850]
abbrev records32850_32851 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32850]
theorem aligned32850_32851 :
    AlignedValid 12 4 missing32850_32851 records32850_32851 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32850
    maskCheck32850 AlignedValid.nil

def missing32851_32852 : List (BitVec (edgeCount 12)) :=
  [missing32851]
abbrev records32851_32852 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32851]
theorem aligned32851_32852 :
    AlignedValid 12 4 missing32851_32852 records32851_32852 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32851
    maskCheck32851 AlignedValid.nil

def missing32850_32852 : List (BitVec (edgeCount 12)) :=
  missing32850_32851 ++ missing32851_32852
abbrev records32850_32852 : List Blob :=
  records32850_32851 ++ records32851_32852
theorem aligned32850_32852 :
    AlignedValid 12 4 missing32850_32852 records32850_32852 :=
  aligned32850_32851.append aligned32851_32852

def missing32848_32852 : List (BitVec (edgeCount 12)) :=
  missing32848_32850 ++ missing32850_32852
abbrev records32848_32852 : List Blob :=
  records32848_32850 ++ records32850_32852
theorem aligned32848_32852 :
    AlignedValid 12 4 missing32848_32852 records32848_32852 :=
  aligned32848_32850.append aligned32850_32852

def missing32852_32853 : List (BitVec (edgeCount 12)) :=
  [missing32852]
abbrev records32852_32853 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32852]
theorem aligned32852_32853 :
    AlignedValid 12 4 missing32852_32853 records32852_32853 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32852
    maskCheck32852 AlignedValid.nil

def missing32853_32854 : List (BitVec (edgeCount 12)) :=
  [missing32853]
abbrev records32853_32854 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32853]
theorem aligned32853_32854 :
    AlignedValid 12 4 missing32853_32854 records32853_32854 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32853
    maskCheck32853 AlignedValid.nil

def missing32852_32854 : List (BitVec (edgeCount 12)) :=
  missing32852_32853 ++ missing32853_32854
abbrev records32852_32854 : List Blob :=
  records32852_32853 ++ records32853_32854
theorem aligned32852_32854 :
    AlignedValid 12 4 missing32852_32854 records32852_32854 :=
  aligned32852_32853.append aligned32853_32854

def missing32854_32855 : List (BitVec (edgeCount 12)) :=
  [missing32854]
abbrev records32854_32855 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32854]
theorem aligned32854_32855 :
    AlignedValid 12 4 missing32854_32855 records32854_32855 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32854
    maskCheck32854 AlignedValid.nil

def missing32855_32856 : List (BitVec (edgeCount 12)) :=
  [missing32855]
abbrev records32855_32856 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32855]
theorem aligned32855_32856 :
    AlignedValid 12 4 missing32855_32856 records32855_32856 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32855
    maskCheck32855 AlignedValid.nil

def missing32854_32856 : List (BitVec (edgeCount 12)) :=
  missing32854_32855 ++ missing32855_32856
abbrev records32854_32856 : List Blob :=
  records32854_32855 ++ records32855_32856
theorem aligned32854_32856 :
    AlignedValid 12 4 missing32854_32856 records32854_32856 :=
  aligned32854_32855.append aligned32855_32856

def missing32852_32856 : List (BitVec (edgeCount 12)) :=
  missing32852_32854 ++ missing32854_32856
abbrev records32852_32856 : List Blob :=
  records32852_32854 ++ records32854_32856
theorem aligned32852_32856 :
    AlignedValid 12 4 missing32852_32856 records32852_32856 :=
  aligned32852_32854.append aligned32854_32856

def missing32848_32856 : List (BitVec (edgeCount 12)) :=
  missing32848_32852 ++ missing32852_32856
abbrev records32848_32856 : List Blob :=
  records32848_32852 ++ records32852_32856
theorem aligned32848_32856 :
    AlignedValid 12 4 missing32848_32856 records32848_32856 :=
  aligned32848_32852.append aligned32852_32856

def missing32856_32857 : List (BitVec (edgeCount 12)) :=
  [missing32856]
abbrev records32856_32857 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32856]
theorem aligned32856_32857 :
    AlignedValid 12 4 missing32856_32857 records32856_32857 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32856
    maskCheck32856 AlignedValid.nil

def missing32857_32858 : List (BitVec (edgeCount 12)) :=
  [missing32857]
abbrev records32857_32858 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32857]
theorem aligned32857_32858 :
    AlignedValid 12 4 missing32857_32858 records32857_32858 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32857
    maskCheck32857 AlignedValid.nil

def missing32856_32858 : List (BitVec (edgeCount 12)) :=
  missing32856_32857 ++ missing32857_32858
abbrev records32856_32858 : List Blob :=
  records32856_32857 ++ records32857_32858
theorem aligned32856_32858 :
    AlignedValid 12 4 missing32856_32858 records32856_32858 :=
  aligned32856_32857.append aligned32857_32858

def missing32858_32859 : List (BitVec (edgeCount 12)) :=
  [missing32858]
abbrev records32858_32859 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32858]
theorem aligned32858_32859 :
    AlignedValid 12 4 missing32858_32859 records32858_32859 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32858
    maskCheck32858 AlignedValid.nil

def missing32859_32860 : List (BitVec (edgeCount 12)) :=
  [missing32859]
abbrev records32859_32860 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32859]
theorem aligned32859_32860 :
    AlignedValid 12 4 missing32859_32860 records32859_32860 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32859
    maskCheck32859 AlignedValid.nil

def missing32858_32860 : List (BitVec (edgeCount 12)) :=
  missing32858_32859 ++ missing32859_32860
abbrev records32858_32860 : List Blob :=
  records32858_32859 ++ records32859_32860
theorem aligned32858_32860 :
    AlignedValid 12 4 missing32858_32860 records32858_32860 :=
  aligned32858_32859.append aligned32859_32860

def missing32856_32860 : List (BitVec (edgeCount 12)) :=
  missing32856_32858 ++ missing32858_32860
abbrev records32856_32860 : List Blob :=
  records32856_32858 ++ records32858_32860
theorem aligned32856_32860 :
    AlignedValid 12 4 missing32856_32860 records32856_32860 :=
  aligned32856_32858.append aligned32858_32860

def missing32860_32861 : List (BitVec (edgeCount 12)) :=
  [missing32860]
abbrev records32860_32861 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32860]
theorem aligned32860_32861 :
    AlignedValid 12 4 missing32860_32861 records32860_32861 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32860
    maskCheck32860 AlignedValid.nil

def missing32861_32862 : List (BitVec (edgeCount 12)) :=
  [missing32861]
abbrev records32861_32862 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32861]
theorem aligned32861_32862 :
    AlignedValid 12 4 missing32861_32862 records32861_32862 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32861
    maskCheck32861 AlignedValid.nil

def missing32860_32862 : List (BitVec (edgeCount 12)) :=
  missing32860_32861 ++ missing32861_32862
abbrev records32860_32862 : List Blob :=
  records32860_32861 ++ records32861_32862
theorem aligned32860_32862 :
    AlignedValid 12 4 missing32860_32862 records32860_32862 :=
  aligned32860_32861.append aligned32861_32862

def missing32862_32863 : List (BitVec (edgeCount 12)) :=
  [missing32862]
abbrev records32862_32863 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32862]
theorem aligned32862_32863 :
    AlignedValid 12 4 missing32862_32863 records32862_32863 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32862
    maskCheck32862 AlignedValid.nil

def missing32863_32864 : List (BitVec (edgeCount 12)) :=
  [missing32863]
abbrev records32863_32864 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32863]
theorem aligned32863_32864 :
    AlignedValid 12 4 missing32863_32864 records32863_32864 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32863
    maskCheck32863 AlignedValid.nil

def missing32862_32864 : List (BitVec (edgeCount 12)) :=
  missing32862_32863 ++ missing32863_32864
abbrev records32862_32864 : List Blob :=
  records32862_32863 ++ records32863_32864
theorem aligned32862_32864 :
    AlignedValid 12 4 missing32862_32864 records32862_32864 :=
  aligned32862_32863.append aligned32863_32864

def missing32860_32864 : List (BitVec (edgeCount 12)) :=
  missing32860_32862 ++ missing32862_32864
abbrev records32860_32864 : List Blob :=
  records32860_32862 ++ records32862_32864
theorem aligned32860_32864 :
    AlignedValid 12 4 missing32860_32864 records32860_32864 :=
  aligned32860_32862.append aligned32862_32864

def missing32856_32864 : List (BitVec (edgeCount 12)) :=
  missing32856_32860 ++ missing32860_32864
abbrev records32856_32864 : List Blob :=
  records32856_32860 ++ records32860_32864
theorem aligned32856_32864 :
    AlignedValid 12 4 missing32856_32864 records32856_32864 :=
  aligned32856_32860.append aligned32860_32864

def missing32848_32864 : List (BitVec (edgeCount 12)) :=
  missing32848_32856 ++ missing32856_32864
abbrev records32848_32864 : List Blob :=
  records32848_32856 ++ records32856_32864
theorem aligned32848_32864 :
    AlignedValid 12 4 missing32848_32864 records32848_32864 :=
  aligned32848_32856.append aligned32856_32864

def missing32832_32864 : List (BitVec (edgeCount 12)) :=
  missing32832_32848 ++ missing32848_32864
abbrev records32832_32864 : List Blob :=
  records32832_32848 ++ records32848_32864
theorem aligned32832_32864 :
    AlignedValid 12 4 missing32832_32864 records32832_32864 :=
  aligned32832_32848.append aligned32848_32864

def missing32864_32865 : List (BitVec (edgeCount 12)) :=
  [missing32864]
abbrev records32864_32865 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32864]
theorem aligned32864_32865 :
    AlignedValid 12 4 missing32864_32865 records32864_32865 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32864
    maskCheck32864 AlignedValid.nil

def missing32865_32866 : List (BitVec (edgeCount 12)) :=
  [missing32865]
abbrev records32865_32866 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32865]
theorem aligned32865_32866 :
    AlignedValid 12 4 missing32865_32866 records32865_32866 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32865
    maskCheck32865 AlignedValid.nil

def missing32864_32866 : List (BitVec (edgeCount 12)) :=
  missing32864_32865 ++ missing32865_32866
abbrev records32864_32866 : List Blob :=
  records32864_32865 ++ records32865_32866
theorem aligned32864_32866 :
    AlignedValid 12 4 missing32864_32866 records32864_32866 :=
  aligned32864_32865.append aligned32865_32866

def missing32866_32867 : List (BitVec (edgeCount 12)) :=
  [missing32866]
abbrev records32866_32867 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32866]
theorem aligned32866_32867 :
    AlignedValid 12 4 missing32866_32867 records32866_32867 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32866
    maskCheck32866 AlignedValid.nil

def missing32867_32868 : List (BitVec (edgeCount 12)) :=
  [missing32867]
abbrev records32867_32868 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32867]
theorem aligned32867_32868 :
    AlignedValid 12 4 missing32867_32868 records32867_32868 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32867
    maskCheck32867 AlignedValid.nil

def missing32866_32868 : List (BitVec (edgeCount 12)) :=
  missing32866_32867 ++ missing32867_32868
abbrev records32866_32868 : List Blob :=
  records32866_32867 ++ records32867_32868
theorem aligned32866_32868 :
    AlignedValid 12 4 missing32866_32868 records32866_32868 :=
  aligned32866_32867.append aligned32867_32868

def missing32864_32868 : List (BitVec (edgeCount 12)) :=
  missing32864_32866 ++ missing32866_32868
abbrev records32864_32868 : List Blob :=
  records32864_32866 ++ records32866_32868
theorem aligned32864_32868 :
    AlignedValid 12 4 missing32864_32868 records32864_32868 :=
  aligned32864_32866.append aligned32866_32868

def missing32868_32869 : List (BitVec (edgeCount 12)) :=
  [missing32868]
abbrev records32868_32869 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32868]
theorem aligned32868_32869 :
    AlignedValid 12 4 missing32868_32869 records32868_32869 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32868
    maskCheck32868 AlignedValid.nil

def missing32869_32870 : List (BitVec (edgeCount 12)) :=
  [missing32869]
abbrev records32869_32870 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32869]
theorem aligned32869_32870 :
    AlignedValid 12 4 missing32869_32870 records32869_32870 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32869
    maskCheck32869 AlignedValid.nil

def missing32868_32870 : List (BitVec (edgeCount 12)) :=
  missing32868_32869 ++ missing32869_32870
abbrev records32868_32870 : List Blob :=
  records32868_32869 ++ records32869_32870
theorem aligned32868_32870 :
    AlignedValid 12 4 missing32868_32870 records32868_32870 :=
  aligned32868_32869.append aligned32869_32870

def missing32870_32871 : List (BitVec (edgeCount 12)) :=
  [missing32870]
abbrev records32870_32871 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32870]
theorem aligned32870_32871 :
    AlignedValid 12 4 missing32870_32871 records32870_32871 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32870
    maskCheck32870 AlignedValid.nil

def missing32871_32872 : List (BitVec (edgeCount 12)) :=
  [missing32871]
abbrev records32871_32872 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32871]
theorem aligned32871_32872 :
    AlignedValid 12 4 missing32871_32872 records32871_32872 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32871
    maskCheck32871 AlignedValid.nil

def missing32870_32872 : List (BitVec (edgeCount 12)) :=
  missing32870_32871 ++ missing32871_32872
abbrev records32870_32872 : List Blob :=
  records32870_32871 ++ records32871_32872
theorem aligned32870_32872 :
    AlignedValid 12 4 missing32870_32872 records32870_32872 :=
  aligned32870_32871.append aligned32871_32872

def missing32868_32872 : List (BitVec (edgeCount 12)) :=
  missing32868_32870 ++ missing32870_32872
abbrev records32868_32872 : List Blob :=
  records32868_32870 ++ records32870_32872
theorem aligned32868_32872 :
    AlignedValid 12 4 missing32868_32872 records32868_32872 :=
  aligned32868_32870.append aligned32870_32872

def missing32864_32872 : List (BitVec (edgeCount 12)) :=
  missing32864_32868 ++ missing32868_32872
abbrev records32864_32872 : List Blob :=
  records32864_32868 ++ records32868_32872
theorem aligned32864_32872 :
    AlignedValid 12 4 missing32864_32872 records32864_32872 :=
  aligned32864_32868.append aligned32868_32872

def missing32872_32873 : List (BitVec (edgeCount 12)) :=
  [missing32872]
abbrev records32872_32873 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32872]
theorem aligned32872_32873 :
    AlignedValid 12 4 missing32872_32873 records32872_32873 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32872
    maskCheck32872 AlignedValid.nil

def missing32873_32874 : List (BitVec (edgeCount 12)) :=
  [missing32873]
abbrev records32873_32874 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32873]
theorem aligned32873_32874 :
    AlignedValid 12 4 missing32873_32874 records32873_32874 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32873
    maskCheck32873 AlignedValid.nil

def missing32872_32874 : List (BitVec (edgeCount 12)) :=
  missing32872_32873 ++ missing32873_32874
abbrev records32872_32874 : List Blob :=
  records32872_32873 ++ records32873_32874
theorem aligned32872_32874 :
    AlignedValid 12 4 missing32872_32874 records32872_32874 :=
  aligned32872_32873.append aligned32873_32874

def missing32874_32875 : List (BitVec (edgeCount 12)) :=
  [missing32874]
abbrev records32874_32875 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32874]
theorem aligned32874_32875 :
    AlignedValid 12 4 missing32874_32875 records32874_32875 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32874
    maskCheck32874 AlignedValid.nil

def missing32875_32876 : List (BitVec (edgeCount 12)) :=
  [missing32875]
abbrev records32875_32876 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32875]
theorem aligned32875_32876 :
    AlignedValid 12 4 missing32875_32876 records32875_32876 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32875
    maskCheck32875 AlignedValid.nil

def missing32874_32876 : List (BitVec (edgeCount 12)) :=
  missing32874_32875 ++ missing32875_32876
abbrev records32874_32876 : List Blob :=
  records32874_32875 ++ records32875_32876
theorem aligned32874_32876 :
    AlignedValid 12 4 missing32874_32876 records32874_32876 :=
  aligned32874_32875.append aligned32875_32876

def missing32872_32876 : List (BitVec (edgeCount 12)) :=
  missing32872_32874 ++ missing32874_32876
abbrev records32872_32876 : List Blob :=
  records32872_32874 ++ records32874_32876
theorem aligned32872_32876 :
    AlignedValid 12 4 missing32872_32876 records32872_32876 :=
  aligned32872_32874.append aligned32874_32876

def missing32876_32877 : List (BitVec (edgeCount 12)) :=
  [missing32876]
abbrev records32876_32877 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32876]
theorem aligned32876_32877 :
    AlignedValid 12 4 missing32876_32877 records32876_32877 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32876
    maskCheck32876 AlignedValid.nil

def missing32877_32878 : List (BitVec (edgeCount 12)) :=
  [missing32877]
abbrev records32877_32878 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32877]
theorem aligned32877_32878 :
    AlignedValid 12 4 missing32877_32878 records32877_32878 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32877
    maskCheck32877 AlignedValid.nil

def missing32876_32878 : List (BitVec (edgeCount 12)) :=
  missing32876_32877 ++ missing32877_32878
abbrev records32876_32878 : List Blob :=
  records32876_32877 ++ records32877_32878
theorem aligned32876_32878 :
    AlignedValid 12 4 missing32876_32878 records32876_32878 :=
  aligned32876_32877.append aligned32877_32878

def missing32878_32879 : List (BitVec (edgeCount 12)) :=
  [missing32878]
abbrev records32878_32879 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32878]
theorem aligned32878_32879 :
    AlignedValid 12 4 missing32878_32879 records32878_32879 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32878
    maskCheck32878 AlignedValid.nil

def missing32879_32880 : List (BitVec (edgeCount 12)) :=
  [missing32879]
abbrev records32879_32880 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32879]
theorem aligned32879_32880 :
    AlignedValid 12 4 missing32879_32880 records32879_32880 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32879
    maskCheck32879 AlignedValid.nil

def missing32878_32880 : List (BitVec (edgeCount 12)) :=
  missing32878_32879 ++ missing32879_32880
abbrev records32878_32880 : List Blob :=
  records32878_32879 ++ records32879_32880
theorem aligned32878_32880 :
    AlignedValid 12 4 missing32878_32880 records32878_32880 :=
  aligned32878_32879.append aligned32879_32880

def missing32876_32880 : List (BitVec (edgeCount 12)) :=
  missing32876_32878 ++ missing32878_32880
abbrev records32876_32880 : List Blob :=
  records32876_32878 ++ records32878_32880
theorem aligned32876_32880 :
    AlignedValid 12 4 missing32876_32880 records32876_32880 :=
  aligned32876_32878.append aligned32878_32880

def missing32872_32880 : List (BitVec (edgeCount 12)) :=
  missing32872_32876 ++ missing32876_32880
abbrev records32872_32880 : List Blob :=
  records32872_32876 ++ records32876_32880
theorem aligned32872_32880 :
    AlignedValid 12 4 missing32872_32880 records32872_32880 :=
  aligned32872_32876.append aligned32876_32880

def missing32864_32880 : List (BitVec (edgeCount 12)) :=
  missing32864_32872 ++ missing32872_32880
abbrev records32864_32880 : List Blob :=
  records32864_32872 ++ records32872_32880
theorem aligned32864_32880 :
    AlignedValid 12 4 missing32864_32880 records32864_32880 :=
  aligned32864_32872.append aligned32872_32880

def missing32880_32881 : List (BitVec (edgeCount 12)) :=
  [missing32880]
abbrev records32880_32881 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32880]
theorem aligned32880_32881 :
    AlignedValid 12 4 missing32880_32881 records32880_32881 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32880
    maskCheck32880 AlignedValid.nil

def missing32881_32882 : List (BitVec (edgeCount 12)) :=
  [missing32881]
abbrev records32881_32882 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32881]
theorem aligned32881_32882 :
    AlignedValid 12 4 missing32881_32882 records32881_32882 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32881
    maskCheck32881 AlignedValid.nil

def missing32880_32882 : List (BitVec (edgeCount 12)) :=
  missing32880_32881 ++ missing32881_32882
abbrev records32880_32882 : List Blob :=
  records32880_32881 ++ records32881_32882
theorem aligned32880_32882 :
    AlignedValid 12 4 missing32880_32882 records32880_32882 :=
  aligned32880_32881.append aligned32881_32882

def missing32882_32883 : List (BitVec (edgeCount 12)) :=
  [missing32882]
abbrev records32882_32883 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32882]
theorem aligned32882_32883 :
    AlignedValid 12 4 missing32882_32883 records32882_32883 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32882
    maskCheck32882 AlignedValid.nil

def missing32883_32884 : List (BitVec (edgeCount 12)) :=
  [missing32883]
abbrev records32883_32884 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32883]
theorem aligned32883_32884 :
    AlignedValid 12 4 missing32883_32884 records32883_32884 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32883
    maskCheck32883 AlignedValid.nil

def missing32882_32884 : List (BitVec (edgeCount 12)) :=
  missing32882_32883 ++ missing32883_32884
abbrev records32882_32884 : List Blob :=
  records32882_32883 ++ records32883_32884
theorem aligned32882_32884 :
    AlignedValid 12 4 missing32882_32884 records32882_32884 :=
  aligned32882_32883.append aligned32883_32884

def missing32880_32884 : List (BitVec (edgeCount 12)) :=
  missing32880_32882 ++ missing32882_32884
abbrev records32880_32884 : List Blob :=
  records32880_32882 ++ records32882_32884
theorem aligned32880_32884 :
    AlignedValid 12 4 missing32880_32884 records32880_32884 :=
  aligned32880_32882.append aligned32882_32884

def missing32884_32885 : List (BitVec (edgeCount 12)) :=
  [missing32884]
abbrev records32884_32885 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32884]
theorem aligned32884_32885 :
    AlignedValid 12 4 missing32884_32885 records32884_32885 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32884
    maskCheck32884 AlignedValid.nil

def missing32885_32886 : List (BitVec (edgeCount 12)) :=
  [missing32885]
abbrev records32885_32886 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32885]
theorem aligned32885_32886 :
    AlignedValid 12 4 missing32885_32886 records32885_32886 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32885
    maskCheck32885 AlignedValid.nil

def missing32884_32886 : List (BitVec (edgeCount 12)) :=
  missing32884_32885 ++ missing32885_32886
abbrev records32884_32886 : List Blob :=
  records32884_32885 ++ records32885_32886
theorem aligned32884_32886 :
    AlignedValid 12 4 missing32884_32886 records32884_32886 :=
  aligned32884_32885.append aligned32885_32886

def missing32886_32887 : List (BitVec (edgeCount 12)) :=
  [missing32886]
abbrev records32886_32887 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32886]
theorem aligned32886_32887 :
    AlignedValid 12 4 missing32886_32887 records32886_32887 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32886
    maskCheck32886 AlignedValid.nil

def missing32887_32888 : List (BitVec (edgeCount 12)) :=
  [missing32887]
abbrev records32887_32888 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32887]
theorem aligned32887_32888 :
    AlignedValid 12 4 missing32887_32888 records32887_32888 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32887
    maskCheck32887 AlignedValid.nil

def missing32886_32888 : List (BitVec (edgeCount 12)) :=
  missing32886_32887 ++ missing32887_32888
abbrev records32886_32888 : List Blob :=
  records32886_32887 ++ records32887_32888
theorem aligned32886_32888 :
    AlignedValid 12 4 missing32886_32888 records32886_32888 :=
  aligned32886_32887.append aligned32887_32888

def missing32884_32888 : List (BitVec (edgeCount 12)) :=
  missing32884_32886 ++ missing32886_32888
abbrev records32884_32888 : List Blob :=
  records32884_32886 ++ records32886_32888
theorem aligned32884_32888 :
    AlignedValid 12 4 missing32884_32888 records32884_32888 :=
  aligned32884_32886.append aligned32886_32888

def missing32880_32888 : List (BitVec (edgeCount 12)) :=
  missing32880_32884 ++ missing32884_32888
abbrev records32880_32888 : List Blob :=
  records32880_32884 ++ records32884_32888
theorem aligned32880_32888 :
    AlignedValid 12 4 missing32880_32888 records32880_32888 :=
  aligned32880_32884.append aligned32884_32888

def missing32888_32889 : List (BitVec (edgeCount 12)) :=
  [missing32888]
abbrev records32888_32889 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32888]
theorem aligned32888_32889 :
    AlignedValid 12 4 missing32888_32889 records32888_32889 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32888
    maskCheck32888 AlignedValid.nil

def missing32889_32890 : List (BitVec (edgeCount 12)) :=
  [missing32889]
abbrev records32889_32890 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32889]
theorem aligned32889_32890 :
    AlignedValid 12 4 missing32889_32890 records32889_32890 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32889
    maskCheck32889 AlignedValid.nil

def missing32888_32890 : List (BitVec (edgeCount 12)) :=
  missing32888_32889 ++ missing32889_32890
abbrev records32888_32890 : List Blob :=
  records32888_32889 ++ records32889_32890
theorem aligned32888_32890 :
    AlignedValid 12 4 missing32888_32890 records32888_32890 :=
  aligned32888_32889.append aligned32889_32890

def missing32890_32891 : List (BitVec (edgeCount 12)) :=
  [missing32890]
abbrev records32890_32891 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32890]
theorem aligned32890_32891 :
    AlignedValid 12 4 missing32890_32891 records32890_32891 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32890
    maskCheck32890 AlignedValid.nil

def missing32891_32892 : List (BitVec (edgeCount 12)) :=
  [missing32891]
abbrev records32891_32892 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32891]
theorem aligned32891_32892 :
    AlignedValid 12 4 missing32891_32892 records32891_32892 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32891
    maskCheck32891 AlignedValid.nil

def missing32890_32892 : List (BitVec (edgeCount 12)) :=
  missing32890_32891 ++ missing32891_32892
abbrev records32890_32892 : List Blob :=
  records32890_32891 ++ records32891_32892
theorem aligned32890_32892 :
    AlignedValid 12 4 missing32890_32892 records32890_32892 :=
  aligned32890_32891.append aligned32891_32892

def missing32888_32892 : List (BitVec (edgeCount 12)) :=
  missing32888_32890 ++ missing32890_32892
abbrev records32888_32892 : List Blob :=
  records32888_32890 ++ records32890_32892
theorem aligned32888_32892 :
    AlignedValid 12 4 missing32888_32892 records32888_32892 :=
  aligned32888_32890.append aligned32890_32892

def missing32892_32893 : List (BitVec (edgeCount 12)) :=
  [missing32892]
abbrev records32892_32893 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32892]
theorem aligned32892_32893 :
    AlignedValid 12 4 missing32892_32893 records32892_32893 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32892
    maskCheck32892 AlignedValid.nil

def missing32893_32894 : List (BitVec (edgeCount 12)) :=
  [missing32893]
abbrev records32893_32894 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32893]
theorem aligned32893_32894 :
    AlignedValid 12 4 missing32893_32894 records32893_32894 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32893
    maskCheck32893 AlignedValid.nil

def missing32892_32894 : List (BitVec (edgeCount 12)) :=
  missing32892_32893 ++ missing32893_32894
abbrev records32892_32894 : List Blob :=
  records32892_32893 ++ records32893_32894
theorem aligned32892_32894 :
    AlignedValid 12 4 missing32892_32894 records32892_32894 :=
  aligned32892_32893.append aligned32893_32894

def missing32894_32895 : List (BitVec (edgeCount 12)) :=
  [missing32894]
abbrev records32894_32895 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32894]
theorem aligned32894_32895 :
    AlignedValid 12 4 missing32894_32895 records32894_32895 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32894
    maskCheck32894 AlignedValid.nil

def missing32895_32896 : List (BitVec (edgeCount 12)) :=
  [missing32895]
abbrev records32895_32896 : List Blob :=
  [StrongPackedBucketN12A4Shard256.record32895]
theorem aligned32895_32896 :
    AlignedValid 12 4 missing32895_32896 records32895_32896 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard256.check32895
    maskCheck32895 AlignedValid.nil

def missing32894_32896 : List (BitVec (edgeCount 12)) :=
  missing32894_32895 ++ missing32895_32896
abbrev records32894_32896 : List Blob :=
  records32894_32895 ++ records32895_32896
theorem aligned32894_32896 :
    AlignedValid 12 4 missing32894_32896 records32894_32896 :=
  aligned32894_32895.append aligned32895_32896

def missing32892_32896 : List (BitVec (edgeCount 12)) :=
  missing32892_32894 ++ missing32894_32896
abbrev records32892_32896 : List Blob :=
  records32892_32894 ++ records32894_32896
theorem aligned32892_32896 :
    AlignedValid 12 4 missing32892_32896 records32892_32896 :=
  aligned32892_32894.append aligned32894_32896

def missing32888_32896 : List (BitVec (edgeCount 12)) :=
  missing32888_32892 ++ missing32892_32896
abbrev records32888_32896 : List Blob :=
  records32888_32892 ++ records32892_32896
theorem aligned32888_32896 :
    AlignedValid 12 4 missing32888_32896 records32888_32896 :=
  aligned32888_32892.append aligned32892_32896

def missing32880_32896 : List (BitVec (edgeCount 12)) :=
  missing32880_32888 ++ missing32888_32896
abbrev records32880_32896 : List Blob :=
  records32880_32888 ++ records32888_32896
theorem aligned32880_32896 :
    AlignedValid 12 4 missing32880_32896 records32880_32896 :=
  aligned32880_32888.append aligned32888_32896

def missing32864_32896 : List (BitVec (edgeCount 12)) :=
  missing32864_32880 ++ missing32880_32896
abbrev records32864_32896 : List Blob :=
  records32864_32880 ++ records32880_32896
theorem aligned32864_32896 :
    AlignedValid 12 4 missing32864_32896 records32864_32896 :=
  aligned32864_32880.append aligned32880_32896

def missing32832_32896 : List (BitVec (edgeCount 12)) :=
  missing32832_32864 ++ missing32864_32896
abbrev records32832_32896 : List Blob :=
  records32832_32864 ++ records32864_32896
theorem aligned32832_32896 :
    AlignedValid 12 4 missing32832_32896 records32832_32896 :=
  aligned32832_32864.append aligned32864_32896

def missing32768_32896 : List (BitVec (edgeCount 12)) :=
  missing32768_32832 ++ missing32832_32896
abbrev records32768_32896 : List Blob :=
  records32768_32832 ++ records32832_32896
theorem aligned32768_32896 :
    AlignedValid 12 4 missing32768_32896 records32768_32896 :=
  aligned32768_32832.append aligned32832_32896

abbrev missing : List (BitVec (edgeCount 12)) := missing32768_32896
abbrev records : List Blob := records32768_32896
theorem aligned : AlignedValid 12 4 missing records := aligned32768_32896

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard256
