/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard271

/-! Decode-only alignment checks for n=12, a=4, records 34688--34815. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard271

open PackedBucketCertificate

def missing34688 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3067307657804152832
theorem maskCheck34688 :
    checkMaskFor missing34688 StrongPackedBucketN12A4Shard271.record34688 = true := by
  decide

def missing34689 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3211422845880008704
theorem maskCheck34689 :
    checkMaskFor missing34689 StrongPackedBucketN12A4Shard271.record34689 = true := by
  decide

def missing34690 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4076113974335143936
theorem maskCheck34690 :
    checkMaskFor missing34690 StrongPackedBucketN12A4Shard271.record34690 = true := by
  decide

def missing34691 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4868747508752351232
theorem maskCheck34691 :
    checkMaskFor missing34691 StrongPackedBucketN12A4Shard271.record34691 = true := by
  decide

def missing34692 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5012862696828207104
theorem maskCheck34692 :
    checkMaskFor missing34692 StrongPackedBucketN12A4Shard271.record34692 = true := by
  decide

def missing34693 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5120949087885099008
theorem maskCheck34693 :
    checkMaskFor missing34693 StrongPackedBucketN12A4Shard271.record34693 = true := by
  decide

def missing34694 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5301093072979918848
theorem maskCheck34694 :
    checkMaskFor missing34694 StrongPackedBucketN12A4Shard271.record34694 = true := by
  decide

def missing34695 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5409179464036810752
theorem maskCheck34695 :
    checkMaskFor missing34695 StrongPackedBucketN12A4Shard271.record34695 = true := by
  decide

def missing34696 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5553294652112666624
theorem maskCheck34696 :
    checkMaskFor missing34696 StrongPackedBucketN12A4Shard271.record34696 = true := by
  decide

def missing34697 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6417985780567801856
theorem maskCheck34697 :
    checkMaskFor missing34697 StrongPackedBucketN12A4Shard271.record34697 = true := by
  decide

def missing34698 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7030475329890189312
theorem maskCheck34698 :
    checkMaskFor missing34698 StrongPackedBucketN12A4Shard271.record34698 = true := by
  decide

def missing34699 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9480433527179739136
theorem maskCheck34699 :
    checkMaskFor missing34699 StrongPackedBucketN12A4Shard271.record34699 = true := by
  decide

def missing34700 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9696606309293522944
theorem maskCheck34700 :
    checkMaskFor missing34700 StrongPackedBucketN12A4Shard271.record34700 = true := by
  decide

def missing34701 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9732635106312486912
theorem maskCheck34701 :
    checkMaskFor missing34701 StrongPackedBucketN12A4Shard271.record34701 = true := by
  decide

def missing34702 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9984836685445234688
theorem maskCheck34702 :
    checkMaskFor missing34702 StrongPackedBucketN12A4Shard271.record34702 = true := by
  decide

def missing34703 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10020865482464198656
theorem maskCheck34703 :
    checkMaskFor missing34703 StrongPackedBucketN12A4Shard271.record34703 = true := by
  decide

def missing34704 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10237038264577982464
theorem maskCheck34704 :
    checkMaskFor missing34704 StrongPackedBucketN12A4Shard271.record34704 = true := by
  decide

def missing34705 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11101729393033117696
theorem maskCheck34705 :
    checkMaskFor missing34705 StrongPackedBucketN12A4Shard271.record34705 = true := by
  decide

def missing34706 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11714218942355505152
theorem maskCheck34706 :
    checkMaskFor missing34706 StrongPackedBucketN12A4Shard271.record34706 = true := by
  decide

def missing34707 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14056090748588163072
theorem maskCheck34707 :
    checkMaskFor missing34707 StrongPackedBucketN12A4Shard271.record34707 = true := by
  decide

def missing34708 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20865533385172353024
theorem maskCheck34708 :
    checkMaskFor missing34708 StrongPackedBucketN12A4Shard271.record34708 = true := by
  decide

def missing34709 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20937590979210280960
theorem maskCheck34709 :
    checkMaskFor missing34709 StrongPackedBucketN12A4Shard271.record34709 = true := by
  decide

def missing34710 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21081706167286136832
theorem maskCheck34710 :
    checkMaskFor missing34710 StrongPackedBucketN12A4Shard271.record34710 = true := by
  decide

def missing34711 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21369936543437848576
theorem maskCheck34711 :
    checkMaskFor missing34711 StrongPackedBucketN12A4Shard271.record34711 = true := by
  decide

def missing34712 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37150549637744066560
theorem maskCheck34712 :
    checkMaskFor missing34712 StrongPackedBucketN12A4Shard271.record34712 = true := by
  decide

def missing34713 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41618120468095598592
theorem maskCheck34713 :
    checkMaskFor missing34713 StrongPackedBucketN12A4Shard271.record34713 = true := by
  decide

def missing34714 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41726206859152490496
theorem maskCheck34714 :
    checkMaskFor missing34714 StrongPackedBucketN12A4Shard271.record34714 = true := by
  decide

def missing34715 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41870322047228346368
theorem maskCheck34715 :
    checkMaskFor missing34715 StrongPackedBucketN12A4Shard271.record34715 = true := by
  decide

def missing34716 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42158552423380058112
theorem maskCheck34716 :
    checkMaskFor missing34716 StrongPackedBucketN12A4Shard271.record34716 = true := by
  decide

def missing34717 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46301864080560914432
theorem maskCheck34717 :
    checkMaskFor missing34717 StrongPackedBucketN12A4Shard271.record34717 = true := by
  decide

def missing34718 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46337892877579878400
theorem maskCheck34718 :
    checkMaskFor missing34718 StrongPackedBucketN12A4Shard271.record34718 = true := by
  decide

def missing34719 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46554065659693662208
theorem maskCheck34719 :
    checkMaskFor missing34719 StrongPackedBucketN12A4Shard271.record34719 = true := by
  decide

def missing34720 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46842296035845373952
theorem maskCheck34720 :
    checkMaskFor missing34720 StrongPackedBucketN12A4Shard271.record34720 = true := by
  decide

def missing34721 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 560737805823672320
theorem maskCheck34721 :
    checkMaskFor missing34721 StrongPackedBucketN12A4Shard271.record34721 = true := by
  decide

def missing34722 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 993083370051239936
theorem maskCheck34722 :
    checkMaskFor missing34722 StrongPackedBucketN12A4Shard271.record34722 = true := by
  decide

def missing34723 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1101169761108131840
theorem maskCheck34723 :
    checkMaskFor missing34723 StrongPackedBucketN12A4Shard271.record34723 = true := by
  decide

def missing34724 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2109976077639122944
theorem maskCheck34724 :
    checkMaskFor missing34724 StrongPackedBucketN12A4Shard271.record34724 = true := by
  decide

def missing34725 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2578350438885654528
theorem maskCheck34725 :
    checkMaskFor missing34725 StrongPackedBucketN12A4Shard271.record34725 = true := by
  decide

def missing34726 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4884193448099348480
theorem maskCheck34726 :
    checkMaskFor missing34726 StrongPackedBucketN12A4Shard271.record34726 = true := by
  decide

def missing34727 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5028308636175204352
theorem maskCheck34727 :
    checkMaskFor missing34727 StrongPackedBucketN12A4Shard271.record34727 = true := by
  decide

def missing34728 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5136395027232096256
theorem maskCheck34728 :
    checkMaskFor missing34728 StrongPackedBucketN12A4Shard271.record34728 = true := by
  decide

def missing34729 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5568740591459663872
theorem maskCheck34729 :
    checkMaskFor missing34729 StrongPackedBucketN12A4Shard271.record34729 = true := by
  decide

def missing34730 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7045921269237186560
theorem maskCheck34730 :
    checkMaskFor missing34730 StrongPackedBucketN12A4Shard271.record34730 = true := by
  decide

def missing34731 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14071536687935160320
theorem maskCheck34731 :
    checkMaskFor missing34731 StrongPackedBucketN12A4Shard271.record34731 = true := by
  decide

def missing34732 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20880979324519350272
theorem maskCheck34732 :
    checkMaskFor missing34732 StrongPackedBucketN12A4Shard271.record34732 = true := by
  decide

def missing34733 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57702409877900525568
theorem maskCheck34733 :
    checkMaskFor missing34733 StrongPackedBucketN12A4Shard271.record34733 = true := by
  decide

def missing34734 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2673027598447050752
theorem maskCheck34734 :
    checkMaskFor missing34734 StrongPackedBucketN12A4Shard271.record34734 = true := by
  decide

def missing34735 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11608169259150114816
theorem maskCheck34735 :
    checkMaskFor missing34735 StrongPackedBucketN12A4Shard271.record34735 = true := by
  decide

def missing34736 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 267964659942850560
theorem maskCheck34736 :
    checkMaskFor missing34736 StrongPackedBucketN12A4Shard271.record34736 = true := by
  decide

def missing34737 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2537778872137580544
theorem maskCheck34737 :
    checkMaskFor missing34737 StrongPackedBucketN12A4Shard271.record34737 = true := by
  decide

def missing34738 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 504861312094863360
theorem maskCheck34738 :
    checkMaskFor missing34738 StrongPackedBucketN12A4Shard271.record34738 = true := by
  decide

def missing34739 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 793091688246575104
theorem maskCheck34739 :
    checkMaskFor missing34739 StrongPackedBucketN12A4Shard271.record34739 = true := by
  decide

def missing34740 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1369833915526709248
theorem maskCheck34740 :
    checkMaskFor missing34740 StrongPackedBucketN12A4Shard271.record34740 = true := by
  decide

def missing34741 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 759068400436674560
theorem maskCheck34741 :
    checkMaskFor missing34741 StrongPackedBucketN12A4Shard271.record34741 = true := by
  decide

def missing34742 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 254876348403712000
theorem maskCheck34742 :
    checkMaskFor missing34742 StrongPackedBucketN12A4Shard271.record34742 = true := by
  decide

def missing34743 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 398991536479567872
theorem maskCheck34743 :
    checkMaskFor missing34743 StrongPackedBucketN12A4Shard271.record34743 = true := by
  decide

def missing34744 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 471049130517495808
theorem maskCheck34744 :
    checkMaskFor missing34744 StrongPackedBucketN12A4Shard271.record34744 = true := by
  decide

def missing34745 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 507077927536459776
theorem maskCheck34745 :
    checkMaskFor missing34745 StrongPackedBucketN12A4Shard271.record34745 = true := by
  decide

def missing34746 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 687221912631279616
theorem maskCheck34746 :
    checkMaskFor missing34746 StrongPackedBucketN12A4Shard271.record34746 = true := by
  decide

def missing34747 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 759279506669207552
theorem maskCheck34747 :
    checkMaskFor missing34747 StrongPackedBucketN12A4Shard271.record34747 = true := by
  decide

def missing34748 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2416604169541550080
theorem maskCheck34748 :
    checkMaskFor missing34748 StrongPackedBucketN12A4Shard271.record34748 = true := by
  decide

def missing34749 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4722447178755244032
theorem maskCheck34749 :
    checkMaskFor missing34749 StrongPackedBucketN12A4Shard271.record34749 = true := by
  decide

def missing34750 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4794504772793171968
theorem maskCheck34750 :
    checkMaskFor missing34750 StrongPackedBucketN12A4Shard271.record34750 = true := by
  decide

def missing34751 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6992261390949974016
theorem maskCheck34751 :
    checkMaskFor missing34751 StrongPackedBucketN12A4Shard271.record34751 = true := by
  decide

def missing34752 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7064318984987901952
theorem maskCheck34752 :
    checkMaskFor missing34752 StrongPackedBucketN12A4Shard271.record34752 = true := by
  decide

def missing34753 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 255157823380422656
theorem maskCheck34753 :
    checkMaskFor missing34753 StrongPackedBucketN12A4Shard271.record34753 = true := by
  decide

def missing34754 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 471330605494206464
theorem maskCheck34754 :
    checkMaskFor missing34754 StrongPackedBucketN12A4Shard271.record34754 = true := by
  decide

def missing34755 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 759560981645918208
theorem maskCheck34755 :
    checkMaskFor missing34755 StrongPackedBucketN12A4Shard271.record34755 = true := by
  decide

def missing34756 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1336021733949341696
theorem maskCheck34756 :
    checkMaskFor missing34756 StrongPackedBucketN12A4Shard271.record34756 = true := by
  decide

def missing34757 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2416885644518260736
theorem maskCheck34757 :
    checkMaskFor missing34757 StrongPackedBucketN12A4Shard271.record34757 = true := by
  decide

def missing34758 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4794786247769882624
theorem maskCheck34758 :
    checkMaskFor missing34758 StrongPackedBucketN12A4Shard271.record34758 = true := by
  decide

def missing34759 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6992542865926684672
theorem maskCheck34759 :
    checkMaskFor missing34759 StrongPackedBucketN12A4Shard271.record34759 = true := by
  decide

def missing34760 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7064600459964612608
theorem maskCheck34760 :
    checkMaskFor missing34760 StrongPackedBucketN12A4Shard271.record34760 = true := by
  decide

def missing34761 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14126244675681550336
theorem maskCheck34761 :
    checkMaskFor missing34761 StrongPackedBucketN12A4Shard271.record34761 = true := by
  decide

def missing34762 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14990935804136685568
theorem maskCheck34762 :
    checkMaskFor missing34762 StrongPackedBucketN12A4Shard271.record34762 = true := by
  decide

def missing34763 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 259098473054371840
theorem maskCheck34763 :
    checkMaskFor missing34763 StrongPackedBucketN12A4Shard271.record34763 = true := by
  decide

def missing34764 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 403213661130227712
theorem maskCheck34764 :
    checkMaskFor missing34764 StrongPackedBucketN12A4Shard271.record34764 = true := by
  decide

def missing34765 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 691444037281939456
theorem maskCheck34765 :
    checkMaskFor missing34765 StrongPackedBucketN12A4Shard271.record34765 = true := by
  decide

def missing34766 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2528912685249101824
theorem maskCheck34766 :
    checkMaskFor missing34766 StrongPackedBucketN12A4Shard271.record34766 = true := by
  decide

def missing34767 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2673027873324957696
theorem maskCheck34767 :
    checkMaskFor missing34767 StrongPackedBucketN12A4Shard271.record34767 = true := by
  decide

def missing34768 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2961258249476669440
theorem maskCheck34768 :
    checkMaskFor missing34768 StrongPackedBucketN12A4Shard271.record34768 = true := by
  decide

def missing34769 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7068541109638561792
theorem maskCheck34769 :
    checkMaskFor missing34769 StrongPackedBucketN12A4Shard271.record34769 = true := by
  decide

def missing34770 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9338355321833291776
theorem maskCheck34770 :
    checkMaskFor missing34770 StrongPackedBucketN12A4Shard271.record34770 = true := by
  decide

def missing34771 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11608169534028021760
theorem maskCheck34771 :
    checkMaskFor missing34771 StrongPackedBucketN12A4Shard271.record34771 = true := by
  decide

def missing34772 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16147797958417481728
theorem maskCheck34772 :
    checkMaskFor missing34772 StrongPackedBucketN12A4Shard271.record34772 = true := by
  decide

def missing34773 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 259239210542727168
theorem maskCheck34773 :
    checkMaskFor missing34773 StrongPackedBucketN12A4Shard271.record34773 = true := by
  decide

def missing34774 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 403354398618583040
theorem maskCheck34774 :
    checkMaskFor missing34774 StrongPackedBucketN12A4Shard271.record34774 = true := by
  decide

def missing34775 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 691584774770294784
theorem maskCheck34775 :
    checkMaskFor missing34775 StrongPackedBucketN12A4Shard271.record34775 = true := by
  decide

def missing34776 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2420967031680565248
theorem maskCheck34776 :
    checkMaskFor missing34776 StrongPackedBucketN12A4Shard271.record34776 = true := by
  decide

def missing34777 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2529053422737457152
theorem maskCheck34777 :
    checkMaskFor missing34777 StrongPackedBucketN12A4Shard271.record34777 = true := by
  decide

def missing34778 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2673168610813313024
theorem maskCheck34778 :
    checkMaskFor missing34778 StrongPackedBucketN12A4Shard271.record34778 = true := by
  decide

def missing34779 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 259520685519437824
theorem maskCheck34779 :
    checkMaskFor missing34779 StrongPackedBucketN12A4Shard271.record34779 = true := by
  decide

def missing34780 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 403635873595293696
theorem maskCheck34780 :
    checkMaskFor missing34780 StrongPackedBucketN12A4Shard271.record34780 = true := by
  decide

def missing34781 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1268327002050428928
theorem maskCheck34781 :
    checkMaskFor missing34781 StrongPackedBucketN12A4Shard271.record34781 = true := by
  decide

def missing34782 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2529334897714167808
theorem maskCheck34782 :
    checkMaskFor missing34782 StrongPackedBucketN12A4Shard271.record34782 = true := by
  decide

def missing34783 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9663036707469033472
theorem maskCheck34783 :
    checkMaskFor missing34783 StrongPackedBucketN12A4Shard271.record34783 = true := by
  decide

def missing34784 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9448728697075957760
theorem maskCheck34784 :
    checkMaskFor missing34784 StrongPackedBucketN12A4Shard271.record34784 = true := by
  decide

def missing34785 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 261631747844767744
theorem maskCheck34785 :
    checkMaskFor missing34785 StrongPackedBucketN12A4Shard271.record34785 = true := by
  decide

def missing34786 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 405746935920623616
theorem maskCheck34786 :
    checkMaskFor missing34786 StrongPackedBucketN12A4Shard271.record34786 = true := by
  decide

def missing34787 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 477804529958551552
theorem maskCheck34787 :
    checkMaskFor missing34787 StrongPackedBucketN12A4Shard271.record34787 = true := by
  decide

def missing34788 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 693977312072335360
theorem maskCheck34788 :
    checkMaskFor missing34788 StrongPackedBucketN12A4Shard271.record34788 = true := by
  decide

def missing34789 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 766034906110263296
theorem maskCheck34789 :
    checkMaskFor missing34789 StrongPackedBucketN12A4Shard271.record34789 = true := by
  decide

def missing34790 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2423359568982605824
theorem maskCheck34790 :
    checkMaskFor missing34790 StrongPackedBucketN12A4Shard271.record34790 = true := by
  decide

def missing34791 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2495417163020533760
theorem maskCheck34791 :
    checkMaskFor missing34791 StrongPackedBucketN12A4Shard271.record34791 = true := by
  decide

def missing34792 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2531445960039497728
theorem maskCheck34792 :
    checkMaskFor missing34792 StrongPackedBucketN12A4Shard271.record34792 = true := by
  decide

def missing34793 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9412946190661615616
theorem maskCheck34793 :
    checkMaskFor missing34793 StrongPackedBucketN12A4Shard271.record34793 = true := by
  decide

def missing34794 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 261913222821478400
theorem maskCheck34794 :
    checkMaskFor missing34794 StrongPackedBucketN12A4Shard271.record34794 = true := by
  decide

def missing34795 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 478086004935262208
theorem maskCheck34795 :
    checkMaskFor missing34795 StrongPackedBucketN12A4Shard271.record34795 = true := by
  decide

def missing34796 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1270719539352469504
theorem maskCheck34796 :
    checkMaskFor missing34796 StrongPackedBucketN12A4Shard271.record34796 = true := by
  decide

def missing34797 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1342777133390397440
theorem maskCheck34797 :
    checkMaskFor missing34797 StrongPackedBucketN12A4Shard271.record34797 = true := by
  decide

def missing34798 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2495698637997244416
theorem maskCheck34798 :
    checkMaskFor missing34798 StrongPackedBucketN12A4Shard271.record34798 = true := by
  decide

def missing34799 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2531727435016208384
theorem maskCheck34799 :
    checkMaskFor missing34799 StrongPackedBucketN12A4Shard271.record34799 = true := by
  decide

def missing34800 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7215471047481524224
theorem maskCheck34800 :
    checkMaskFor missing34800 StrongPackedBucketN12A4Shard271.record34800 = true := by
  decide

def missing34801 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8080162175936659456
theorem maskCheck34801 :
    checkMaskFor missing34801 StrongPackedBucketN12A4Shard271.record34801 = true := by
  decide

def missing34802 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9413227665638326272
theorem maskCheck34802 :
    checkMaskFor missing34802 StrongPackedBucketN12A4Shard271.record34802 = true := by
  decide

def missing34803 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 263602072681742336
theorem maskCheck34803 :
    checkMaskFor missing34803 StrongPackedBucketN12A4Shard271.record34803 = true := by
  decide

def missing34804 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 479774854795526144
theorem maskCheck34804 :
    checkMaskFor missing34804 StrongPackedBucketN12A4Shard271.record34804 = true := by
  decide

def missing34805 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 768005230947237888
theorem maskCheck34805 :
    checkMaskFor missing34805 StrongPackedBucketN12A4Shard271.record34805 = true := by
  decide

def missing34806 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2425329893819580416
theorem maskCheck34806 :
    checkMaskFor missing34806 StrongPackedBucketN12A4Shard271.record34806 = true := by
  decide

def missing34807 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2497387487857508352
theorem maskCheck34807 :
    checkMaskFor missing34807 StrongPackedBucketN12A4Shard271.record34807 = true := by
  decide

def missing34808 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2533416284876472320
theorem maskCheck34808 :
    checkMaskFor missing34808 StrongPackedBucketN12A4Shard271.record34808 = true := by
  decide

def missing34809 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2677531472952328192
theorem maskCheck34809 :
    checkMaskFor missing34809 StrongPackedBucketN12A4Shard271.record34809 = true := by
  decide

def missing34810 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2965761849104039936
theorem maskCheck34810 :
    checkMaskFor missing34810 StrongPackedBucketN12A4Shard271.record34810 = true := by
  decide

def missing34811 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4803230497071202304
theorem maskCheck34811 :
    checkMaskFor missing34811 StrongPackedBucketN12A4Shard271.record34811 = true := by
  decide

def missing34812 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7000987115228004352
theorem maskCheck34812 :
    checkMaskFor missing34812 StrongPackedBucketN12A4Shard271.record34812 = true := by
  decide

def missing34813 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7073044709265932288
theorem maskCheck34813 :
    checkMaskFor missing34813 StrongPackedBucketN12A4Shard271.record34813 = true := by
  decide

def missing34814 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9414916515498590208
theorem maskCheck34814 :
    checkMaskFor missing34814 StrongPackedBucketN12A4Shard271.record34814 = true := by
  decide

def missing34815 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 252695879406878720
theorem maskCheck34815 :
    checkMaskFor missing34815 StrongPackedBucketN12A4Shard271.record34815 = true := by
  decide

def missing34688_34689 : List (BitVec (edgeCount 12)) :=
  [missing34688]
abbrev records34688_34689 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34688]
theorem aligned34688_34689 :
    AlignedValid 12 4 missing34688_34689 records34688_34689 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34688
    maskCheck34688 AlignedValid.nil

def missing34689_34690 : List (BitVec (edgeCount 12)) :=
  [missing34689]
abbrev records34689_34690 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34689]
theorem aligned34689_34690 :
    AlignedValid 12 4 missing34689_34690 records34689_34690 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34689
    maskCheck34689 AlignedValid.nil

def missing34688_34690 : List (BitVec (edgeCount 12)) :=
  missing34688_34689 ++ missing34689_34690
abbrev records34688_34690 : List Blob :=
  records34688_34689 ++ records34689_34690
theorem aligned34688_34690 :
    AlignedValid 12 4 missing34688_34690 records34688_34690 :=
  aligned34688_34689.append aligned34689_34690

def missing34690_34691 : List (BitVec (edgeCount 12)) :=
  [missing34690]
abbrev records34690_34691 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34690]
theorem aligned34690_34691 :
    AlignedValid 12 4 missing34690_34691 records34690_34691 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34690
    maskCheck34690 AlignedValid.nil

def missing34691_34692 : List (BitVec (edgeCount 12)) :=
  [missing34691]
abbrev records34691_34692 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34691]
theorem aligned34691_34692 :
    AlignedValid 12 4 missing34691_34692 records34691_34692 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34691
    maskCheck34691 AlignedValid.nil

def missing34690_34692 : List (BitVec (edgeCount 12)) :=
  missing34690_34691 ++ missing34691_34692
abbrev records34690_34692 : List Blob :=
  records34690_34691 ++ records34691_34692
theorem aligned34690_34692 :
    AlignedValid 12 4 missing34690_34692 records34690_34692 :=
  aligned34690_34691.append aligned34691_34692

def missing34688_34692 : List (BitVec (edgeCount 12)) :=
  missing34688_34690 ++ missing34690_34692
abbrev records34688_34692 : List Blob :=
  records34688_34690 ++ records34690_34692
theorem aligned34688_34692 :
    AlignedValid 12 4 missing34688_34692 records34688_34692 :=
  aligned34688_34690.append aligned34690_34692

def missing34692_34693 : List (BitVec (edgeCount 12)) :=
  [missing34692]
abbrev records34692_34693 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34692]
theorem aligned34692_34693 :
    AlignedValid 12 4 missing34692_34693 records34692_34693 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34692
    maskCheck34692 AlignedValid.nil

def missing34693_34694 : List (BitVec (edgeCount 12)) :=
  [missing34693]
abbrev records34693_34694 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34693]
theorem aligned34693_34694 :
    AlignedValid 12 4 missing34693_34694 records34693_34694 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34693
    maskCheck34693 AlignedValid.nil

def missing34692_34694 : List (BitVec (edgeCount 12)) :=
  missing34692_34693 ++ missing34693_34694
abbrev records34692_34694 : List Blob :=
  records34692_34693 ++ records34693_34694
theorem aligned34692_34694 :
    AlignedValid 12 4 missing34692_34694 records34692_34694 :=
  aligned34692_34693.append aligned34693_34694

def missing34694_34695 : List (BitVec (edgeCount 12)) :=
  [missing34694]
abbrev records34694_34695 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34694]
theorem aligned34694_34695 :
    AlignedValid 12 4 missing34694_34695 records34694_34695 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34694
    maskCheck34694 AlignedValid.nil

def missing34695_34696 : List (BitVec (edgeCount 12)) :=
  [missing34695]
abbrev records34695_34696 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34695]
theorem aligned34695_34696 :
    AlignedValid 12 4 missing34695_34696 records34695_34696 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34695
    maskCheck34695 AlignedValid.nil

def missing34694_34696 : List (BitVec (edgeCount 12)) :=
  missing34694_34695 ++ missing34695_34696
abbrev records34694_34696 : List Blob :=
  records34694_34695 ++ records34695_34696
theorem aligned34694_34696 :
    AlignedValid 12 4 missing34694_34696 records34694_34696 :=
  aligned34694_34695.append aligned34695_34696

def missing34692_34696 : List (BitVec (edgeCount 12)) :=
  missing34692_34694 ++ missing34694_34696
abbrev records34692_34696 : List Blob :=
  records34692_34694 ++ records34694_34696
theorem aligned34692_34696 :
    AlignedValid 12 4 missing34692_34696 records34692_34696 :=
  aligned34692_34694.append aligned34694_34696

def missing34688_34696 : List (BitVec (edgeCount 12)) :=
  missing34688_34692 ++ missing34692_34696
abbrev records34688_34696 : List Blob :=
  records34688_34692 ++ records34692_34696
theorem aligned34688_34696 :
    AlignedValid 12 4 missing34688_34696 records34688_34696 :=
  aligned34688_34692.append aligned34692_34696

def missing34696_34697 : List (BitVec (edgeCount 12)) :=
  [missing34696]
abbrev records34696_34697 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34696]
theorem aligned34696_34697 :
    AlignedValid 12 4 missing34696_34697 records34696_34697 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34696
    maskCheck34696 AlignedValid.nil

def missing34697_34698 : List (BitVec (edgeCount 12)) :=
  [missing34697]
abbrev records34697_34698 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34697]
theorem aligned34697_34698 :
    AlignedValid 12 4 missing34697_34698 records34697_34698 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34697
    maskCheck34697 AlignedValid.nil

def missing34696_34698 : List (BitVec (edgeCount 12)) :=
  missing34696_34697 ++ missing34697_34698
abbrev records34696_34698 : List Blob :=
  records34696_34697 ++ records34697_34698
theorem aligned34696_34698 :
    AlignedValid 12 4 missing34696_34698 records34696_34698 :=
  aligned34696_34697.append aligned34697_34698

def missing34698_34699 : List (BitVec (edgeCount 12)) :=
  [missing34698]
abbrev records34698_34699 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34698]
theorem aligned34698_34699 :
    AlignedValid 12 4 missing34698_34699 records34698_34699 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34698
    maskCheck34698 AlignedValid.nil

def missing34699_34700 : List (BitVec (edgeCount 12)) :=
  [missing34699]
abbrev records34699_34700 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34699]
theorem aligned34699_34700 :
    AlignedValid 12 4 missing34699_34700 records34699_34700 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34699
    maskCheck34699 AlignedValid.nil

def missing34698_34700 : List (BitVec (edgeCount 12)) :=
  missing34698_34699 ++ missing34699_34700
abbrev records34698_34700 : List Blob :=
  records34698_34699 ++ records34699_34700
theorem aligned34698_34700 :
    AlignedValid 12 4 missing34698_34700 records34698_34700 :=
  aligned34698_34699.append aligned34699_34700

def missing34696_34700 : List (BitVec (edgeCount 12)) :=
  missing34696_34698 ++ missing34698_34700
abbrev records34696_34700 : List Blob :=
  records34696_34698 ++ records34698_34700
theorem aligned34696_34700 :
    AlignedValid 12 4 missing34696_34700 records34696_34700 :=
  aligned34696_34698.append aligned34698_34700

def missing34700_34701 : List (BitVec (edgeCount 12)) :=
  [missing34700]
abbrev records34700_34701 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34700]
theorem aligned34700_34701 :
    AlignedValid 12 4 missing34700_34701 records34700_34701 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34700
    maskCheck34700 AlignedValid.nil

def missing34701_34702 : List (BitVec (edgeCount 12)) :=
  [missing34701]
abbrev records34701_34702 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34701]
theorem aligned34701_34702 :
    AlignedValid 12 4 missing34701_34702 records34701_34702 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34701
    maskCheck34701 AlignedValid.nil

def missing34700_34702 : List (BitVec (edgeCount 12)) :=
  missing34700_34701 ++ missing34701_34702
abbrev records34700_34702 : List Blob :=
  records34700_34701 ++ records34701_34702
theorem aligned34700_34702 :
    AlignedValid 12 4 missing34700_34702 records34700_34702 :=
  aligned34700_34701.append aligned34701_34702

def missing34702_34703 : List (BitVec (edgeCount 12)) :=
  [missing34702]
abbrev records34702_34703 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34702]
theorem aligned34702_34703 :
    AlignedValid 12 4 missing34702_34703 records34702_34703 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34702
    maskCheck34702 AlignedValid.nil

def missing34703_34704 : List (BitVec (edgeCount 12)) :=
  [missing34703]
abbrev records34703_34704 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34703]
theorem aligned34703_34704 :
    AlignedValid 12 4 missing34703_34704 records34703_34704 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34703
    maskCheck34703 AlignedValid.nil

def missing34702_34704 : List (BitVec (edgeCount 12)) :=
  missing34702_34703 ++ missing34703_34704
abbrev records34702_34704 : List Blob :=
  records34702_34703 ++ records34703_34704
theorem aligned34702_34704 :
    AlignedValid 12 4 missing34702_34704 records34702_34704 :=
  aligned34702_34703.append aligned34703_34704

def missing34700_34704 : List (BitVec (edgeCount 12)) :=
  missing34700_34702 ++ missing34702_34704
abbrev records34700_34704 : List Blob :=
  records34700_34702 ++ records34702_34704
theorem aligned34700_34704 :
    AlignedValid 12 4 missing34700_34704 records34700_34704 :=
  aligned34700_34702.append aligned34702_34704

def missing34696_34704 : List (BitVec (edgeCount 12)) :=
  missing34696_34700 ++ missing34700_34704
abbrev records34696_34704 : List Blob :=
  records34696_34700 ++ records34700_34704
theorem aligned34696_34704 :
    AlignedValid 12 4 missing34696_34704 records34696_34704 :=
  aligned34696_34700.append aligned34700_34704

def missing34688_34704 : List (BitVec (edgeCount 12)) :=
  missing34688_34696 ++ missing34696_34704
abbrev records34688_34704 : List Blob :=
  records34688_34696 ++ records34696_34704
theorem aligned34688_34704 :
    AlignedValid 12 4 missing34688_34704 records34688_34704 :=
  aligned34688_34696.append aligned34696_34704

def missing34704_34705 : List (BitVec (edgeCount 12)) :=
  [missing34704]
abbrev records34704_34705 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34704]
theorem aligned34704_34705 :
    AlignedValid 12 4 missing34704_34705 records34704_34705 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34704
    maskCheck34704 AlignedValid.nil

def missing34705_34706 : List (BitVec (edgeCount 12)) :=
  [missing34705]
abbrev records34705_34706 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34705]
theorem aligned34705_34706 :
    AlignedValid 12 4 missing34705_34706 records34705_34706 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34705
    maskCheck34705 AlignedValid.nil

def missing34704_34706 : List (BitVec (edgeCount 12)) :=
  missing34704_34705 ++ missing34705_34706
abbrev records34704_34706 : List Blob :=
  records34704_34705 ++ records34705_34706
theorem aligned34704_34706 :
    AlignedValid 12 4 missing34704_34706 records34704_34706 :=
  aligned34704_34705.append aligned34705_34706

def missing34706_34707 : List (BitVec (edgeCount 12)) :=
  [missing34706]
abbrev records34706_34707 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34706]
theorem aligned34706_34707 :
    AlignedValid 12 4 missing34706_34707 records34706_34707 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34706
    maskCheck34706 AlignedValid.nil

def missing34707_34708 : List (BitVec (edgeCount 12)) :=
  [missing34707]
abbrev records34707_34708 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34707]
theorem aligned34707_34708 :
    AlignedValid 12 4 missing34707_34708 records34707_34708 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34707
    maskCheck34707 AlignedValid.nil

def missing34706_34708 : List (BitVec (edgeCount 12)) :=
  missing34706_34707 ++ missing34707_34708
abbrev records34706_34708 : List Blob :=
  records34706_34707 ++ records34707_34708
theorem aligned34706_34708 :
    AlignedValid 12 4 missing34706_34708 records34706_34708 :=
  aligned34706_34707.append aligned34707_34708

def missing34704_34708 : List (BitVec (edgeCount 12)) :=
  missing34704_34706 ++ missing34706_34708
abbrev records34704_34708 : List Blob :=
  records34704_34706 ++ records34706_34708
theorem aligned34704_34708 :
    AlignedValid 12 4 missing34704_34708 records34704_34708 :=
  aligned34704_34706.append aligned34706_34708

def missing34708_34709 : List (BitVec (edgeCount 12)) :=
  [missing34708]
abbrev records34708_34709 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34708]
theorem aligned34708_34709 :
    AlignedValid 12 4 missing34708_34709 records34708_34709 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34708
    maskCheck34708 AlignedValid.nil

def missing34709_34710 : List (BitVec (edgeCount 12)) :=
  [missing34709]
abbrev records34709_34710 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34709]
theorem aligned34709_34710 :
    AlignedValid 12 4 missing34709_34710 records34709_34710 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34709
    maskCheck34709 AlignedValid.nil

def missing34708_34710 : List (BitVec (edgeCount 12)) :=
  missing34708_34709 ++ missing34709_34710
abbrev records34708_34710 : List Blob :=
  records34708_34709 ++ records34709_34710
theorem aligned34708_34710 :
    AlignedValid 12 4 missing34708_34710 records34708_34710 :=
  aligned34708_34709.append aligned34709_34710

def missing34710_34711 : List (BitVec (edgeCount 12)) :=
  [missing34710]
abbrev records34710_34711 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34710]
theorem aligned34710_34711 :
    AlignedValid 12 4 missing34710_34711 records34710_34711 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34710
    maskCheck34710 AlignedValid.nil

def missing34711_34712 : List (BitVec (edgeCount 12)) :=
  [missing34711]
abbrev records34711_34712 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34711]
theorem aligned34711_34712 :
    AlignedValid 12 4 missing34711_34712 records34711_34712 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34711
    maskCheck34711 AlignedValid.nil

def missing34710_34712 : List (BitVec (edgeCount 12)) :=
  missing34710_34711 ++ missing34711_34712
abbrev records34710_34712 : List Blob :=
  records34710_34711 ++ records34711_34712
theorem aligned34710_34712 :
    AlignedValid 12 4 missing34710_34712 records34710_34712 :=
  aligned34710_34711.append aligned34711_34712

def missing34708_34712 : List (BitVec (edgeCount 12)) :=
  missing34708_34710 ++ missing34710_34712
abbrev records34708_34712 : List Blob :=
  records34708_34710 ++ records34710_34712
theorem aligned34708_34712 :
    AlignedValid 12 4 missing34708_34712 records34708_34712 :=
  aligned34708_34710.append aligned34710_34712

def missing34704_34712 : List (BitVec (edgeCount 12)) :=
  missing34704_34708 ++ missing34708_34712
abbrev records34704_34712 : List Blob :=
  records34704_34708 ++ records34708_34712
theorem aligned34704_34712 :
    AlignedValid 12 4 missing34704_34712 records34704_34712 :=
  aligned34704_34708.append aligned34708_34712

def missing34712_34713 : List (BitVec (edgeCount 12)) :=
  [missing34712]
abbrev records34712_34713 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34712]
theorem aligned34712_34713 :
    AlignedValid 12 4 missing34712_34713 records34712_34713 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34712
    maskCheck34712 AlignedValid.nil

def missing34713_34714 : List (BitVec (edgeCount 12)) :=
  [missing34713]
abbrev records34713_34714 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34713]
theorem aligned34713_34714 :
    AlignedValid 12 4 missing34713_34714 records34713_34714 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34713
    maskCheck34713 AlignedValid.nil

def missing34712_34714 : List (BitVec (edgeCount 12)) :=
  missing34712_34713 ++ missing34713_34714
abbrev records34712_34714 : List Blob :=
  records34712_34713 ++ records34713_34714
theorem aligned34712_34714 :
    AlignedValid 12 4 missing34712_34714 records34712_34714 :=
  aligned34712_34713.append aligned34713_34714

def missing34714_34715 : List (BitVec (edgeCount 12)) :=
  [missing34714]
abbrev records34714_34715 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34714]
theorem aligned34714_34715 :
    AlignedValid 12 4 missing34714_34715 records34714_34715 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34714
    maskCheck34714 AlignedValid.nil

def missing34715_34716 : List (BitVec (edgeCount 12)) :=
  [missing34715]
abbrev records34715_34716 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34715]
theorem aligned34715_34716 :
    AlignedValid 12 4 missing34715_34716 records34715_34716 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34715
    maskCheck34715 AlignedValid.nil

def missing34714_34716 : List (BitVec (edgeCount 12)) :=
  missing34714_34715 ++ missing34715_34716
abbrev records34714_34716 : List Blob :=
  records34714_34715 ++ records34715_34716
theorem aligned34714_34716 :
    AlignedValid 12 4 missing34714_34716 records34714_34716 :=
  aligned34714_34715.append aligned34715_34716

def missing34712_34716 : List (BitVec (edgeCount 12)) :=
  missing34712_34714 ++ missing34714_34716
abbrev records34712_34716 : List Blob :=
  records34712_34714 ++ records34714_34716
theorem aligned34712_34716 :
    AlignedValid 12 4 missing34712_34716 records34712_34716 :=
  aligned34712_34714.append aligned34714_34716

def missing34716_34717 : List (BitVec (edgeCount 12)) :=
  [missing34716]
abbrev records34716_34717 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34716]
theorem aligned34716_34717 :
    AlignedValid 12 4 missing34716_34717 records34716_34717 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34716
    maskCheck34716 AlignedValid.nil

def missing34717_34718 : List (BitVec (edgeCount 12)) :=
  [missing34717]
abbrev records34717_34718 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34717]
theorem aligned34717_34718 :
    AlignedValid 12 4 missing34717_34718 records34717_34718 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34717
    maskCheck34717 AlignedValid.nil

def missing34716_34718 : List (BitVec (edgeCount 12)) :=
  missing34716_34717 ++ missing34717_34718
abbrev records34716_34718 : List Blob :=
  records34716_34717 ++ records34717_34718
theorem aligned34716_34718 :
    AlignedValid 12 4 missing34716_34718 records34716_34718 :=
  aligned34716_34717.append aligned34717_34718

def missing34718_34719 : List (BitVec (edgeCount 12)) :=
  [missing34718]
abbrev records34718_34719 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34718]
theorem aligned34718_34719 :
    AlignedValid 12 4 missing34718_34719 records34718_34719 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34718
    maskCheck34718 AlignedValid.nil

def missing34719_34720 : List (BitVec (edgeCount 12)) :=
  [missing34719]
abbrev records34719_34720 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34719]
theorem aligned34719_34720 :
    AlignedValid 12 4 missing34719_34720 records34719_34720 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34719
    maskCheck34719 AlignedValid.nil

def missing34718_34720 : List (BitVec (edgeCount 12)) :=
  missing34718_34719 ++ missing34719_34720
abbrev records34718_34720 : List Blob :=
  records34718_34719 ++ records34719_34720
theorem aligned34718_34720 :
    AlignedValid 12 4 missing34718_34720 records34718_34720 :=
  aligned34718_34719.append aligned34719_34720

def missing34716_34720 : List (BitVec (edgeCount 12)) :=
  missing34716_34718 ++ missing34718_34720
abbrev records34716_34720 : List Blob :=
  records34716_34718 ++ records34718_34720
theorem aligned34716_34720 :
    AlignedValid 12 4 missing34716_34720 records34716_34720 :=
  aligned34716_34718.append aligned34718_34720

def missing34712_34720 : List (BitVec (edgeCount 12)) :=
  missing34712_34716 ++ missing34716_34720
abbrev records34712_34720 : List Blob :=
  records34712_34716 ++ records34716_34720
theorem aligned34712_34720 :
    AlignedValid 12 4 missing34712_34720 records34712_34720 :=
  aligned34712_34716.append aligned34716_34720

def missing34704_34720 : List (BitVec (edgeCount 12)) :=
  missing34704_34712 ++ missing34712_34720
abbrev records34704_34720 : List Blob :=
  records34704_34712 ++ records34712_34720
theorem aligned34704_34720 :
    AlignedValid 12 4 missing34704_34720 records34704_34720 :=
  aligned34704_34712.append aligned34712_34720

def missing34688_34720 : List (BitVec (edgeCount 12)) :=
  missing34688_34704 ++ missing34704_34720
abbrev records34688_34720 : List Blob :=
  records34688_34704 ++ records34704_34720
theorem aligned34688_34720 :
    AlignedValid 12 4 missing34688_34720 records34688_34720 :=
  aligned34688_34704.append aligned34704_34720

def missing34720_34721 : List (BitVec (edgeCount 12)) :=
  [missing34720]
abbrev records34720_34721 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34720]
theorem aligned34720_34721 :
    AlignedValid 12 4 missing34720_34721 records34720_34721 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34720
    maskCheck34720 AlignedValid.nil

def missing34721_34722 : List (BitVec (edgeCount 12)) :=
  [missing34721]
abbrev records34721_34722 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34721]
theorem aligned34721_34722 :
    AlignedValid 12 4 missing34721_34722 records34721_34722 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34721
    maskCheck34721 AlignedValid.nil

def missing34720_34722 : List (BitVec (edgeCount 12)) :=
  missing34720_34721 ++ missing34721_34722
abbrev records34720_34722 : List Blob :=
  records34720_34721 ++ records34721_34722
theorem aligned34720_34722 :
    AlignedValid 12 4 missing34720_34722 records34720_34722 :=
  aligned34720_34721.append aligned34721_34722

def missing34722_34723 : List (BitVec (edgeCount 12)) :=
  [missing34722]
abbrev records34722_34723 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34722]
theorem aligned34722_34723 :
    AlignedValid 12 4 missing34722_34723 records34722_34723 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34722
    maskCheck34722 AlignedValid.nil

def missing34723_34724 : List (BitVec (edgeCount 12)) :=
  [missing34723]
abbrev records34723_34724 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34723]
theorem aligned34723_34724 :
    AlignedValid 12 4 missing34723_34724 records34723_34724 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34723
    maskCheck34723 AlignedValid.nil

def missing34722_34724 : List (BitVec (edgeCount 12)) :=
  missing34722_34723 ++ missing34723_34724
abbrev records34722_34724 : List Blob :=
  records34722_34723 ++ records34723_34724
theorem aligned34722_34724 :
    AlignedValid 12 4 missing34722_34724 records34722_34724 :=
  aligned34722_34723.append aligned34723_34724

def missing34720_34724 : List (BitVec (edgeCount 12)) :=
  missing34720_34722 ++ missing34722_34724
abbrev records34720_34724 : List Blob :=
  records34720_34722 ++ records34722_34724
theorem aligned34720_34724 :
    AlignedValid 12 4 missing34720_34724 records34720_34724 :=
  aligned34720_34722.append aligned34722_34724

def missing34724_34725 : List (BitVec (edgeCount 12)) :=
  [missing34724]
abbrev records34724_34725 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34724]
theorem aligned34724_34725 :
    AlignedValid 12 4 missing34724_34725 records34724_34725 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34724
    maskCheck34724 AlignedValid.nil

def missing34725_34726 : List (BitVec (edgeCount 12)) :=
  [missing34725]
abbrev records34725_34726 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34725]
theorem aligned34725_34726 :
    AlignedValid 12 4 missing34725_34726 records34725_34726 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34725
    maskCheck34725 AlignedValid.nil

def missing34724_34726 : List (BitVec (edgeCount 12)) :=
  missing34724_34725 ++ missing34725_34726
abbrev records34724_34726 : List Blob :=
  records34724_34725 ++ records34725_34726
theorem aligned34724_34726 :
    AlignedValid 12 4 missing34724_34726 records34724_34726 :=
  aligned34724_34725.append aligned34725_34726

def missing34726_34727 : List (BitVec (edgeCount 12)) :=
  [missing34726]
abbrev records34726_34727 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34726]
theorem aligned34726_34727 :
    AlignedValid 12 4 missing34726_34727 records34726_34727 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34726
    maskCheck34726 AlignedValid.nil

def missing34727_34728 : List (BitVec (edgeCount 12)) :=
  [missing34727]
abbrev records34727_34728 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34727]
theorem aligned34727_34728 :
    AlignedValid 12 4 missing34727_34728 records34727_34728 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34727
    maskCheck34727 AlignedValid.nil

def missing34726_34728 : List (BitVec (edgeCount 12)) :=
  missing34726_34727 ++ missing34727_34728
abbrev records34726_34728 : List Blob :=
  records34726_34727 ++ records34727_34728
theorem aligned34726_34728 :
    AlignedValid 12 4 missing34726_34728 records34726_34728 :=
  aligned34726_34727.append aligned34727_34728

def missing34724_34728 : List (BitVec (edgeCount 12)) :=
  missing34724_34726 ++ missing34726_34728
abbrev records34724_34728 : List Blob :=
  records34724_34726 ++ records34726_34728
theorem aligned34724_34728 :
    AlignedValid 12 4 missing34724_34728 records34724_34728 :=
  aligned34724_34726.append aligned34726_34728

def missing34720_34728 : List (BitVec (edgeCount 12)) :=
  missing34720_34724 ++ missing34724_34728
abbrev records34720_34728 : List Blob :=
  records34720_34724 ++ records34724_34728
theorem aligned34720_34728 :
    AlignedValid 12 4 missing34720_34728 records34720_34728 :=
  aligned34720_34724.append aligned34724_34728

def missing34728_34729 : List (BitVec (edgeCount 12)) :=
  [missing34728]
abbrev records34728_34729 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34728]
theorem aligned34728_34729 :
    AlignedValid 12 4 missing34728_34729 records34728_34729 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34728
    maskCheck34728 AlignedValid.nil

def missing34729_34730 : List (BitVec (edgeCount 12)) :=
  [missing34729]
abbrev records34729_34730 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34729]
theorem aligned34729_34730 :
    AlignedValid 12 4 missing34729_34730 records34729_34730 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34729
    maskCheck34729 AlignedValid.nil

def missing34728_34730 : List (BitVec (edgeCount 12)) :=
  missing34728_34729 ++ missing34729_34730
abbrev records34728_34730 : List Blob :=
  records34728_34729 ++ records34729_34730
theorem aligned34728_34730 :
    AlignedValid 12 4 missing34728_34730 records34728_34730 :=
  aligned34728_34729.append aligned34729_34730

def missing34730_34731 : List (BitVec (edgeCount 12)) :=
  [missing34730]
abbrev records34730_34731 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34730]
theorem aligned34730_34731 :
    AlignedValid 12 4 missing34730_34731 records34730_34731 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34730
    maskCheck34730 AlignedValid.nil

def missing34731_34732 : List (BitVec (edgeCount 12)) :=
  [missing34731]
abbrev records34731_34732 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34731]
theorem aligned34731_34732 :
    AlignedValid 12 4 missing34731_34732 records34731_34732 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34731
    maskCheck34731 AlignedValid.nil

def missing34730_34732 : List (BitVec (edgeCount 12)) :=
  missing34730_34731 ++ missing34731_34732
abbrev records34730_34732 : List Blob :=
  records34730_34731 ++ records34731_34732
theorem aligned34730_34732 :
    AlignedValid 12 4 missing34730_34732 records34730_34732 :=
  aligned34730_34731.append aligned34731_34732

def missing34728_34732 : List (BitVec (edgeCount 12)) :=
  missing34728_34730 ++ missing34730_34732
abbrev records34728_34732 : List Blob :=
  records34728_34730 ++ records34730_34732
theorem aligned34728_34732 :
    AlignedValid 12 4 missing34728_34732 records34728_34732 :=
  aligned34728_34730.append aligned34730_34732

def missing34732_34733 : List (BitVec (edgeCount 12)) :=
  [missing34732]
abbrev records34732_34733 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34732]
theorem aligned34732_34733 :
    AlignedValid 12 4 missing34732_34733 records34732_34733 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34732
    maskCheck34732 AlignedValid.nil

def missing34733_34734 : List (BitVec (edgeCount 12)) :=
  [missing34733]
abbrev records34733_34734 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34733]
theorem aligned34733_34734 :
    AlignedValid 12 4 missing34733_34734 records34733_34734 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34733
    maskCheck34733 AlignedValid.nil

def missing34732_34734 : List (BitVec (edgeCount 12)) :=
  missing34732_34733 ++ missing34733_34734
abbrev records34732_34734 : List Blob :=
  records34732_34733 ++ records34733_34734
theorem aligned34732_34734 :
    AlignedValid 12 4 missing34732_34734 records34732_34734 :=
  aligned34732_34733.append aligned34733_34734

def missing34734_34735 : List (BitVec (edgeCount 12)) :=
  [missing34734]
abbrev records34734_34735 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34734]
theorem aligned34734_34735 :
    AlignedValid 12 4 missing34734_34735 records34734_34735 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34734
    maskCheck34734 AlignedValid.nil

def missing34735_34736 : List (BitVec (edgeCount 12)) :=
  [missing34735]
abbrev records34735_34736 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34735]
theorem aligned34735_34736 :
    AlignedValid 12 4 missing34735_34736 records34735_34736 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34735
    maskCheck34735 AlignedValid.nil

def missing34734_34736 : List (BitVec (edgeCount 12)) :=
  missing34734_34735 ++ missing34735_34736
abbrev records34734_34736 : List Blob :=
  records34734_34735 ++ records34735_34736
theorem aligned34734_34736 :
    AlignedValid 12 4 missing34734_34736 records34734_34736 :=
  aligned34734_34735.append aligned34735_34736

def missing34732_34736 : List (BitVec (edgeCount 12)) :=
  missing34732_34734 ++ missing34734_34736
abbrev records34732_34736 : List Blob :=
  records34732_34734 ++ records34734_34736
theorem aligned34732_34736 :
    AlignedValid 12 4 missing34732_34736 records34732_34736 :=
  aligned34732_34734.append aligned34734_34736

def missing34728_34736 : List (BitVec (edgeCount 12)) :=
  missing34728_34732 ++ missing34732_34736
abbrev records34728_34736 : List Blob :=
  records34728_34732 ++ records34732_34736
theorem aligned34728_34736 :
    AlignedValid 12 4 missing34728_34736 records34728_34736 :=
  aligned34728_34732.append aligned34732_34736

def missing34720_34736 : List (BitVec (edgeCount 12)) :=
  missing34720_34728 ++ missing34728_34736
abbrev records34720_34736 : List Blob :=
  records34720_34728 ++ records34728_34736
theorem aligned34720_34736 :
    AlignedValid 12 4 missing34720_34736 records34720_34736 :=
  aligned34720_34728.append aligned34728_34736

def missing34736_34737 : List (BitVec (edgeCount 12)) :=
  [missing34736]
abbrev records34736_34737 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34736]
theorem aligned34736_34737 :
    AlignedValid 12 4 missing34736_34737 records34736_34737 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34736
    maskCheck34736 AlignedValid.nil

def missing34737_34738 : List (BitVec (edgeCount 12)) :=
  [missing34737]
abbrev records34737_34738 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34737]
theorem aligned34737_34738 :
    AlignedValid 12 4 missing34737_34738 records34737_34738 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34737
    maskCheck34737 AlignedValid.nil

def missing34736_34738 : List (BitVec (edgeCount 12)) :=
  missing34736_34737 ++ missing34737_34738
abbrev records34736_34738 : List Blob :=
  records34736_34737 ++ records34737_34738
theorem aligned34736_34738 :
    AlignedValid 12 4 missing34736_34738 records34736_34738 :=
  aligned34736_34737.append aligned34737_34738

def missing34738_34739 : List (BitVec (edgeCount 12)) :=
  [missing34738]
abbrev records34738_34739 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34738]
theorem aligned34738_34739 :
    AlignedValid 12 4 missing34738_34739 records34738_34739 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34738
    maskCheck34738 AlignedValid.nil

def missing34739_34740 : List (BitVec (edgeCount 12)) :=
  [missing34739]
abbrev records34739_34740 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34739]
theorem aligned34739_34740 :
    AlignedValid 12 4 missing34739_34740 records34739_34740 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34739
    maskCheck34739 AlignedValid.nil

def missing34738_34740 : List (BitVec (edgeCount 12)) :=
  missing34738_34739 ++ missing34739_34740
abbrev records34738_34740 : List Blob :=
  records34738_34739 ++ records34739_34740
theorem aligned34738_34740 :
    AlignedValid 12 4 missing34738_34740 records34738_34740 :=
  aligned34738_34739.append aligned34739_34740

def missing34736_34740 : List (BitVec (edgeCount 12)) :=
  missing34736_34738 ++ missing34738_34740
abbrev records34736_34740 : List Blob :=
  records34736_34738 ++ records34738_34740
theorem aligned34736_34740 :
    AlignedValid 12 4 missing34736_34740 records34736_34740 :=
  aligned34736_34738.append aligned34738_34740

def missing34740_34741 : List (BitVec (edgeCount 12)) :=
  [missing34740]
abbrev records34740_34741 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34740]
theorem aligned34740_34741 :
    AlignedValid 12 4 missing34740_34741 records34740_34741 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34740
    maskCheck34740 AlignedValid.nil

def missing34741_34742 : List (BitVec (edgeCount 12)) :=
  [missing34741]
abbrev records34741_34742 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34741]
theorem aligned34741_34742 :
    AlignedValid 12 4 missing34741_34742 records34741_34742 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34741
    maskCheck34741 AlignedValid.nil

def missing34740_34742 : List (BitVec (edgeCount 12)) :=
  missing34740_34741 ++ missing34741_34742
abbrev records34740_34742 : List Blob :=
  records34740_34741 ++ records34741_34742
theorem aligned34740_34742 :
    AlignedValid 12 4 missing34740_34742 records34740_34742 :=
  aligned34740_34741.append aligned34741_34742

def missing34742_34743 : List (BitVec (edgeCount 12)) :=
  [missing34742]
abbrev records34742_34743 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34742]
theorem aligned34742_34743 :
    AlignedValid 12 4 missing34742_34743 records34742_34743 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34742
    maskCheck34742 AlignedValid.nil

def missing34743_34744 : List (BitVec (edgeCount 12)) :=
  [missing34743]
abbrev records34743_34744 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34743]
theorem aligned34743_34744 :
    AlignedValid 12 4 missing34743_34744 records34743_34744 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34743
    maskCheck34743 AlignedValid.nil

def missing34742_34744 : List (BitVec (edgeCount 12)) :=
  missing34742_34743 ++ missing34743_34744
abbrev records34742_34744 : List Blob :=
  records34742_34743 ++ records34743_34744
theorem aligned34742_34744 :
    AlignedValid 12 4 missing34742_34744 records34742_34744 :=
  aligned34742_34743.append aligned34743_34744

def missing34740_34744 : List (BitVec (edgeCount 12)) :=
  missing34740_34742 ++ missing34742_34744
abbrev records34740_34744 : List Blob :=
  records34740_34742 ++ records34742_34744
theorem aligned34740_34744 :
    AlignedValid 12 4 missing34740_34744 records34740_34744 :=
  aligned34740_34742.append aligned34742_34744

def missing34736_34744 : List (BitVec (edgeCount 12)) :=
  missing34736_34740 ++ missing34740_34744
abbrev records34736_34744 : List Blob :=
  records34736_34740 ++ records34740_34744
theorem aligned34736_34744 :
    AlignedValid 12 4 missing34736_34744 records34736_34744 :=
  aligned34736_34740.append aligned34740_34744

def missing34744_34745 : List (BitVec (edgeCount 12)) :=
  [missing34744]
abbrev records34744_34745 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34744]
theorem aligned34744_34745 :
    AlignedValid 12 4 missing34744_34745 records34744_34745 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34744
    maskCheck34744 AlignedValid.nil

def missing34745_34746 : List (BitVec (edgeCount 12)) :=
  [missing34745]
abbrev records34745_34746 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34745]
theorem aligned34745_34746 :
    AlignedValid 12 4 missing34745_34746 records34745_34746 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34745
    maskCheck34745 AlignedValid.nil

def missing34744_34746 : List (BitVec (edgeCount 12)) :=
  missing34744_34745 ++ missing34745_34746
abbrev records34744_34746 : List Blob :=
  records34744_34745 ++ records34745_34746
theorem aligned34744_34746 :
    AlignedValid 12 4 missing34744_34746 records34744_34746 :=
  aligned34744_34745.append aligned34745_34746

def missing34746_34747 : List (BitVec (edgeCount 12)) :=
  [missing34746]
abbrev records34746_34747 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34746]
theorem aligned34746_34747 :
    AlignedValid 12 4 missing34746_34747 records34746_34747 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34746
    maskCheck34746 AlignedValid.nil

def missing34747_34748 : List (BitVec (edgeCount 12)) :=
  [missing34747]
abbrev records34747_34748 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34747]
theorem aligned34747_34748 :
    AlignedValid 12 4 missing34747_34748 records34747_34748 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34747
    maskCheck34747 AlignedValid.nil

def missing34746_34748 : List (BitVec (edgeCount 12)) :=
  missing34746_34747 ++ missing34747_34748
abbrev records34746_34748 : List Blob :=
  records34746_34747 ++ records34747_34748
theorem aligned34746_34748 :
    AlignedValid 12 4 missing34746_34748 records34746_34748 :=
  aligned34746_34747.append aligned34747_34748

def missing34744_34748 : List (BitVec (edgeCount 12)) :=
  missing34744_34746 ++ missing34746_34748
abbrev records34744_34748 : List Blob :=
  records34744_34746 ++ records34746_34748
theorem aligned34744_34748 :
    AlignedValid 12 4 missing34744_34748 records34744_34748 :=
  aligned34744_34746.append aligned34746_34748

def missing34748_34749 : List (BitVec (edgeCount 12)) :=
  [missing34748]
abbrev records34748_34749 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34748]
theorem aligned34748_34749 :
    AlignedValid 12 4 missing34748_34749 records34748_34749 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34748
    maskCheck34748 AlignedValid.nil

def missing34749_34750 : List (BitVec (edgeCount 12)) :=
  [missing34749]
abbrev records34749_34750 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34749]
theorem aligned34749_34750 :
    AlignedValid 12 4 missing34749_34750 records34749_34750 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34749
    maskCheck34749 AlignedValid.nil

def missing34748_34750 : List (BitVec (edgeCount 12)) :=
  missing34748_34749 ++ missing34749_34750
abbrev records34748_34750 : List Blob :=
  records34748_34749 ++ records34749_34750
theorem aligned34748_34750 :
    AlignedValid 12 4 missing34748_34750 records34748_34750 :=
  aligned34748_34749.append aligned34749_34750

def missing34750_34751 : List (BitVec (edgeCount 12)) :=
  [missing34750]
abbrev records34750_34751 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34750]
theorem aligned34750_34751 :
    AlignedValid 12 4 missing34750_34751 records34750_34751 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34750
    maskCheck34750 AlignedValid.nil

def missing34751_34752 : List (BitVec (edgeCount 12)) :=
  [missing34751]
abbrev records34751_34752 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34751]
theorem aligned34751_34752 :
    AlignedValid 12 4 missing34751_34752 records34751_34752 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34751
    maskCheck34751 AlignedValid.nil

def missing34750_34752 : List (BitVec (edgeCount 12)) :=
  missing34750_34751 ++ missing34751_34752
abbrev records34750_34752 : List Blob :=
  records34750_34751 ++ records34751_34752
theorem aligned34750_34752 :
    AlignedValid 12 4 missing34750_34752 records34750_34752 :=
  aligned34750_34751.append aligned34751_34752

def missing34748_34752 : List (BitVec (edgeCount 12)) :=
  missing34748_34750 ++ missing34750_34752
abbrev records34748_34752 : List Blob :=
  records34748_34750 ++ records34750_34752
theorem aligned34748_34752 :
    AlignedValid 12 4 missing34748_34752 records34748_34752 :=
  aligned34748_34750.append aligned34750_34752

def missing34744_34752 : List (BitVec (edgeCount 12)) :=
  missing34744_34748 ++ missing34748_34752
abbrev records34744_34752 : List Blob :=
  records34744_34748 ++ records34748_34752
theorem aligned34744_34752 :
    AlignedValid 12 4 missing34744_34752 records34744_34752 :=
  aligned34744_34748.append aligned34748_34752

def missing34736_34752 : List (BitVec (edgeCount 12)) :=
  missing34736_34744 ++ missing34744_34752
abbrev records34736_34752 : List Blob :=
  records34736_34744 ++ records34744_34752
theorem aligned34736_34752 :
    AlignedValid 12 4 missing34736_34752 records34736_34752 :=
  aligned34736_34744.append aligned34744_34752

def missing34720_34752 : List (BitVec (edgeCount 12)) :=
  missing34720_34736 ++ missing34736_34752
abbrev records34720_34752 : List Blob :=
  records34720_34736 ++ records34736_34752
theorem aligned34720_34752 :
    AlignedValid 12 4 missing34720_34752 records34720_34752 :=
  aligned34720_34736.append aligned34736_34752

def missing34688_34752 : List (BitVec (edgeCount 12)) :=
  missing34688_34720 ++ missing34720_34752
abbrev records34688_34752 : List Blob :=
  records34688_34720 ++ records34720_34752
theorem aligned34688_34752 :
    AlignedValid 12 4 missing34688_34752 records34688_34752 :=
  aligned34688_34720.append aligned34720_34752

def missing34752_34753 : List (BitVec (edgeCount 12)) :=
  [missing34752]
abbrev records34752_34753 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34752]
theorem aligned34752_34753 :
    AlignedValid 12 4 missing34752_34753 records34752_34753 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34752
    maskCheck34752 AlignedValid.nil

def missing34753_34754 : List (BitVec (edgeCount 12)) :=
  [missing34753]
abbrev records34753_34754 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34753]
theorem aligned34753_34754 :
    AlignedValid 12 4 missing34753_34754 records34753_34754 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34753
    maskCheck34753 AlignedValid.nil

def missing34752_34754 : List (BitVec (edgeCount 12)) :=
  missing34752_34753 ++ missing34753_34754
abbrev records34752_34754 : List Blob :=
  records34752_34753 ++ records34753_34754
theorem aligned34752_34754 :
    AlignedValid 12 4 missing34752_34754 records34752_34754 :=
  aligned34752_34753.append aligned34753_34754

def missing34754_34755 : List (BitVec (edgeCount 12)) :=
  [missing34754]
abbrev records34754_34755 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34754]
theorem aligned34754_34755 :
    AlignedValid 12 4 missing34754_34755 records34754_34755 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34754
    maskCheck34754 AlignedValid.nil

def missing34755_34756 : List (BitVec (edgeCount 12)) :=
  [missing34755]
abbrev records34755_34756 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34755]
theorem aligned34755_34756 :
    AlignedValid 12 4 missing34755_34756 records34755_34756 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34755
    maskCheck34755 AlignedValid.nil

def missing34754_34756 : List (BitVec (edgeCount 12)) :=
  missing34754_34755 ++ missing34755_34756
abbrev records34754_34756 : List Blob :=
  records34754_34755 ++ records34755_34756
theorem aligned34754_34756 :
    AlignedValid 12 4 missing34754_34756 records34754_34756 :=
  aligned34754_34755.append aligned34755_34756

def missing34752_34756 : List (BitVec (edgeCount 12)) :=
  missing34752_34754 ++ missing34754_34756
abbrev records34752_34756 : List Blob :=
  records34752_34754 ++ records34754_34756
theorem aligned34752_34756 :
    AlignedValid 12 4 missing34752_34756 records34752_34756 :=
  aligned34752_34754.append aligned34754_34756

def missing34756_34757 : List (BitVec (edgeCount 12)) :=
  [missing34756]
abbrev records34756_34757 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34756]
theorem aligned34756_34757 :
    AlignedValid 12 4 missing34756_34757 records34756_34757 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34756
    maskCheck34756 AlignedValid.nil

def missing34757_34758 : List (BitVec (edgeCount 12)) :=
  [missing34757]
abbrev records34757_34758 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34757]
theorem aligned34757_34758 :
    AlignedValid 12 4 missing34757_34758 records34757_34758 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34757
    maskCheck34757 AlignedValid.nil

def missing34756_34758 : List (BitVec (edgeCount 12)) :=
  missing34756_34757 ++ missing34757_34758
abbrev records34756_34758 : List Blob :=
  records34756_34757 ++ records34757_34758
theorem aligned34756_34758 :
    AlignedValid 12 4 missing34756_34758 records34756_34758 :=
  aligned34756_34757.append aligned34757_34758

def missing34758_34759 : List (BitVec (edgeCount 12)) :=
  [missing34758]
abbrev records34758_34759 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34758]
theorem aligned34758_34759 :
    AlignedValid 12 4 missing34758_34759 records34758_34759 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34758
    maskCheck34758 AlignedValid.nil

def missing34759_34760 : List (BitVec (edgeCount 12)) :=
  [missing34759]
abbrev records34759_34760 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34759]
theorem aligned34759_34760 :
    AlignedValid 12 4 missing34759_34760 records34759_34760 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34759
    maskCheck34759 AlignedValid.nil

def missing34758_34760 : List (BitVec (edgeCount 12)) :=
  missing34758_34759 ++ missing34759_34760
abbrev records34758_34760 : List Blob :=
  records34758_34759 ++ records34759_34760
theorem aligned34758_34760 :
    AlignedValid 12 4 missing34758_34760 records34758_34760 :=
  aligned34758_34759.append aligned34759_34760

def missing34756_34760 : List (BitVec (edgeCount 12)) :=
  missing34756_34758 ++ missing34758_34760
abbrev records34756_34760 : List Blob :=
  records34756_34758 ++ records34758_34760
theorem aligned34756_34760 :
    AlignedValid 12 4 missing34756_34760 records34756_34760 :=
  aligned34756_34758.append aligned34758_34760

def missing34752_34760 : List (BitVec (edgeCount 12)) :=
  missing34752_34756 ++ missing34756_34760
abbrev records34752_34760 : List Blob :=
  records34752_34756 ++ records34756_34760
theorem aligned34752_34760 :
    AlignedValid 12 4 missing34752_34760 records34752_34760 :=
  aligned34752_34756.append aligned34756_34760

def missing34760_34761 : List (BitVec (edgeCount 12)) :=
  [missing34760]
abbrev records34760_34761 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34760]
theorem aligned34760_34761 :
    AlignedValid 12 4 missing34760_34761 records34760_34761 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34760
    maskCheck34760 AlignedValid.nil

def missing34761_34762 : List (BitVec (edgeCount 12)) :=
  [missing34761]
abbrev records34761_34762 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34761]
theorem aligned34761_34762 :
    AlignedValid 12 4 missing34761_34762 records34761_34762 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34761
    maskCheck34761 AlignedValid.nil

def missing34760_34762 : List (BitVec (edgeCount 12)) :=
  missing34760_34761 ++ missing34761_34762
abbrev records34760_34762 : List Blob :=
  records34760_34761 ++ records34761_34762
theorem aligned34760_34762 :
    AlignedValid 12 4 missing34760_34762 records34760_34762 :=
  aligned34760_34761.append aligned34761_34762

def missing34762_34763 : List (BitVec (edgeCount 12)) :=
  [missing34762]
abbrev records34762_34763 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34762]
theorem aligned34762_34763 :
    AlignedValid 12 4 missing34762_34763 records34762_34763 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34762
    maskCheck34762 AlignedValid.nil

def missing34763_34764 : List (BitVec (edgeCount 12)) :=
  [missing34763]
abbrev records34763_34764 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34763]
theorem aligned34763_34764 :
    AlignedValid 12 4 missing34763_34764 records34763_34764 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34763
    maskCheck34763 AlignedValid.nil

def missing34762_34764 : List (BitVec (edgeCount 12)) :=
  missing34762_34763 ++ missing34763_34764
abbrev records34762_34764 : List Blob :=
  records34762_34763 ++ records34763_34764
theorem aligned34762_34764 :
    AlignedValid 12 4 missing34762_34764 records34762_34764 :=
  aligned34762_34763.append aligned34763_34764

def missing34760_34764 : List (BitVec (edgeCount 12)) :=
  missing34760_34762 ++ missing34762_34764
abbrev records34760_34764 : List Blob :=
  records34760_34762 ++ records34762_34764
theorem aligned34760_34764 :
    AlignedValid 12 4 missing34760_34764 records34760_34764 :=
  aligned34760_34762.append aligned34762_34764

def missing34764_34765 : List (BitVec (edgeCount 12)) :=
  [missing34764]
abbrev records34764_34765 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34764]
theorem aligned34764_34765 :
    AlignedValid 12 4 missing34764_34765 records34764_34765 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34764
    maskCheck34764 AlignedValid.nil

def missing34765_34766 : List (BitVec (edgeCount 12)) :=
  [missing34765]
abbrev records34765_34766 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34765]
theorem aligned34765_34766 :
    AlignedValid 12 4 missing34765_34766 records34765_34766 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34765
    maskCheck34765 AlignedValid.nil

def missing34764_34766 : List (BitVec (edgeCount 12)) :=
  missing34764_34765 ++ missing34765_34766
abbrev records34764_34766 : List Blob :=
  records34764_34765 ++ records34765_34766
theorem aligned34764_34766 :
    AlignedValid 12 4 missing34764_34766 records34764_34766 :=
  aligned34764_34765.append aligned34765_34766

def missing34766_34767 : List (BitVec (edgeCount 12)) :=
  [missing34766]
abbrev records34766_34767 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34766]
theorem aligned34766_34767 :
    AlignedValid 12 4 missing34766_34767 records34766_34767 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34766
    maskCheck34766 AlignedValid.nil

def missing34767_34768 : List (BitVec (edgeCount 12)) :=
  [missing34767]
abbrev records34767_34768 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34767]
theorem aligned34767_34768 :
    AlignedValid 12 4 missing34767_34768 records34767_34768 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34767
    maskCheck34767 AlignedValid.nil

def missing34766_34768 : List (BitVec (edgeCount 12)) :=
  missing34766_34767 ++ missing34767_34768
abbrev records34766_34768 : List Blob :=
  records34766_34767 ++ records34767_34768
theorem aligned34766_34768 :
    AlignedValid 12 4 missing34766_34768 records34766_34768 :=
  aligned34766_34767.append aligned34767_34768

def missing34764_34768 : List (BitVec (edgeCount 12)) :=
  missing34764_34766 ++ missing34766_34768
abbrev records34764_34768 : List Blob :=
  records34764_34766 ++ records34766_34768
theorem aligned34764_34768 :
    AlignedValid 12 4 missing34764_34768 records34764_34768 :=
  aligned34764_34766.append aligned34766_34768

def missing34760_34768 : List (BitVec (edgeCount 12)) :=
  missing34760_34764 ++ missing34764_34768
abbrev records34760_34768 : List Blob :=
  records34760_34764 ++ records34764_34768
theorem aligned34760_34768 :
    AlignedValid 12 4 missing34760_34768 records34760_34768 :=
  aligned34760_34764.append aligned34764_34768

def missing34752_34768 : List (BitVec (edgeCount 12)) :=
  missing34752_34760 ++ missing34760_34768
abbrev records34752_34768 : List Blob :=
  records34752_34760 ++ records34760_34768
theorem aligned34752_34768 :
    AlignedValid 12 4 missing34752_34768 records34752_34768 :=
  aligned34752_34760.append aligned34760_34768

def missing34768_34769 : List (BitVec (edgeCount 12)) :=
  [missing34768]
abbrev records34768_34769 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34768]
theorem aligned34768_34769 :
    AlignedValid 12 4 missing34768_34769 records34768_34769 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34768
    maskCheck34768 AlignedValid.nil

def missing34769_34770 : List (BitVec (edgeCount 12)) :=
  [missing34769]
abbrev records34769_34770 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34769]
theorem aligned34769_34770 :
    AlignedValid 12 4 missing34769_34770 records34769_34770 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34769
    maskCheck34769 AlignedValid.nil

def missing34768_34770 : List (BitVec (edgeCount 12)) :=
  missing34768_34769 ++ missing34769_34770
abbrev records34768_34770 : List Blob :=
  records34768_34769 ++ records34769_34770
theorem aligned34768_34770 :
    AlignedValid 12 4 missing34768_34770 records34768_34770 :=
  aligned34768_34769.append aligned34769_34770

def missing34770_34771 : List (BitVec (edgeCount 12)) :=
  [missing34770]
abbrev records34770_34771 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34770]
theorem aligned34770_34771 :
    AlignedValid 12 4 missing34770_34771 records34770_34771 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34770
    maskCheck34770 AlignedValid.nil

def missing34771_34772 : List (BitVec (edgeCount 12)) :=
  [missing34771]
abbrev records34771_34772 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34771]
theorem aligned34771_34772 :
    AlignedValid 12 4 missing34771_34772 records34771_34772 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34771
    maskCheck34771 AlignedValid.nil

def missing34770_34772 : List (BitVec (edgeCount 12)) :=
  missing34770_34771 ++ missing34771_34772
abbrev records34770_34772 : List Blob :=
  records34770_34771 ++ records34771_34772
theorem aligned34770_34772 :
    AlignedValid 12 4 missing34770_34772 records34770_34772 :=
  aligned34770_34771.append aligned34771_34772

def missing34768_34772 : List (BitVec (edgeCount 12)) :=
  missing34768_34770 ++ missing34770_34772
abbrev records34768_34772 : List Blob :=
  records34768_34770 ++ records34770_34772
theorem aligned34768_34772 :
    AlignedValid 12 4 missing34768_34772 records34768_34772 :=
  aligned34768_34770.append aligned34770_34772

def missing34772_34773 : List (BitVec (edgeCount 12)) :=
  [missing34772]
abbrev records34772_34773 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34772]
theorem aligned34772_34773 :
    AlignedValid 12 4 missing34772_34773 records34772_34773 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34772
    maskCheck34772 AlignedValid.nil

def missing34773_34774 : List (BitVec (edgeCount 12)) :=
  [missing34773]
abbrev records34773_34774 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34773]
theorem aligned34773_34774 :
    AlignedValid 12 4 missing34773_34774 records34773_34774 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34773
    maskCheck34773 AlignedValid.nil

def missing34772_34774 : List (BitVec (edgeCount 12)) :=
  missing34772_34773 ++ missing34773_34774
abbrev records34772_34774 : List Blob :=
  records34772_34773 ++ records34773_34774
theorem aligned34772_34774 :
    AlignedValid 12 4 missing34772_34774 records34772_34774 :=
  aligned34772_34773.append aligned34773_34774

def missing34774_34775 : List (BitVec (edgeCount 12)) :=
  [missing34774]
abbrev records34774_34775 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34774]
theorem aligned34774_34775 :
    AlignedValid 12 4 missing34774_34775 records34774_34775 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34774
    maskCheck34774 AlignedValid.nil

def missing34775_34776 : List (BitVec (edgeCount 12)) :=
  [missing34775]
abbrev records34775_34776 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34775]
theorem aligned34775_34776 :
    AlignedValid 12 4 missing34775_34776 records34775_34776 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34775
    maskCheck34775 AlignedValid.nil

def missing34774_34776 : List (BitVec (edgeCount 12)) :=
  missing34774_34775 ++ missing34775_34776
abbrev records34774_34776 : List Blob :=
  records34774_34775 ++ records34775_34776
theorem aligned34774_34776 :
    AlignedValid 12 4 missing34774_34776 records34774_34776 :=
  aligned34774_34775.append aligned34775_34776

def missing34772_34776 : List (BitVec (edgeCount 12)) :=
  missing34772_34774 ++ missing34774_34776
abbrev records34772_34776 : List Blob :=
  records34772_34774 ++ records34774_34776
theorem aligned34772_34776 :
    AlignedValid 12 4 missing34772_34776 records34772_34776 :=
  aligned34772_34774.append aligned34774_34776

def missing34768_34776 : List (BitVec (edgeCount 12)) :=
  missing34768_34772 ++ missing34772_34776
abbrev records34768_34776 : List Blob :=
  records34768_34772 ++ records34772_34776
theorem aligned34768_34776 :
    AlignedValid 12 4 missing34768_34776 records34768_34776 :=
  aligned34768_34772.append aligned34772_34776

def missing34776_34777 : List (BitVec (edgeCount 12)) :=
  [missing34776]
abbrev records34776_34777 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34776]
theorem aligned34776_34777 :
    AlignedValid 12 4 missing34776_34777 records34776_34777 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34776
    maskCheck34776 AlignedValid.nil

def missing34777_34778 : List (BitVec (edgeCount 12)) :=
  [missing34777]
abbrev records34777_34778 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34777]
theorem aligned34777_34778 :
    AlignedValid 12 4 missing34777_34778 records34777_34778 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34777
    maskCheck34777 AlignedValid.nil

def missing34776_34778 : List (BitVec (edgeCount 12)) :=
  missing34776_34777 ++ missing34777_34778
abbrev records34776_34778 : List Blob :=
  records34776_34777 ++ records34777_34778
theorem aligned34776_34778 :
    AlignedValid 12 4 missing34776_34778 records34776_34778 :=
  aligned34776_34777.append aligned34777_34778

def missing34778_34779 : List (BitVec (edgeCount 12)) :=
  [missing34778]
abbrev records34778_34779 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34778]
theorem aligned34778_34779 :
    AlignedValid 12 4 missing34778_34779 records34778_34779 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34778
    maskCheck34778 AlignedValid.nil

def missing34779_34780 : List (BitVec (edgeCount 12)) :=
  [missing34779]
abbrev records34779_34780 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34779]
theorem aligned34779_34780 :
    AlignedValid 12 4 missing34779_34780 records34779_34780 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34779
    maskCheck34779 AlignedValid.nil

def missing34778_34780 : List (BitVec (edgeCount 12)) :=
  missing34778_34779 ++ missing34779_34780
abbrev records34778_34780 : List Blob :=
  records34778_34779 ++ records34779_34780
theorem aligned34778_34780 :
    AlignedValid 12 4 missing34778_34780 records34778_34780 :=
  aligned34778_34779.append aligned34779_34780

def missing34776_34780 : List (BitVec (edgeCount 12)) :=
  missing34776_34778 ++ missing34778_34780
abbrev records34776_34780 : List Blob :=
  records34776_34778 ++ records34778_34780
theorem aligned34776_34780 :
    AlignedValid 12 4 missing34776_34780 records34776_34780 :=
  aligned34776_34778.append aligned34778_34780

def missing34780_34781 : List (BitVec (edgeCount 12)) :=
  [missing34780]
abbrev records34780_34781 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34780]
theorem aligned34780_34781 :
    AlignedValid 12 4 missing34780_34781 records34780_34781 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34780
    maskCheck34780 AlignedValid.nil

def missing34781_34782 : List (BitVec (edgeCount 12)) :=
  [missing34781]
abbrev records34781_34782 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34781]
theorem aligned34781_34782 :
    AlignedValid 12 4 missing34781_34782 records34781_34782 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34781
    maskCheck34781 AlignedValid.nil

def missing34780_34782 : List (BitVec (edgeCount 12)) :=
  missing34780_34781 ++ missing34781_34782
abbrev records34780_34782 : List Blob :=
  records34780_34781 ++ records34781_34782
theorem aligned34780_34782 :
    AlignedValid 12 4 missing34780_34782 records34780_34782 :=
  aligned34780_34781.append aligned34781_34782

def missing34782_34783 : List (BitVec (edgeCount 12)) :=
  [missing34782]
abbrev records34782_34783 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34782]
theorem aligned34782_34783 :
    AlignedValid 12 4 missing34782_34783 records34782_34783 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34782
    maskCheck34782 AlignedValid.nil

def missing34783_34784 : List (BitVec (edgeCount 12)) :=
  [missing34783]
abbrev records34783_34784 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34783]
theorem aligned34783_34784 :
    AlignedValid 12 4 missing34783_34784 records34783_34784 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34783
    maskCheck34783 AlignedValid.nil

def missing34782_34784 : List (BitVec (edgeCount 12)) :=
  missing34782_34783 ++ missing34783_34784
abbrev records34782_34784 : List Blob :=
  records34782_34783 ++ records34783_34784
theorem aligned34782_34784 :
    AlignedValid 12 4 missing34782_34784 records34782_34784 :=
  aligned34782_34783.append aligned34783_34784

def missing34780_34784 : List (BitVec (edgeCount 12)) :=
  missing34780_34782 ++ missing34782_34784
abbrev records34780_34784 : List Blob :=
  records34780_34782 ++ records34782_34784
theorem aligned34780_34784 :
    AlignedValid 12 4 missing34780_34784 records34780_34784 :=
  aligned34780_34782.append aligned34782_34784

def missing34776_34784 : List (BitVec (edgeCount 12)) :=
  missing34776_34780 ++ missing34780_34784
abbrev records34776_34784 : List Blob :=
  records34776_34780 ++ records34780_34784
theorem aligned34776_34784 :
    AlignedValid 12 4 missing34776_34784 records34776_34784 :=
  aligned34776_34780.append aligned34780_34784

def missing34768_34784 : List (BitVec (edgeCount 12)) :=
  missing34768_34776 ++ missing34776_34784
abbrev records34768_34784 : List Blob :=
  records34768_34776 ++ records34776_34784
theorem aligned34768_34784 :
    AlignedValid 12 4 missing34768_34784 records34768_34784 :=
  aligned34768_34776.append aligned34776_34784

def missing34752_34784 : List (BitVec (edgeCount 12)) :=
  missing34752_34768 ++ missing34768_34784
abbrev records34752_34784 : List Blob :=
  records34752_34768 ++ records34768_34784
theorem aligned34752_34784 :
    AlignedValid 12 4 missing34752_34784 records34752_34784 :=
  aligned34752_34768.append aligned34768_34784

def missing34784_34785 : List (BitVec (edgeCount 12)) :=
  [missing34784]
abbrev records34784_34785 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34784]
theorem aligned34784_34785 :
    AlignedValid 12 4 missing34784_34785 records34784_34785 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34784
    maskCheck34784 AlignedValid.nil

def missing34785_34786 : List (BitVec (edgeCount 12)) :=
  [missing34785]
abbrev records34785_34786 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34785]
theorem aligned34785_34786 :
    AlignedValid 12 4 missing34785_34786 records34785_34786 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34785
    maskCheck34785 AlignedValid.nil

def missing34784_34786 : List (BitVec (edgeCount 12)) :=
  missing34784_34785 ++ missing34785_34786
abbrev records34784_34786 : List Blob :=
  records34784_34785 ++ records34785_34786
theorem aligned34784_34786 :
    AlignedValid 12 4 missing34784_34786 records34784_34786 :=
  aligned34784_34785.append aligned34785_34786

def missing34786_34787 : List (BitVec (edgeCount 12)) :=
  [missing34786]
abbrev records34786_34787 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34786]
theorem aligned34786_34787 :
    AlignedValid 12 4 missing34786_34787 records34786_34787 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34786
    maskCheck34786 AlignedValid.nil

def missing34787_34788 : List (BitVec (edgeCount 12)) :=
  [missing34787]
abbrev records34787_34788 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34787]
theorem aligned34787_34788 :
    AlignedValid 12 4 missing34787_34788 records34787_34788 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34787
    maskCheck34787 AlignedValid.nil

def missing34786_34788 : List (BitVec (edgeCount 12)) :=
  missing34786_34787 ++ missing34787_34788
abbrev records34786_34788 : List Blob :=
  records34786_34787 ++ records34787_34788
theorem aligned34786_34788 :
    AlignedValid 12 4 missing34786_34788 records34786_34788 :=
  aligned34786_34787.append aligned34787_34788

def missing34784_34788 : List (BitVec (edgeCount 12)) :=
  missing34784_34786 ++ missing34786_34788
abbrev records34784_34788 : List Blob :=
  records34784_34786 ++ records34786_34788
theorem aligned34784_34788 :
    AlignedValid 12 4 missing34784_34788 records34784_34788 :=
  aligned34784_34786.append aligned34786_34788

def missing34788_34789 : List (BitVec (edgeCount 12)) :=
  [missing34788]
abbrev records34788_34789 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34788]
theorem aligned34788_34789 :
    AlignedValid 12 4 missing34788_34789 records34788_34789 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34788
    maskCheck34788 AlignedValid.nil

def missing34789_34790 : List (BitVec (edgeCount 12)) :=
  [missing34789]
abbrev records34789_34790 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34789]
theorem aligned34789_34790 :
    AlignedValid 12 4 missing34789_34790 records34789_34790 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34789
    maskCheck34789 AlignedValid.nil

def missing34788_34790 : List (BitVec (edgeCount 12)) :=
  missing34788_34789 ++ missing34789_34790
abbrev records34788_34790 : List Blob :=
  records34788_34789 ++ records34789_34790
theorem aligned34788_34790 :
    AlignedValid 12 4 missing34788_34790 records34788_34790 :=
  aligned34788_34789.append aligned34789_34790

def missing34790_34791 : List (BitVec (edgeCount 12)) :=
  [missing34790]
abbrev records34790_34791 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34790]
theorem aligned34790_34791 :
    AlignedValid 12 4 missing34790_34791 records34790_34791 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34790
    maskCheck34790 AlignedValid.nil

def missing34791_34792 : List (BitVec (edgeCount 12)) :=
  [missing34791]
abbrev records34791_34792 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34791]
theorem aligned34791_34792 :
    AlignedValid 12 4 missing34791_34792 records34791_34792 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34791
    maskCheck34791 AlignedValid.nil

def missing34790_34792 : List (BitVec (edgeCount 12)) :=
  missing34790_34791 ++ missing34791_34792
abbrev records34790_34792 : List Blob :=
  records34790_34791 ++ records34791_34792
theorem aligned34790_34792 :
    AlignedValid 12 4 missing34790_34792 records34790_34792 :=
  aligned34790_34791.append aligned34791_34792

def missing34788_34792 : List (BitVec (edgeCount 12)) :=
  missing34788_34790 ++ missing34790_34792
abbrev records34788_34792 : List Blob :=
  records34788_34790 ++ records34790_34792
theorem aligned34788_34792 :
    AlignedValid 12 4 missing34788_34792 records34788_34792 :=
  aligned34788_34790.append aligned34790_34792

def missing34784_34792 : List (BitVec (edgeCount 12)) :=
  missing34784_34788 ++ missing34788_34792
abbrev records34784_34792 : List Blob :=
  records34784_34788 ++ records34788_34792
theorem aligned34784_34792 :
    AlignedValid 12 4 missing34784_34792 records34784_34792 :=
  aligned34784_34788.append aligned34788_34792

def missing34792_34793 : List (BitVec (edgeCount 12)) :=
  [missing34792]
abbrev records34792_34793 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34792]
theorem aligned34792_34793 :
    AlignedValid 12 4 missing34792_34793 records34792_34793 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34792
    maskCheck34792 AlignedValid.nil

def missing34793_34794 : List (BitVec (edgeCount 12)) :=
  [missing34793]
abbrev records34793_34794 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34793]
theorem aligned34793_34794 :
    AlignedValid 12 4 missing34793_34794 records34793_34794 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34793
    maskCheck34793 AlignedValid.nil

def missing34792_34794 : List (BitVec (edgeCount 12)) :=
  missing34792_34793 ++ missing34793_34794
abbrev records34792_34794 : List Blob :=
  records34792_34793 ++ records34793_34794
theorem aligned34792_34794 :
    AlignedValid 12 4 missing34792_34794 records34792_34794 :=
  aligned34792_34793.append aligned34793_34794

def missing34794_34795 : List (BitVec (edgeCount 12)) :=
  [missing34794]
abbrev records34794_34795 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34794]
theorem aligned34794_34795 :
    AlignedValid 12 4 missing34794_34795 records34794_34795 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34794
    maskCheck34794 AlignedValid.nil

def missing34795_34796 : List (BitVec (edgeCount 12)) :=
  [missing34795]
abbrev records34795_34796 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34795]
theorem aligned34795_34796 :
    AlignedValid 12 4 missing34795_34796 records34795_34796 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34795
    maskCheck34795 AlignedValid.nil

def missing34794_34796 : List (BitVec (edgeCount 12)) :=
  missing34794_34795 ++ missing34795_34796
abbrev records34794_34796 : List Blob :=
  records34794_34795 ++ records34795_34796
theorem aligned34794_34796 :
    AlignedValid 12 4 missing34794_34796 records34794_34796 :=
  aligned34794_34795.append aligned34795_34796

def missing34792_34796 : List (BitVec (edgeCount 12)) :=
  missing34792_34794 ++ missing34794_34796
abbrev records34792_34796 : List Blob :=
  records34792_34794 ++ records34794_34796
theorem aligned34792_34796 :
    AlignedValid 12 4 missing34792_34796 records34792_34796 :=
  aligned34792_34794.append aligned34794_34796

def missing34796_34797 : List (BitVec (edgeCount 12)) :=
  [missing34796]
abbrev records34796_34797 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34796]
theorem aligned34796_34797 :
    AlignedValid 12 4 missing34796_34797 records34796_34797 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34796
    maskCheck34796 AlignedValid.nil

def missing34797_34798 : List (BitVec (edgeCount 12)) :=
  [missing34797]
abbrev records34797_34798 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34797]
theorem aligned34797_34798 :
    AlignedValid 12 4 missing34797_34798 records34797_34798 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34797
    maskCheck34797 AlignedValid.nil

def missing34796_34798 : List (BitVec (edgeCount 12)) :=
  missing34796_34797 ++ missing34797_34798
abbrev records34796_34798 : List Blob :=
  records34796_34797 ++ records34797_34798
theorem aligned34796_34798 :
    AlignedValid 12 4 missing34796_34798 records34796_34798 :=
  aligned34796_34797.append aligned34797_34798

def missing34798_34799 : List (BitVec (edgeCount 12)) :=
  [missing34798]
abbrev records34798_34799 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34798]
theorem aligned34798_34799 :
    AlignedValid 12 4 missing34798_34799 records34798_34799 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34798
    maskCheck34798 AlignedValid.nil

def missing34799_34800 : List (BitVec (edgeCount 12)) :=
  [missing34799]
abbrev records34799_34800 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34799]
theorem aligned34799_34800 :
    AlignedValid 12 4 missing34799_34800 records34799_34800 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34799
    maskCheck34799 AlignedValid.nil

def missing34798_34800 : List (BitVec (edgeCount 12)) :=
  missing34798_34799 ++ missing34799_34800
abbrev records34798_34800 : List Blob :=
  records34798_34799 ++ records34799_34800
theorem aligned34798_34800 :
    AlignedValid 12 4 missing34798_34800 records34798_34800 :=
  aligned34798_34799.append aligned34799_34800

def missing34796_34800 : List (BitVec (edgeCount 12)) :=
  missing34796_34798 ++ missing34798_34800
abbrev records34796_34800 : List Blob :=
  records34796_34798 ++ records34798_34800
theorem aligned34796_34800 :
    AlignedValid 12 4 missing34796_34800 records34796_34800 :=
  aligned34796_34798.append aligned34798_34800

def missing34792_34800 : List (BitVec (edgeCount 12)) :=
  missing34792_34796 ++ missing34796_34800
abbrev records34792_34800 : List Blob :=
  records34792_34796 ++ records34796_34800
theorem aligned34792_34800 :
    AlignedValid 12 4 missing34792_34800 records34792_34800 :=
  aligned34792_34796.append aligned34796_34800

def missing34784_34800 : List (BitVec (edgeCount 12)) :=
  missing34784_34792 ++ missing34792_34800
abbrev records34784_34800 : List Blob :=
  records34784_34792 ++ records34792_34800
theorem aligned34784_34800 :
    AlignedValid 12 4 missing34784_34800 records34784_34800 :=
  aligned34784_34792.append aligned34792_34800

def missing34800_34801 : List (BitVec (edgeCount 12)) :=
  [missing34800]
abbrev records34800_34801 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34800]
theorem aligned34800_34801 :
    AlignedValid 12 4 missing34800_34801 records34800_34801 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34800
    maskCheck34800 AlignedValid.nil

def missing34801_34802 : List (BitVec (edgeCount 12)) :=
  [missing34801]
abbrev records34801_34802 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34801]
theorem aligned34801_34802 :
    AlignedValid 12 4 missing34801_34802 records34801_34802 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34801
    maskCheck34801 AlignedValid.nil

def missing34800_34802 : List (BitVec (edgeCount 12)) :=
  missing34800_34801 ++ missing34801_34802
abbrev records34800_34802 : List Blob :=
  records34800_34801 ++ records34801_34802
theorem aligned34800_34802 :
    AlignedValid 12 4 missing34800_34802 records34800_34802 :=
  aligned34800_34801.append aligned34801_34802

def missing34802_34803 : List (BitVec (edgeCount 12)) :=
  [missing34802]
abbrev records34802_34803 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34802]
theorem aligned34802_34803 :
    AlignedValid 12 4 missing34802_34803 records34802_34803 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34802
    maskCheck34802 AlignedValid.nil

def missing34803_34804 : List (BitVec (edgeCount 12)) :=
  [missing34803]
abbrev records34803_34804 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34803]
theorem aligned34803_34804 :
    AlignedValid 12 4 missing34803_34804 records34803_34804 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34803
    maskCheck34803 AlignedValid.nil

def missing34802_34804 : List (BitVec (edgeCount 12)) :=
  missing34802_34803 ++ missing34803_34804
abbrev records34802_34804 : List Blob :=
  records34802_34803 ++ records34803_34804
theorem aligned34802_34804 :
    AlignedValid 12 4 missing34802_34804 records34802_34804 :=
  aligned34802_34803.append aligned34803_34804

def missing34800_34804 : List (BitVec (edgeCount 12)) :=
  missing34800_34802 ++ missing34802_34804
abbrev records34800_34804 : List Blob :=
  records34800_34802 ++ records34802_34804
theorem aligned34800_34804 :
    AlignedValid 12 4 missing34800_34804 records34800_34804 :=
  aligned34800_34802.append aligned34802_34804

def missing34804_34805 : List (BitVec (edgeCount 12)) :=
  [missing34804]
abbrev records34804_34805 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34804]
theorem aligned34804_34805 :
    AlignedValid 12 4 missing34804_34805 records34804_34805 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34804
    maskCheck34804 AlignedValid.nil

def missing34805_34806 : List (BitVec (edgeCount 12)) :=
  [missing34805]
abbrev records34805_34806 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34805]
theorem aligned34805_34806 :
    AlignedValid 12 4 missing34805_34806 records34805_34806 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34805
    maskCheck34805 AlignedValid.nil

def missing34804_34806 : List (BitVec (edgeCount 12)) :=
  missing34804_34805 ++ missing34805_34806
abbrev records34804_34806 : List Blob :=
  records34804_34805 ++ records34805_34806
theorem aligned34804_34806 :
    AlignedValid 12 4 missing34804_34806 records34804_34806 :=
  aligned34804_34805.append aligned34805_34806

def missing34806_34807 : List (BitVec (edgeCount 12)) :=
  [missing34806]
abbrev records34806_34807 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34806]
theorem aligned34806_34807 :
    AlignedValid 12 4 missing34806_34807 records34806_34807 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34806
    maskCheck34806 AlignedValid.nil

def missing34807_34808 : List (BitVec (edgeCount 12)) :=
  [missing34807]
abbrev records34807_34808 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34807]
theorem aligned34807_34808 :
    AlignedValid 12 4 missing34807_34808 records34807_34808 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34807
    maskCheck34807 AlignedValid.nil

def missing34806_34808 : List (BitVec (edgeCount 12)) :=
  missing34806_34807 ++ missing34807_34808
abbrev records34806_34808 : List Blob :=
  records34806_34807 ++ records34807_34808
theorem aligned34806_34808 :
    AlignedValid 12 4 missing34806_34808 records34806_34808 :=
  aligned34806_34807.append aligned34807_34808

def missing34804_34808 : List (BitVec (edgeCount 12)) :=
  missing34804_34806 ++ missing34806_34808
abbrev records34804_34808 : List Blob :=
  records34804_34806 ++ records34806_34808
theorem aligned34804_34808 :
    AlignedValid 12 4 missing34804_34808 records34804_34808 :=
  aligned34804_34806.append aligned34806_34808

def missing34800_34808 : List (BitVec (edgeCount 12)) :=
  missing34800_34804 ++ missing34804_34808
abbrev records34800_34808 : List Blob :=
  records34800_34804 ++ records34804_34808
theorem aligned34800_34808 :
    AlignedValid 12 4 missing34800_34808 records34800_34808 :=
  aligned34800_34804.append aligned34804_34808

def missing34808_34809 : List (BitVec (edgeCount 12)) :=
  [missing34808]
abbrev records34808_34809 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34808]
theorem aligned34808_34809 :
    AlignedValid 12 4 missing34808_34809 records34808_34809 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34808
    maskCheck34808 AlignedValid.nil

def missing34809_34810 : List (BitVec (edgeCount 12)) :=
  [missing34809]
abbrev records34809_34810 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34809]
theorem aligned34809_34810 :
    AlignedValid 12 4 missing34809_34810 records34809_34810 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34809
    maskCheck34809 AlignedValid.nil

def missing34808_34810 : List (BitVec (edgeCount 12)) :=
  missing34808_34809 ++ missing34809_34810
abbrev records34808_34810 : List Blob :=
  records34808_34809 ++ records34809_34810
theorem aligned34808_34810 :
    AlignedValid 12 4 missing34808_34810 records34808_34810 :=
  aligned34808_34809.append aligned34809_34810

def missing34810_34811 : List (BitVec (edgeCount 12)) :=
  [missing34810]
abbrev records34810_34811 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34810]
theorem aligned34810_34811 :
    AlignedValid 12 4 missing34810_34811 records34810_34811 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34810
    maskCheck34810 AlignedValid.nil

def missing34811_34812 : List (BitVec (edgeCount 12)) :=
  [missing34811]
abbrev records34811_34812 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34811]
theorem aligned34811_34812 :
    AlignedValid 12 4 missing34811_34812 records34811_34812 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34811
    maskCheck34811 AlignedValid.nil

def missing34810_34812 : List (BitVec (edgeCount 12)) :=
  missing34810_34811 ++ missing34811_34812
abbrev records34810_34812 : List Blob :=
  records34810_34811 ++ records34811_34812
theorem aligned34810_34812 :
    AlignedValid 12 4 missing34810_34812 records34810_34812 :=
  aligned34810_34811.append aligned34811_34812

def missing34808_34812 : List (BitVec (edgeCount 12)) :=
  missing34808_34810 ++ missing34810_34812
abbrev records34808_34812 : List Blob :=
  records34808_34810 ++ records34810_34812
theorem aligned34808_34812 :
    AlignedValid 12 4 missing34808_34812 records34808_34812 :=
  aligned34808_34810.append aligned34810_34812

def missing34812_34813 : List (BitVec (edgeCount 12)) :=
  [missing34812]
abbrev records34812_34813 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34812]
theorem aligned34812_34813 :
    AlignedValid 12 4 missing34812_34813 records34812_34813 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34812
    maskCheck34812 AlignedValid.nil

def missing34813_34814 : List (BitVec (edgeCount 12)) :=
  [missing34813]
abbrev records34813_34814 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34813]
theorem aligned34813_34814 :
    AlignedValid 12 4 missing34813_34814 records34813_34814 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34813
    maskCheck34813 AlignedValid.nil

def missing34812_34814 : List (BitVec (edgeCount 12)) :=
  missing34812_34813 ++ missing34813_34814
abbrev records34812_34814 : List Blob :=
  records34812_34813 ++ records34813_34814
theorem aligned34812_34814 :
    AlignedValid 12 4 missing34812_34814 records34812_34814 :=
  aligned34812_34813.append aligned34813_34814

def missing34814_34815 : List (BitVec (edgeCount 12)) :=
  [missing34814]
abbrev records34814_34815 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34814]
theorem aligned34814_34815 :
    AlignedValid 12 4 missing34814_34815 records34814_34815 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34814
    maskCheck34814 AlignedValid.nil

def missing34815_34816 : List (BitVec (edgeCount 12)) :=
  [missing34815]
abbrev records34815_34816 : List Blob :=
  [StrongPackedBucketN12A4Shard271.record34815]
theorem aligned34815_34816 :
    AlignedValid 12 4 missing34815_34816 records34815_34816 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard271.check34815
    maskCheck34815 AlignedValid.nil

def missing34814_34816 : List (BitVec (edgeCount 12)) :=
  missing34814_34815 ++ missing34815_34816
abbrev records34814_34816 : List Blob :=
  records34814_34815 ++ records34815_34816
theorem aligned34814_34816 :
    AlignedValid 12 4 missing34814_34816 records34814_34816 :=
  aligned34814_34815.append aligned34815_34816

def missing34812_34816 : List (BitVec (edgeCount 12)) :=
  missing34812_34814 ++ missing34814_34816
abbrev records34812_34816 : List Blob :=
  records34812_34814 ++ records34814_34816
theorem aligned34812_34816 :
    AlignedValid 12 4 missing34812_34816 records34812_34816 :=
  aligned34812_34814.append aligned34814_34816

def missing34808_34816 : List (BitVec (edgeCount 12)) :=
  missing34808_34812 ++ missing34812_34816
abbrev records34808_34816 : List Blob :=
  records34808_34812 ++ records34812_34816
theorem aligned34808_34816 :
    AlignedValid 12 4 missing34808_34816 records34808_34816 :=
  aligned34808_34812.append aligned34812_34816

def missing34800_34816 : List (BitVec (edgeCount 12)) :=
  missing34800_34808 ++ missing34808_34816
abbrev records34800_34816 : List Blob :=
  records34800_34808 ++ records34808_34816
theorem aligned34800_34816 :
    AlignedValid 12 4 missing34800_34816 records34800_34816 :=
  aligned34800_34808.append aligned34808_34816

def missing34784_34816 : List (BitVec (edgeCount 12)) :=
  missing34784_34800 ++ missing34800_34816
abbrev records34784_34816 : List Blob :=
  records34784_34800 ++ records34800_34816
theorem aligned34784_34816 :
    AlignedValid 12 4 missing34784_34816 records34784_34816 :=
  aligned34784_34800.append aligned34800_34816

def missing34752_34816 : List (BitVec (edgeCount 12)) :=
  missing34752_34784 ++ missing34784_34816
abbrev records34752_34816 : List Blob :=
  records34752_34784 ++ records34784_34816
theorem aligned34752_34816 :
    AlignedValid 12 4 missing34752_34816 records34752_34816 :=
  aligned34752_34784.append aligned34784_34816

def missing34688_34816 : List (BitVec (edgeCount 12)) :=
  missing34688_34752 ++ missing34752_34816
abbrev records34688_34816 : List Blob :=
  records34688_34752 ++ records34752_34816
theorem aligned34688_34816 :
    AlignedValid 12 4 missing34688_34816 records34688_34816 :=
  aligned34688_34752.append aligned34752_34816

abbrev missing : List (BitVec (edgeCount 12)) := missing34688_34816
abbrev records : List Blob := records34688_34816
theorem aligned : AlignedValid 12 4 missing records := aligned34688_34816

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard271
