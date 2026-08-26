/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard240

/-! Decode-only alignment checks for n=12, a=4, records 30720--30847. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard240

open PackedBucketCertificate

def missing30720 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12898978386692571136
theorem maskCheck30720 :
    checkMaskFor missing30720 StrongPackedBucketN12A4Shard240.record30720 = true := by
  decide

def missing30721 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13115151168806354944
theorem maskCheck30721 :
    checkMaskFor missing30721 StrongPackedBucketN12A4Shard240.record30721 = true := by
  decide

def missing30722 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13403381544958066688
theorem maskCheck30722 :
    checkMaskFor missing30722 StrongPackedBucketN12A4Shard240.record30722 = true := by
  decide

def missing30723 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16321714103494148096
theorem maskCheck30723 :
    checkMaskFor missing30723 StrongPackedBucketN12A4Shard240.record30723 = true := by
  decide

def missing30724 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16573915682626895872
theorem maskCheck30724 :
    checkMaskFor missing30724 StrongPackedBucketN12A4Shard240.record30724 = true := by
  decide

def missing30725 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16862146058778607616
theorem maskCheck30725 :
    checkMaskFor missing30725 StrongPackedBucketN12A4Shard240.record30725 = true := by
  decide

def missing30726 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17438606811082031104
theorem maskCheck30726 :
    checkMaskFor missing30726 StrongPackedBucketN12A4Shard240.record30726 = true := by
  decide

def missing30727 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28139159525714329600
theorem maskCheck30727 :
    checkMaskFor missing30727 StrongPackedBucketN12A4Shard240.record30727 = true := by
  decide

def missing30728 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28679591480998789120
theorem maskCheck30728 :
    checkMaskFor missing30728 StrongPackedBucketN12A4Shard240.record30728 = true := by
  decide

def missing30729 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29256052233302212608
theorem maskCheck30729 :
    checkMaskFor missing30729 StrongPackedBucketN12A4Shard240.record30729 = true := by
  decide

def missing30730 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30408973737909059584
theorem maskCheck30730 :
    checkMaskFor missing30730 StrongPackedBucketN12A4Shard240.record30730 = true := by
  decide

def missing30731 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37434589156607033344
theorem maskCheck30731 :
    checkMaskFor missing30731 StrongPackedBucketN12A4Shard240.record30731 = true := by
  decide

def missing30732 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37722819532758745088
theorem maskCheck30732 :
    checkMaskFor missing30732 StrongPackedBucketN12A4Shard240.record30732 = true := by
  decide

def missing30733 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37938992314872528896
theorem maskCheck30733 :
    checkMaskFor missing30733 StrongPackedBucketN12A4Shard240.record30733 = true := by
  decide

def missing30734 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38299280285062168576
theorem maskCheck30734 :
    checkMaskFor missing30734 StrongPackedBucketN12A4Shard240.record30734 = true := by
  decide

def missing30735 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38515453067175952384
theorem maskCheck30735 :
    checkMaskFor missing30735 StrongPackedBucketN12A4Shard240.record30735 = true := by
  decide

def missing30736 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38731625849289736192
theorem maskCheck30736 :
    checkMaskFor missing30736 StrongPackedBucketN12A4Shard240.record30736 = true := by
  decide

def missing30737 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38803683443327664128
theorem maskCheck30737 :
    checkMaskFor missing30737 StrongPackedBucketN12A4Shard240.record30737 = true := by
  decide

def missing30738 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39055885022460411904
theorem maskCheck30738 :
    checkMaskFor missing30738 StrongPackedBucketN12A4Shard240.record30738 = true := by
  decide

def missing30739 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39452201789669015552
theorem maskCheck30739 :
    checkMaskFor missing30739 StrongPackedBucketN12A4Shard240.record30739 = true := by
  decide

def missing30740 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39668374571782799360
theorem maskCheck30740 :
    checkMaskFor missing30740 StrongPackedBucketN12A4Shard240.record30740 = true := by
  decide

def missing30741 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39704403368801763328
theorem maskCheck30741 :
    checkMaskFor missing30741 StrongPackedBucketN12A4Shard240.record30741 = true := by
  decide

def missing30742 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39884547353896583168
theorem maskCheck30742 :
    checkMaskFor missing30742 StrongPackedBucketN12A4Shard240.record30742 = true := by
  decide

def missing30743 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39956604947934511104
theorem maskCheck30743 :
    checkMaskFor missing30743 StrongPackedBucketN12A4Shard240.record30743 = true := by
  decide

def missing30744 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39992633744953475072
theorem maskCheck30744 :
    checkMaskFor missing30744 StrongPackedBucketN12A4Shard240.record30744 = true := by
  decide

def missing30745 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40208806527067258880
theorem maskCheck30745 :
    checkMaskFor missing30745 StrongPackedBucketN12A4Shard240.record30745 = true := by
  decide

def missing30746 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40461008106200006656
theorem maskCheck30746 :
    checkMaskFor missing30746 StrongPackedBucketN12A4Shard240.record30746 = true := by
  decide

def missing30747 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40533065700237934592
theorem maskCheck30747 :
    checkMaskFor missing30747 StrongPackedBucketN12A4Shard240.record30747 = true := by
  decide

def missing30748 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40569094497256898560
theorem maskCheck30748 :
    checkMaskFor missing30748 StrongPackedBucketN12A4Shard240.record30748 = true := by
  decide

def missing30749 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40785267279370682368
theorem maskCheck30749 :
    checkMaskFor missing30749 StrongPackedBucketN12A4Shard240.record30749 = true := by
  decide

def missing30750 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40965411264465502208
theorem maskCheck30750 :
    checkMaskFor missing30750 StrongPackedBucketN12A4Shard240.record30750 = true := by
  decide

def missing30751 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41001440061484466176
theorem maskCheck30751 :
    checkMaskFor missing30751 StrongPackedBucketN12A4Shard240.record30751 = true := by
  decide

def missing30752 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41073497655522394112
theorem maskCheck30752 :
    checkMaskFor missing30752 StrongPackedBucketN12A4Shard240.record30752 = true := by
  decide

def missing30753 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43919772620020547584
theorem maskCheck30753 :
    checkMaskFor missing30753 StrongPackedBucketN12A4Shard240.record30753 = true := by
  decide

def missing30754 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43991830214058475520
theorem maskCheck30754 :
    checkMaskFor missing30754 StrongPackedBucketN12A4Shard240.record30754 = true := by
  decide

def missing30755 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 44244031793191223296
theorem maskCheck30755 :
    checkMaskFor missing30755 StrongPackedBucketN12A4Shard240.record30755 = true := by
  decide

def missing30756 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 44424175778286043136
theorem maskCheck30756 :
    checkMaskFor missing30756 StrongPackedBucketN12A4Shard240.record30756 = true := by
  decide

def missing30757 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 44532262169342935040
theorem maskCheck30757 :
    checkMaskFor missing30757 StrongPackedBucketN12A4Shard240.record30757 = true := by
  decide

def missing30758 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45000636530589466624
theorem maskCheck30758 :
    checkMaskFor missing30758 StrongPackedBucketN12A4Shard240.record30758 = true := by
  decide

def missing30759 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45108722921646358528
theorem maskCheck30759 :
    checkMaskFor missing30759 StrongPackedBucketN12A4Shard240.record30759 = true := by
  decide

def missing30760 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45541068485873926144
theorem maskCheck30760 :
    checkMaskFor missing30760 StrongPackedBucketN12A4Shard240.record30760 = true := by
  decide

def missing30761 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46369730817310097408
theorem maskCheck30761 :
    checkMaskFor missing30761 StrongPackedBucketN12A4Shard240.record30761 = true := by
  decide

def missing30762 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46585903599423881216
theorem maskCheck30762 :
    checkMaskFor missing30762 StrongPackedBucketN12A4Shard240.record30762 = true := by
  decide

def missing30763 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46874133975575592960
theorem maskCheck30763 :
    checkMaskFor missing30763 StrongPackedBucketN12A4Shard240.record30763 = true := by
  decide

def missing30764 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47126335554708340736
theorem maskCheck30764 :
    checkMaskFor missing30764 StrongPackedBucketN12A4Shard240.record30764 = true := by
  decide

def missing30765 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47450594727879016448
theorem maskCheck30765 :
    checkMaskFor missing30765 StrongPackedBucketN12A4Shard240.record30765 = true := by
  decide

def missing30766 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47702796307011764224
theorem maskCheck30766 :
    checkMaskFor missing30766 StrongPackedBucketN12A4Shard240.record30766 = true := by
  decide

def missing30767 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47991026683163475968
theorem maskCheck30767 :
    checkMaskFor missing30767 StrongPackedBucketN12A4Shard240.record30767 = true := by
  decide

def missing30768 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48603516232485863424
theorem maskCheck30768 :
    checkMaskFor missing30768 StrongPackedBucketN12A4Shard240.record30768 = true := by
  decide

def missing30769 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48639545029504827392
theorem maskCheck30769 :
    checkMaskFor missing30769 StrongPackedBucketN12A4Shard240.record30769 = true := by
  decide

def missing30770 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48855717811618611200
theorem maskCheck30770 :
    checkMaskFor missing30770 StrongPackedBucketN12A4Shard240.record30770 = true := by
  decide

def missing30771 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49143948187770322944
theorem maskCheck30771 :
    checkMaskFor missing30771 StrongPackedBucketN12A4Shard240.record30771 = true := by
  decide

def missing30772 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49720408940073746432
theorem maskCheck30772 :
    checkMaskFor missing30772 StrongPackedBucketN12A4Shard240.record30772 = true := by
  decide

def missing30773 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 53179173453894287360
theorem maskCheck30773 :
    checkMaskFor missing30773 StrongPackedBucketN12A4Shard240.record30773 = true := by
  decide

def missing30774 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64996618876114468864
theorem maskCheck30774 :
    checkMaskFor missing30774 StrongPackedBucketN12A4Shard240.record30774 = true := by
  decide

def missing30775 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1118617292654018560
theorem maskCheck30775 :
    checkMaskFor missing30775 StrongPackedBucketN12A4Shard240.record30775 = true := by
  decide

def missing30776 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1983308421109153792
theorem maskCheck30776 :
    checkMaskFor missing30776 StrongPackedBucketN12A4Shard240.record30776 = true := by
  decide

def missing30777 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2235510000241901568
theorem maskCheck30777 :
    checkMaskFor missing30777 StrongPackedBucketN12A4Shard240.record30777 = true := by
  decide

def missing30778 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2847999549564289024
theorem maskCheck30778 :
    checkMaskFor missing30778 StrongPackedBucketN12A4Shard240.record30778 = true := by
  decide

def missing30779 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3136229925716000768
theorem maskCheck30779 :
    checkMaskFor missing30779 StrongPackedBucketN12A4Shard240.record30779 = true := by
  decide

def missing30780 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3388431504848748544
theorem maskCheck30780 :
    checkMaskFor missing30780 StrongPackedBucketN12A4Shard240.record30780 = true := by
  decide

def missing30781 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4145036242246991872
theorem maskCheck30781 :
    checkMaskFor missing30781 StrongPackedBucketN12A4Shard240.record30781 = true := by
  decide

def missing30782 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4253122633303883776
theorem maskCheck30782 :
    checkMaskFor missing30782 StrongPackedBucketN12A4Shard240.record30782 = true := by
  decide

def missing30783 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5153842558777982976
theorem maskCheck30783 :
    checkMaskFor missing30783 StrongPackedBucketN12A4Shard240.record30783 = true := by
  decide

def missing30784 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5442072934929694720
theorem maskCheck30784 :
    checkMaskFor missing30784 StrongPackedBucketN12A4Shard240.record30784 = true := by
  decide

def missing30785 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5694274514062442496
theorem maskCheck30785 :
    checkMaskFor missing30785 StrongPackedBucketN12A4Shard240.record30785 = true := by
  decide

def missing30786 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6450879251460685824
theorem maskCheck30786 :
    checkMaskFor missing30786 StrongPackedBucketN12A4Shard240.record30786 = true := by
  decide

def missing30787 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6558965642517577728
theorem maskCheck30787 :
    checkMaskFor missing30787 StrongPackedBucketN12A4Shard240.record30787 = true := by
  decide

def missing30788 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7171455191839965184
theorem maskCheck30788 :
    checkMaskFor missing30788 StrongPackedBucketN12A4Shard240.record30788 = true := by
  decide

def missing30789 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7423656770972712960
theorem maskCheck30789 :
    checkMaskFor missing30789 StrongPackedBucketN12A4Shard240.record30789 = true := by
  decide

def missing30790 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7603800756067532800
theorem maskCheck30790 :
    checkMaskFor missing30790 StrongPackedBucketN12A4Shard240.record30790 = true := by
  decide

def missing30791 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7711887147124424704
theorem maskCheck30791 :
    checkMaskFor missing30791 StrongPackedBucketN12A4Shard240.record30791 = true := by
  decide

def missing30792 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8720693463655415808
theorem maskCheck30792 :
    checkMaskFor missing30792 StrongPackedBucketN12A4Shard240.record30792 = true := by
  decide

def missing30793 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14088984219481047040
theorem maskCheck30793 :
    checkMaskFor missing30793 StrongPackedBucketN12A4Shard240.record30793 = true := by
  decide

def missing30794 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14341185798613794816
theorem maskCheck30794 :
    checkMaskFor missing30794 StrongPackedBucketN12A4Shard240.record30794 = true := by
  decide

def missing30795 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14629416174765506560
theorem maskCheck30795 :
    checkMaskFor missing30795 StrongPackedBucketN12A4Shard240.record30795 = true := by
  decide

def missing30796 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16358798431675777024
theorem maskCheck30796 :
    checkMaskFor missing30796 StrongPackedBucketN12A4Shard240.record30796 = true := by
  decide

def missing30797 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37435644687769698304
theorem maskCheck30797 :
    checkMaskFor missing30797 StrongPackedBucketN12A4Shard240.record30797 = true := by
  decide

def missing30798 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37723875063921410048
theorem maskCheck30798 :
    checkMaskFor missing30798 StrongPackedBucketN12A4Shard240.record30798 = true := by
  decide

def missing30799 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37976076643054157824
theorem maskCheck30799 :
    checkMaskFor missing30799 StrongPackedBucketN12A4Shard240.record30799 = true := by
  decide

def missing30800 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38732681380452401152
theorem maskCheck30800 :
    checkMaskFor missing30800 StrongPackedBucketN12A4Shard240.record30800 = true := by
  decide

def missing30801 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38840767771509293056
theorem maskCheck30801 :
    checkMaskFor missing30801 StrongPackedBucketN12A4Shard240.record30801 = true := by
  decide

def missing30802 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39453257320831680512
theorem maskCheck30802 :
    checkMaskFor missing30802 StrongPackedBucketN12A4Shard240.record30802 = true := by
  decide

def missing30803 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39705458899964428288
theorem maskCheck30803 :
    checkMaskFor missing30803 StrongPackedBucketN12A4Shard240.record30803 = true := by
  decide

def missing30804 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39885602885059248128
theorem maskCheck30804 :
    checkMaskFor missing30804 StrongPackedBucketN12A4Shard240.record30804 = true := by
  decide

def missing30805 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39993689276116140032
theorem maskCheck30805 :
    checkMaskFor missing30805 StrongPackedBucketN12A4Shard240.record30805 = true := by
  decide

def missing30806 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40966466795628167168
theorem maskCheck30806 :
    checkMaskFor missing30806 StrongPackedBucketN12A4Shard240.record30806 = true := by
  decide

def missing30807 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41002495592647131136
theorem maskCheck30807 :
    checkMaskFor missing30807 StrongPackedBucketN12A4Shard240.record30807 = true := by
  decide

def missing30808 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41759100330045374464
theorem maskCheck30808 :
    checkMaskFor missing30808 StrongPackedBucketN12A4Shard240.record30808 = true := by
  decide

def missing30809 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42011301909178122240
theorem maskCheck30809 :
    checkMaskFor missing30809 StrongPackedBucketN12A4Shard240.record30809 = true := by
  decide

def missing30810 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42191445894272942080
theorem maskCheck30810 :
    checkMaskFor missing30810 StrongPackedBucketN12A4Shard240.record30810 = true := by
  decide

def missing30811 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42299532285329833984
theorem maskCheck30811 :
    checkMaskFor missing30811 StrongPackedBucketN12A4Shard240.record30811 = true := by
  decide

def missing30812 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43308338601860825088
theorem maskCheck30812 :
    checkMaskFor missing30812 StrongPackedBucketN12A4Shard240.record30812 = true := by
  decide

def missing30813 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43920828151183212544
theorem maskCheck30813 :
    checkMaskFor missing30813 StrongPackedBucketN12A4Shard240.record30813 = true := by
  decide

def missing30814 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 44028914542240104448
theorem maskCheck30814 :
    checkMaskFor missing30814 StrongPackedBucketN12A4Shard240.record30814 = true := by
  decide

def missing30815 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 44461260106467672064
theorem maskCheck30815 :
    checkMaskFor missing30815 StrongPackedBucketN12A4Shard240.record30815 = true := by
  decide

def missing30816 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50946443569881186304
theorem maskCheck30816 :
    checkMaskFor missing30816 StrongPackedBucketN12A4Shard240.record30816 = true := by
  decide

def missing30817 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1119250611351617536
theorem maskCheck30817 :
    checkMaskFor missing30817 StrongPackedBucketN12A4Shard240.record30817 = true := by
  decide

def missing30818 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1983941739806752768
theorem maskCheck30818 :
    checkMaskFor missing30818 StrongPackedBucketN12A4Shard240.record30818 = true := by
  decide

def missing30819 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2200114521920536576
theorem maskCheck30819 :
    checkMaskFor missing30819 StrongPackedBucketN12A4Shard240.record30819 = true := by
  decide

def missing30820 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2236143318939500544
theorem maskCheck30820 :
    checkMaskFor missing30820 StrongPackedBucketN12A4Shard240.record30820 = true := by
  decide

def missing30821 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2848632868261888000
theorem maskCheck30821 :
    checkMaskFor missing30821 StrongPackedBucketN12A4Shard240.record30821 = true := by
  decide

def missing30822 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3136863244413599744
theorem maskCheck30822 :
    checkMaskFor missing30822 StrongPackedBucketN12A4Shard240.record30822 = true := by
  decide

def missing30823 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3353036026527383552
theorem maskCheck30823 :
    checkMaskFor missing30823 StrongPackedBucketN12A4Shard240.record30823 = true := by
  decide

def missing30824 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4145669560944590848
theorem maskCheck30824 :
    checkMaskFor missing30824 StrongPackedBucketN12A4Shard240.record30824 = true := by
  decide

def missing30825 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4217727154982518784
theorem maskCheck30825 :
    checkMaskFor missing30825 StrongPackedBucketN12A4Shard240.record30825 = true := by
  decide

def missing30826 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5154475877475581952
theorem maskCheck30826 :
    checkMaskFor missing30826 StrongPackedBucketN12A4Shard240.record30826 = true := by
  decide

def missing30827 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5442706253627293696
theorem maskCheck30827 :
    checkMaskFor missing30827 StrongPackedBucketN12A4Shard240.record30827 = true := by
  decide

def missing30828 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5658879035741077504
theorem maskCheck30828 :
    checkMaskFor missing30828 StrongPackedBucketN12A4Shard240.record30828 = true := by
  decide

def missing30829 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5694907832760041472
theorem maskCheck30829 :
    checkMaskFor missing30829 StrongPackedBucketN12A4Shard240.record30829 = true := by
  decide

def missing30830 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6451512570158284800
theorem maskCheck30830 :
    checkMaskFor missing30830 StrongPackedBucketN12A4Shard240.record30830 = true := by
  decide

def missing30831 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6523570164196212736
theorem maskCheck30831 :
    checkMaskFor missing30831 StrongPackedBucketN12A4Shard240.record30831 = true := by
  decide

def missing30832 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6559598961215176704
theorem maskCheck30832 :
    checkMaskFor missing30832 StrongPackedBucketN12A4Shard240.record30832 = true := by
  decide

def missing30833 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6775771743328960512
theorem maskCheck30833 :
    checkMaskFor missing30833 StrongPackedBucketN12A4Shard240.record30833 = true := by
  decide

def missing30834 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7172088510537564160
theorem maskCheck30834 :
    checkMaskFor missing30834 StrongPackedBucketN12A4Shard240.record30834 = true := by
  decide

def missing30835 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7388261292651347968
theorem maskCheck30835 :
    checkMaskFor missing30835 StrongPackedBucketN12A4Shard240.record30835 = true := by
  decide

def missing30836 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7604434074765131776
theorem maskCheck30836 :
    checkMaskFor missing30836 StrongPackedBucketN12A4Shard240.record30836 = true := by
  decide

def missing30837 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7676491668803059712
theorem maskCheck30837 :
    checkMaskFor missing30837 StrongPackedBucketN12A4Shard240.record30837 = true := by
  decide

def missing30838 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8685297985334050816
theorem maskCheck30838 :
    checkMaskFor missing30838 StrongPackedBucketN12A4Shard240.record30838 = true := by
  decide

def missing30839 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9766161895902969856
theorem maskCheck30839 :
    checkMaskFor missing30839 StrongPackedBucketN12A4Shard240.record30839 = true := by
  decide

def missing30840 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10054392272054681600
theorem maskCheck30840 :
    checkMaskFor missing30840 StrongPackedBucketN12A4Shard240.record30840 = true := by
  decide

def missing30841 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10270565054168465408
theorem maskCheck30841 :
    checkMaskFor missing30841 StrongPackedBucketN12A4Shard240.record30841 = true := by
  decide

def missing30842 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10306593851187429376
theorem maskCheck30842 :
    checkMaskFor missing30842 StrongPackedBucketN12A4Shard240.record30842 = true := by
  decide

def missing30843 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11135256182623600640
theorem maskCheck30843 :
    checkMaskFor missing30843 StrongPackedBucketN12A4Shard240.record30843 = true := by
  decide

def missing30844 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11171284979642564608
theorem maskCheck30844 :
    checkMaskFor missing30844 StrongPackedBucketN12A4Shard240.record30844 = true := by
  decide

def missing30845 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11387457761756348416
theorem maskCheck30845 :
    checkMaskFor missing30845 StrongPackedBucketN12A4Shard240.record30845 = true := by
  decide

def missing30846 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11783774528964952064
theorem maskCheck30846 :
    checkMaskFor missing30846 StrongPackedBucketN12A4Shard240.record30846 = true := by
  decide

def missing30847 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11999947311078735872
theorem maskCheck30847 :
    checkMaskFor missing30847 StrongPackedBucketN12A4Shard240.record30847 = true := by
  decide

def missing30720_30721 : List (BitVec (edgeCount 12)) :=
  [missing30720]
abbrev records30720_30721 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30720]
theorem aligned30720_30721 :
    AlignedValid 12 4 missing30720_30721 records30720_30721 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30720
    maskCheck30720 AlignedValid.nil

def missing30721_30722 : List (BitVec (edgeCount 12)) :=
  [missing30721]
abbrev records30721_30722 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30721]
theorem aligned30721_30722 :
    AlignedValid 12 4 missing30721_30722 records30721_30722 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30721
    maskCheck30721 AlignedValid.nil

def missing30720_30722 : List (BitVec (edgeCount 12)) :=
  missing30720_30721 ++ missing30721_30722
abbrev records30720_30722 : List Blob :=
  records30720_30721 ++ records30721_30722
theorem aligned30720_30722 :
    AlignedValid 12 4 missing30720_30722 records30720_30722 :=
  aligned30720_30721.append aligned30721_30722

def missing30722_30723 : List (BitVec (edgeCount 12)) :=
  [missing30722]
abbrev records30722_30723 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30722]
theorem aligned30722_30723 :
    AlignedValid 12 4 missing30722_30723 records30722_30723 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30722
    maskCheck30722 AlignedValid.nil

def missing30723_30724 : List (BitVec (edgeCount 12)) :=
  [missing30723]
abbrev records30723_30724 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30723]
theorem aligned30723_30724 :
    AlignedValid 12 4 missing30723_30724 records30723_30724 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30723
    maskCheck30723 AlignedValid.nil

def missing30722_30724 : List (BitVec (edgeCount 12)) :=
  missing30722_30723 ++ missing30723_30724
abbrev records30722_30724 : List Blob :=
  records30722_30723 ++ records30723_30724
theorem aligned30722_30724 :
    AlignedValid 12 4 missing30722_30724 records30722_30724 :=
  aligned30722_30723.append aligned30723_30724

def missing30720_30724 : List (BitVec (edgeCount 12)) :=
  missing30720_30722 ++ missing30722_30724
abbrev records30720_30724 : List Blob :=
  records30720_30722 ++ records30722_30724
theorem aligned30720_30724 :
    AlignedValid 12 4 missing30720_30724 records30720_30724 :=
  aligned30720_30722.append aligned30722_30724

def missing30724_30725 : List (BitVec (edgeCount 12)) :=
  [missing30724]
abbrev records30724_30725 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30724]
theorem aligned30724_30725 :
    AlignedValid 12 4 missing30724_30725 records30724_30725 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30724
    maskCheck30724 AlignedValid.nil

def missing30725_30726 : List (BitVec (edgeCount 12)) :=
  [missing30725]
abbrev records30725_30726 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30725]
theorem aligned30725_30726 :
    AlignedValid 12 4 missing30725_30726 records30725_30726 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30725
    maskCheck30725 AlignedValid.nil

def missing30724_30726 : List (BitVec (edgeCount 12)) :=
  missing30724_30725 ++ missing30725_30726
abbrev records30724_30726 : List Blob :=
  records30724_30725 ++ records30725_30726
theorem aligned30724_30726 :
    AlignedValid 12 4 missing30724_30726 records30724_30726 :=
  aligned30724_30725.append aligned30725_30726

def missing30726_30727 : List (BitVec (edgeCount 12)) :=
  [missing30726]
abbrev records30726_30727 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30726]
theorem aligned30726_30727 :
    AlignedValid 12 4 missing30726_30727 records30726_30727 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30726
    maskCheck30726 AlignedValid.nil

def missing30727_30728 : List (BitVec (edgeCount 12)) :=
  [missing30727]
abbrev records30727_30728 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30727]
theorem aligned30727_30728 :
    AlignedValid 12 4 missing30727_30728 records30727_30728 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30727
    maskCheck30727 AlignedValid.nil

def missing30726_30728 : List (BitVec (edgeCount 12)) :=
  missing30726_30727 ++ missing30727_30728
abbrev records30726_30728 : List Blob :=
  records30726_30727 ++ records30727_30728
theorem aligned30726_30728 :
    AlignedValid 12 4 missing30726_30728 records30726_30728 :=
  aligned30726_30727.append aligned30727_30728

def missing30724_30728 : List (BitVec (edgeCount 12)) :=
  missing30724_30726 ++ missing30726_30728
abbrev records30724_30728 : List Blob :=
  records30724_30726 ++ records30726_30728
theorem aligned30724_30728 :
    AlignedValid 12 4 missing30724_30728 records30724_30728 :=
  aligned30724_30726.append aligned30726_30728

def missing30720_30728 : List (BitVec (edgeCount 12)) :=
  missing30720_30724 ++ missing30724_30728
abbrev records30720_30728 : List Blob :=
  records30720_30724 ++ records30724_30728
theorem aligned30720_30728 :
    AlignedValid 12 4 missing30720_30728 records30720_30728 :=
  aligned30720_30724.append aligned30724_30728

def missing30728_30729 : List (BitVec (edgeCount 12)) :=
  [missing30728]
abbrev records30728_30729 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30728]
theorem aligned30728_30729 :
    AlignedValid 12 4 missing30728_30729 records30728_30729 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30728
    maskCheck30728 AlignedValid.nil

def missing30729_30730 : List (BitVec (edgeCount 12)) :=
  [missing30729]
abbrev records30729_30730 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30729]
theorem aligned30729_30730 :
    AlignedValid 12 4 missing30729_30730 records30729_30730 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30729
    maskCheck30729 AlignedValid.nil

def missing30728_30730 : List (BitVec (edgeCount 12)) :=
  missing30728_30729 ++ missing30729_30730
abbrev records30728_30730 : List Blob :=
  records30728_30729 ++ records30729_30730
theorem aligned30728_30730 :
    AlignedValid 12 4 missing30728_30730 records30728_30730 :=
  aligned30728_30729.append aligned30729_30730

def missing30730_30731 : List (BitVec (edgeCount 12)) :=
  [missing30730]
abbrev records30730_30731 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30730]
theorem aligned30730_30731 :
    AlignedValid 12 4 missing30730_30731 records30730_30731 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30730
    maskCheck30730 AlignedValid.nil

def missing30731_30732 : List (BitVec (edgeCount 12)) :=
  [missing30731]
abbrev records30731_30732 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30731]
theorem aligned30731_30732 :
    AlignedValid 12 4 missing30731_30732 records30731_30732 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30731
    maskCheck30731 AlignedValid.nil

def missing30730_30732 : List (BitVec (edgeCount 12)) :=
  missing30730_30731 ++ missing30731_30732
abbrev records30730_30732 : List Blob :=
  records30730_30731 ++ records30731_30732
theorem aligned30730_30732 :
    AlignedValid 12 4 missing30730_30732 records30730_30732 :=
  aligned30730_30731.append aligned30731_30732

def missing30728_30732 : List (BitVec (edgeCount 12)) :=
  missing30728_30730 ++ missing30730_30732
abbrev records30728_30732 : List Blob :=
  records30728_30730 ++ records30730_30732
theorem aligned30728_30732 :
    AlignedValid 12 4 missing30728_30732 records30728_30732 :=
  aligned30728_30730.append aligned30730_30732

def missing30732_30733 : List (BitVec (edgeCount 12)) :=
  [missing30732]
abbrev records30732_30733 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30732]
theorem aligned30732_30733 :
    AlignedValid 12 4 missing30732_30733 records30732_30733 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30732
    maskCheck30732 AlignedValid.nil

def missing30733_30734 : List (BitVec (edgeCount 12)) :=
  [missing30733]
abbrev records30733_30734 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30733]
theorem aligned30733_30734 :
    AlignedValid 12 4 missing30733_30734 records30733_30734 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30733
    maskCheck30733 AlignedValid.nil

def missing30732_30734 : List (BitVec (edgeCount 12)) :=
  missing30732_30733 ++ missing30733_30734
abbrev records30732_30734 : List Blob :=
  records30732_30733 ++ records30733_30734
theorem aligned30732_30734 :
    AlignedValid 12 4 missing30732_30734 records30732_30734 :=
  aligned30732_30733.append aligned30733_30734

def missing30734_30735 : List (BitVec (edgeCount 12)) :=
  [missing30734]
abbrev records30734_30735 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30734]
theorem aligned30734_30735 :
    AlignedValid 12 4 missing30734_30735 records30734_30735 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30734
    maskCheck30734 AlignedValid.nil

def missing30735_30736 : List (BitVec (edgeCount 12)) :=
  [missing30735]
abbrev records30735_30736 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30735]
theorem aligned30735_30736 :
    AlignedValid 12 4 missing30735_30736 records30735_30736 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30735
    maskCheck30735 AlignedValid.nil

def missing30734_30736 : List (BitVec (edgeCount 12)) :=
  missing30734_30735 ++ missing30735_30736
abbrev records30734_30736 : List Blob :=
  records30734_30735 ++ records30735_30736
theorem aligned30734_30736 :
    AlignedValid 12 4 missing30734_30736 records30734_30736 :=
  aligned30734_30735.append aligned30735_30736

def missing30732_30736 : List (BitVec (edgeCount 12)) :=
  missing30732_30734 ++ missing30734_30736
abbrev records30732_30736 : List Blob :=
  records30732_30734 ++ records30734_30736
theorem aligned30732_30736 :
    AlignedValid 12 4 missing30732_30736 records30732_30736 :=
  aligned30732_30734.append aligned30734_30736

def missing30728_30736 : List (BitVec (edgeCount 12)) :=
  missing30728_30732 ++ missing30732_30736
abbrev records30728_30736 : List Blob :=
  records30728_30732 ++ records30732_30736
theorem aligned30728_30736 :
    AlignedValid 12 4 missing30728_30736 records30728_30736 :=
  aligned30728_30732.append aligned30732_30736

def missing30720_30736 : List (BitVec (edgeCount 12)) :=
  missing30720_30728 ++ missing30728_30736
abbrev records30720_30736 : List Blob :=
  records30720_30728 ++ records30728_30736
theorem aligned30720_30736 :
    AlignedValid 12 4 missing30720_30736 records30720_30736 :=
  aligned30720_30728.append aligned30728_30736

def missing30736_30737 : List (BitVec (edgeCount 12)) :=
  [missing30736]
abbrev records30736_30737 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30736]
theorem aligned30736_30737 :
    AlignedValid 12 4 missing30736_30737 records30736_30737 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30736
    maskCheck30736 AlignedValid.nil

def missing30737_30738 : List (BitVec (edgeCount 12)) :=
  [missing30737]
abbrev records30737_30738 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30737]
theorem aligned30737_30738 :
    AlignedValid 12 4 missing30737_30738 records30737_30738 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30737
    maskCheck30737 AlignedValid.nil

def missing30736_30738 : List (BitVec (edgeCount 12)) :=
  missing30736_30737 ++ missing30737_30738
abbrev records30736_30738 : List Blob :=
  records30736_30737 ++ records30737_30738
theorem aligned30736_30738 :
    AlignedValid 12 4 missing30736_30738 records30736_30738 :=
  aligned30736_30737.append aligned30737_30738

def missing30738_30739 : List (BitVec (edgeCount 12)) :=
  [missing30738]
abbrev records30738_30739 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30738]
theorem aligned30738_30739 :
    AlignedValid 12 4 missing30738_30739 records30738_30739 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30738
    maskCheck30738 AlignedValid.nil

def missing30739_30740 : List (BitVec (edgeCount 12)) :=
  [missing30739]
abbrev records30739_30740 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30739]
theorem aligned30739_30740 :
    AlignedValid 12 4 missing30739_30740 records30739_30740 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30739
    maskCheck30739 AlignedValid.nil

def missing30738_30740 : List (BitVec (edgeCount 12)) :=
  missing30738_30739 ++ missing30739_30740
abbrev records30738_30740 : List Blob :=
  records30738_30739 ++ records30739_30740
theorem aligned30738_30740 :
    AlignedValid 12 4 missing30738_30740 records30738_30740 :=
  aligned30738_30739.append aligned30739_30740

def missing30736_30740 : List (BitVec (edgeCount 12)) :=
  missing30736_30738 ++ missing30738_30740
abbrev records30736_30740 : List Blob :=
  records30736_30738 ++ records30738_30740
theorem aligned30736_30740 :
    AlignedValid 12 4 missing30736_30740 records30736_30740 :=
  aligned30736_30738.append aligned30738_30740

def missing30740_30741 : List (BitVec (edgeCount 12)) :=
  [missing30740]
abbrev records30740_30741 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30740]
theorem aligned30740_30741 :
    AlignedValid 12 4 missing30740_30741 records30740_30741 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30740
    maskCheck30740 AlignedValid.nil

def missing30741_30742 : List (BitVec (edgeCount 12)) :=
  [missing30741]
abbrev records30741_30742 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30741]
theorem aligned30741_30742 :
    AlignedValid 12 4 missing30741_30742 records30741_30742 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30741
    maskCheck30741 AlignedValid.nil

def missing30740_30742 : List (BitVec (edgeCount 12)) :=
  missing30740_30741 ++ missing30741_30742
abbrev records30740_30742 : List Blob :=
  records30740_30741 ++ records30741_30742
theorem aligned30740_30742 :
    AlignedValid 12 4 missing30740_30742 records30740_30742 :=
  aligned30740_30741.append aligned30741_30742

def missing30742_30743 : List (BitVec (edgeCount 12)) :=
  [missing30742]
abbrev records30742_30743 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30742]
theorem aligned30742_30743 :
    AlignedValid 12 4 missing30742_30743 records30742_30743 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30742
    maskCheck30742 AlignedValid.nil

def missing30743_30744 : List (BitVec (edgeCount 12)) :=
  [missing30743]
abbrev records30743_30744 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30743]
theorem aligned30743_30744 :
    AlignedValid 12 4 missing30743_30744 records30743_30744 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30743
    maskCheck30743 AlignedValid.nil

def missing30742_30744 : List (BitVec (edgeCount 12)) :=
  missing30742_30743 ++ missing30743_30744
abbrev records30742_30744 : List Blob :=
  records30742_30743 ++ records30743_30744
theorem aligned30742_30744 :
    AlignedValid 12 4 missing30742_30744 records30742_30744 :=
  aligned30742_30743.append aligned30743_30744

def missing30740_30744 : List (BitVec (edgeCount 12)) :=
  missing30740_30742 ++ missing30742_30744
abbrev records30740_30744 : List Blob :=
  records30740_30742 ++ records30742_30744
theorem aligned30740_30744 :
    AlignedValid 12 4 missing30740_30744 records30740_30744 :=
  aligned30740_30742.append aligned30742_30744

def missing30736_30744 : List (BitVec (edgeCount 12)) :=
  missing30736_30740 ++ missing30740_30744
abbrev records30736_30744 : List Blob :=
  records30736_30740 ++ records30740_30744
theorem aligned30736_30744 :
    AlignedValid 12 4 missing30736_30744 records30736_30744 :=
  aligned30736_30740.append aligned30740_30744

def missing30744_30745 : List (BitVec (edgeCount 12)) :=
  [missing30744]
abbrev records30744_30745 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30744]
theorem aligned30744_30745 :
    AlignedValid 12 4 missing30744_30745 records30744_30745 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30744
    maskCheck30744 AlignedValid.nil

def missing30745_30746 : List (BitVec (edgeCount 12)) :=
  [missing30745]
abbrev records30745_30746 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30745]
theorem aligned30745_30746 :
    AlignedValid 12 4 missing30745_30746 records30745_30746 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30745
    maskCheck30745 AlignedValid.nil

def missing30744_30746 : List (BitVec (edgeCount 12)) :=
  missing30744_30745 ++ missing30745_30746
abbrev records30744_30746 : List Blob :=
  records30744_30745 ++ records30745_30746
theorem aligned30744_30746 :
    AlignedValid 12 4 missing30744_30746 records30744_30746 :=
  aligned30744_30745.append aligned30745_30746

def missing30746_30747 : List (BitVec (edgeCount 12)) :=
  [missing30746]
abbrev records30746_30747 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30746]
theorem aligned30746_30747 :
    AlignedValid 12 4 missing30746_30747 records30746_30747 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30746
    maskCheck30746 AlignedValid.nil

def missing30747_30748 : List (BitVec (edgeCount 12)) :=
  [missing30747]
abbrev records30747_30748 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30747]
theorem aligned30747_30748 :
    AlignedValid 12 4 missing30747_30748 records30747_30748 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30747
    maskCheck30747 AlignedValid.nil

def missing30746_30748 : List (BitVec (edgeCount 12)) :=
  missing30746_30747 ++ missing30747_30748
abbrev records30746_30748 : List Blob :=
  records30746_30747 ++ records30747_30748
theorem aligned30746_30748 :
    AlignedValid 12 4 missing30746_30748 records30746_30748 :=
  aligned30746_30747.append aligned30747_30748

def missing30744_30748 : List (BitVec (edgeCount 12)) :=
  missing30744_30746 ++ missing30746_30748
abbrev records30744_30748 : List Blob :=
  records30744_30746 ++ records30746_30748
theorem aligned30744_30748 :
    AlignedValid 12 4 missing30744_30748 records30744_30748 :=
  aligned30744_30746.append aligned30746_30748

def missing30748_30749 : List (BitVec (edgeCount 12)) :=
  [missing30748]
abbrev records30748_30749 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30748]
theorem aligned30748_30749 :
    AlignedValid 12 4 missing30748_30749 records30748_30749 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30748
    maskCheck30748 AlignedValid.nil

def missing30749_30750 : List (BitVec (edgeCount 12)) :=
  [missing30749]
abbrev records30749_30750 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30749]
theorem aligned30749_30750 :
    AlignedValid 12 4 missing30749_30750 records30749_30750 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30749
    maskCheck30749 AlignedValid.nil

def missing30748_30750 : List (BitVec (edgeCount 12)) :=
  missing30748_30749 ++ missing30749_30750
abbrev records30748_30750 : List Blob :=
  records30748_30749 ++ records30749_30750
theorem aligned30748_30750 :
    AlignedValid 12 4 missing30748_30750 records30748_30750 :=
  aligned30748_30749.append aligned30749_30750

def missing30750_30751 : List (BitVec (edgeCount 12)) :=
  [missing30750]
abbrev records30750_30751 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30750]
theorem aligned30750_30751 :
    AlignedValid 12 4 missing30750_30751 records30750_30751 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30750
    maskCheck30750 AlignedValid.nil

def missing30751_30752 : List (BitVec (edgeCount 12)) :=
  [missing30751]
abbrev records30751_30752 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30751]
theorem aligned30751_30752 :
    AlignedValid 12 4 missing30751_30752 records30751_30752 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30751
    maskCheck30751 AlignedValid.nil

def missing30750_30752 : List (BitVec (edgeCount 12)) :=
  missing30750_30751 ++ missing30751_30752
abbrev records30750_30752 : List Blob :=
  records30750_30751 ++ records30751_30752
theorem aligned30750_30752 :
    AlignedValid 12 4 missing30750_30752 records30750_30752 :=
  aligned30750_30751.append aligned30751_30752

def missing30748_30752 : List (BitVec (edgeCount 12)) :=
  missing30748_30750 ++ missing30750_30752
abbrev records30748_30752 : List Blob :=
  records30748_30750 ++ records30750_30752
theorem aligned30748_30752 :
    AlignedValid 12 4 missing30748_30752 records30748_30752 :=
  aligned30748_30750.append aligned30750_30752

def missing30744_30752 : List (BitVec (edgeCount 12)) :=
  missing30744_30748 ++ missing30748_30752
abbrev records30744_30752 : List Blob :=
  records30744_30748 ++ records30748_30752
theorem aligned30744_30752 :
    AlignedValid 12 4 missing30744_30752 records30744_30752 :=
  aligned30744_30748.append aligned30748_30752

def missing30736_30752 : List (BitVec (edgeCount 12)) :=
  missing30736_30744 ++ missing30744_30752
abbrev records30736_30752 : List Blob :=
  records30736_30744 ++ records30744_30752
theorem aligned30736_30752 :
    AlignedValid 12 4 missing30736_30752 records30736_30752 :=
  aligned30736_30744.append aligned30744_30752

def missing30720_30752 : List (BitVec (edgeCount 12)) :=
  missing30720_30736 ++ missing30736_30752
abbrev records30720_30752 : List Blob :=
  records30720_30736 ++ records30736_30752
theorem aligned30720_30752 :
    AlignedValid 12 4 missing30720_30752 records30720_30752 :=
  aligned30720_30736.append aligned30736_30752

def missing30752_30753 : List (BitVec (edgeCount 12)) :=
  [missing30752]
abbrev records30752_30753 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30752]
theorem aligned30752_30753 :
    AlignedValid 12 4 missing30752_30753 records30752_30753 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30752
    maskCheck30752 AlignedValid.nil

def missing30753_30754 : List (BitVec (edgeCount 12)) :=
  [missing30753]
abbrev records30753_30754 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30753]
theorem aligned30753_30754 :
    AlignedValid 12 4 missing30753_30754 records30753_30754 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30753
    maskCheck30753 AlignedValid.nil

def missing30752_30754 : List (BitVec (edgeCount 12)) :=
  missing30752_30753 ++ missing30753_30754
abbrev records30752_30754 : List Blob :=
  records30752_30753 ++ records30753_30754
theorem aligned30752_30754 :
    AlignedValid 12 4 missing30752_30754 records30752_30754 :=
  aligned30752_30753.append aligned30753_30754

def missing30754_30755 : List (BitVec (edgeCount 12)) :=
  [missing30754]
abbrev records30754_30755 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30754]
theorem aligned30754_30755 :
    AlignedValid 12 4 missing30754_30755 records30754_30755 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30754
    maskCheck30754 AlignedValid.nil

def missing30755_30756 : List (BitVec (edgeCount 12)) :=
  [missing30755]
abbrev records30755_30756 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30755]
theorem aligned30755_30756 :
    AlignedValid 12 4 missing30755_30756 records30755_30756 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30755
    maskCheck30755 AlignedValid.nil

def missing30754_30756 : List (BitVec (edgeCount 12)) :=
  missing30754_30755 ++ missing30755_30756
abbrev records30754_30756 : List Blob :=
  records30754_30755 ++ records30755_30756
theorem aligned30754_30756 :
    AlignedValid 12 4 missing30754_30756 records30754_30756 :=
  aligned30754_30755.append aligned30755_30756

def missing30752_30756 : List (BitVec (edgeCount 12)) :=
  missing30752_30754 ++ missing30754_30756
abbrev records30752_30756 : List Blob :=
  records30752_30754 ++ records30754_30756
theorem aligned30752_30756 :
    AlignedValid 12 4 missing30752_30756 records30752_30756 :=
  aligned30752_30754.append aligned30754_30756

def missing30756_30757 : List (BitVec (edgeCount 12)) :=
  [missing30756]
abbrev records30756_30757 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30756]
theorem aligned30756_30757 :
    AlignedValid 12 4 missing30756_30757 records30756_30757 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30756
    maskCheck30756 AlignedValid.nil

def missing30757_30758 : List (BitVec (edgeCount 12)) :=
  [missing30757]
abbrev records30757_30758 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30757]
theorem aligned30757_30758 :
    AlignedValid 12 4 missing30757_30758 records30757_30758 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30757
    maskCheck30757 AlignedValid.nil

def missing30756_30758 : List (BitVec (edgeCount 12)) :=
  missing30756_30757 ++ missing30757_30758
abbrev records30756_30758 : List Blob :=
  records30756_30757 ++ records30757_30758
theorem aligned30756_30758 :
    AlignedValid 12 4 missing30756_30758 records30756_30758 :=
  aligned30756_30757.append aligned30757_30758

def missing30758_30759 : List (BitVec (edgeCount 12)) :=
  [missing30758]
abbrev records30758_30759 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30758]
theorem aligned30758_30759 :
    AlignedValid 12 4 missing30758_30759 records30758_30759 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30758
    maskCheck30758 AlignedValid.nil

def missing30759_30760 : List (BitVec (edgeCount 12)) :=
  [missing30759]
abbrev records30759_30760 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30759]
theorem aligned30759_30760 :
    AlignedValid 12 4 missing30759_30760 records30759_30760 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30759
    maskCheck30759 AlignedValid.nil

def missing30758_30760 : List (BitVec (edgeCount 12)) :=
  missing30758_30759 ++ missing30759_30760
abbrev records30758_30760 : List Blob :=
  records30758_30759 ++ records30759_30760
theorem aligned30758_30760 :
    AlignedValid 12 4 missing30758_30760 records30758_30760 :=
  aligned30758_30759.append aligned30759_30760

def missing30756_30760 : List (BitVec (edgeCount 12)) :=
  missing30756_30758 ++ missing30758_30760
abbrev records30756_30760 : List Blob :=
  records30756_30758 ++ records30758_30760
theorem aligned30756_30760 :
    AlignedValid 12 4 missing30756_30760 records30756_30760 :=
  aligned30756_30758.append aligned30758_30760

def missing30752_30760 : List (BitVec (edgeCount 12)) :=
  missing30752_30756 ++ missing30756_30760
abbrev records30752_30760 : List Blob :=
  records30752_30756 ++ records30756_30760
theorem aligned30752_30760 :
    AlignedValid 12 4 missing30752_30760 records30752_30760 :=
  aligned30752_30756.append aligned30756_30760

def missing30760_30761 : List (BitVec (edgeCount 12)) :=
  [missing30760]
abbrev records30760_30761 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30760]
theorem aligned30760_30761 :
    AlignedValid 12 4 missing30760_30761 records30760_30761 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30760
    maskCheck30760 AlignedValid.nil

def missing30761_30762 : List (BitVec (edgeCount 12)) :=
  [missing30761]
abbrev records30761_30762 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30761]
theorem aligned30761_30762 :
    AlignedValid 12 4 missing30761_30762 records30761_30762 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30761
    maskCheck30761 AlignedValid.nil

def missing30760_30762 : List (BitVec (edgeCount 12)) :=
  missing30760_30761 ++ missing30761_30762
abbrev records30760_30762 : List Blob :=
  records30760_30761 ++ records30761_30762
theorem aligned30760_30762 :
    AlignedValid 12 4 missing30760_30762 records30760_30762 :=
  aligned30760_30761.append aligned30761_30762

def missing30762_30763 : List (BitVec (edgeCount 12)) :=
  [missing30762]
abbrev records30762_30763 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30762]
theorem aligned30762_30763 :
    AlignedValid 12 4 missing30762_30763 records30762_30763 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30762
    maskCheck30762 AlignedValid.nil

def missing30763_30764 : List (BitVec (edgeCount 12)) :=
  [missing30763]
abbrev records30763_30764 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30763]
theorem aligned30763_30764 :
    AlignedValid 12 4 missing30763_30764 records30763_30764 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30763
    maskCheck30763 AlignedValid.nil

def missing30762_30764 : List (BitVec (edgeCount 12)) :=
  missing30762_30763 ++ missing30763_30764
abbrev records30762_30764 : List Blob :=
  records30762_30763 ++ records30763_30764
theorem aligned30762_30764 :
    AlignedValid 12 4 missing30762_30764 records30762_30764 :=
  aligned30762_30763.append aligned30763_30764

def missing30760_30764 : List (BitVec (edgeCount 12)) :=
  missing30760_30762 ++ missing30762_30764
abbrev records30760_30764 : List Blob :=
  records30760_30762 ++ records30762_30764
theorem aligned30760_30764 :
    AlignedValid 12 4 missing30760_30764 records30760_30764 :=
  aligned30760_30762.append aligned30762_30764

def missing30764_30765 : List (BitVec (edgeCount 12)) :=
  [missing30764]
abbrev records30764_30765 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30764]
theorem aligned30764_30765 :
    AlignedValid 12 4 missing30764_30765 records30764_30765 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30764
    maskCheck30764 AlignedValid.nil

def missing30765_30766 : List (BitVec (edgeCount 12)) :=
  [missing30765]
abbrev records30765_30766 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30765]
theorem aligned30765_30766 :
    AlignedValid 12 4 missing30765_30766 records30765_30766 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30765
    maskCheck30765 AlignedValid.nil

def missing30764_30766 : List (BitVec (edgeCount 12)) :=
  missing30764_30765 ++ missing30765_30766
abbrev records30764_30766 : List Blob :=
  records30764_30765 ++ records30765_30766
theorem aligned30764_30766 :
    AlignedValid 12 4 missing30764_30766 records30764_30766 :=
  aligned30764_30765.append aligned30765_30766

def missing30766_30767 : List (BitVec (edgeCount 12)) :=
  [missing30766]
abbrev records30766_30767 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30766]
theorem aligned30766_30767 :
    AlignedValid 12 4 missing30766_30767 records30766_30767 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30766
    maskCheck30766 AlignedValid.nil

def missing30767_30768 : List (BitVec (edgeCount 12)) :=
  [missing30767]
abbrev records30767_30768 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30767]
theorem aligned30767_30768 :
    AlignedValid 12 4 missing30767_30768 records30767_30768 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30767
    maskCheck30767 AlignedValid.nil

def missing30766_30768 : List (BitVec (edgeCount 12)) :=
  missing30766_30767 ++ missing30767_30768
abbrev records30766_30768 : List Blob :=
  records30766_30767 ++ records30767_30768
theorem aligned30766_30768 :
    AlignedValid 12 4 missing30766_30768 records30766_30768 :=
  aligned30766_30767.append aligned30767_30768

def missing30764_30768 : List (BitVec (edgeCount 12)) :=
  missing30764_30766 ++ missing30766_30768
abbrev records30764_30768 : List Blob :=
  records30764_30766 ++ records30766_30768
theorem aligned30764_30768 :
    AlignedValid 12 4 missing30764_30768 records30764_30768 :=
  aligned30764_30766.append aligned30766_30768

def missing30760_30768 : List (BitVec (edgeCount 12)) :=
  missing30760_30764 ++ missing30764_30768
abbrev records30760_30768 : List Blob :=
  records30760_30764 ++ records30764_30768
theorem aligned30760_30768 :
    AlignedValid 12 4 missing30760_30768 records30760_30768 :=
  aligned30760_30764.append aligned30764_30768

def missing30752_30768 : List (BitVec (edgeCount 12)) :=
  missing30752_30760 ++ missing30760_30768
abbrev records30752_30768 : List Blob :=
  records30752_30760 ++ records30760_30768
theorem aligned30752_30768 :
    AlignedValid 12 4 missing30752_30768 records30752_30768 :=
  aligned30752_30760.append aligned30760_30768

def missing30768_30769 : List (BitVec (edgeCount 12)) :=
  [missing30768]
abbrev records30768_30769 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30768]
theorem aligned30768_30769 :
    AlignedValid 12 4 missing30768_30769 records30768_30769 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30768
    maskCheck30768 AlignedValid.nil

def missing30769_30770 : List (BitVec (edgeCount 12)) :=
  [missing30769]
abbrev records30769_30770 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30769]
theorem aligned30769_30770 :
    AlignedValid 12 4 missing30769_30770 records30769_30770 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30769
    maskCheck30769 AlignedValid.nil

def missing30768_30770 : List (BitVec (edgeCount 12)) :=
  missing30768_30769 ++ missing30769_30770
abbrev records30768_30770 : List Blob :=
  records30768_30769 ++ records30769_30770
theorem aligned30768_30770 :
    AlignedValid 12 4 missing30768_30770 records30768_30770 :=
  aligned30768_30769.append aligned30769_30770

def missing30770_30771 : List (BitVec (edgeCount 12)) :=
  [missing30770]
abbrev records30770_30771 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30770]
theorem aligned30770_30771 :
    AlignedValid 12 4 missing30770_30771 records30770_30771 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30770
    maskCheck30770 AlignedValid.nil

def missing30771_30772 : List (BitVec (edgeCount 12)) :=
  [missing30771]
abbrev records30771_30772 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30771]
theorem aligned30771_30772 :
    AlignedValid 12 4 missing30771_30772 records30771_30772 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30771
    maskCheck30771 AlignedValid.nil

def missing30770_30772 : List (BitVec (edgeCount 12)) :=
  missing30770_30771 ++ missing30771_30772
abbrev records30770_30772 : List Blob :=
  records30770_30771 ++ records30771_30772
theorem aligned30770_30772 :
    AlignedValid 12 4 missing30770_30772 records30770_30772 :=
  aligned30770_30771.append aligned30771_30772

def missing30768_30772 : List (BitVec (edgeCount 12)) :=
  missing30768_30770 ++ missing30770_30772
abbrev records30768_30772 : List Blob :=
  records30768_30770 ++ records30770_30772
theorem aligned30768_30772 :
    AlignedValid 12 4 missing30768_30772 records30768_30772 :=
  aligned30768_30770.append aligned30770_30772

def missing30772_30773 : List (BitVec (edgeCount 12)) :=
  [missing30772]
abbrev records30772_30773 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30772]
theorem aligned30772_30773 :
    AlignedValid 12 4 missing30772_30773 records30772_30773 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30772
    maskCheck30772 AlignedValid.nil

def missing30773_30774 : List (BitVec (edgeCount 12)) :=
  [missing30773]
abbrev records30773_30774 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30773]
theorem aligned30773_30774 :
    AlignedValid 12 4 missing30773_30774 records30773_30774 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30773
    maskCheck30773 AlignedValid.nil

def missing30772_30774 : List (BitVec (edgeCount 12)) :=
  missing30772_30773 ++ missing30773_30774
abbrev records30772_30774 : List Blob :=
  records30772_30773 ++ records30773_30774
theorem aligned30772_30774 :
    AlignedValid 12 4 missing30772_30774 records30772_30774 :=
  aligned30772_30773.append aligned30773_30774

def missing30774_30775 : List (BitVec (edgeCount 12)) :=
  [missing30774]
abbrev records30774_30775 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30774]
theorem aligned30774_30775 :
    AlignedValid 12 4 missing30774_30775 records30774_30775 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30774
    maskCheck30774 AlignedValid.nil

def missing30775_30776 : List (BitVec (edgeCount 12)) :=
  [missing30775]
abbrev records30775_30776 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30775]
theorem aligned30775_30776 :
    AlignedValid 12 4 missing30775_30776 records30775_30776 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30775
    maskCheck30775 AlignedValid.nil

def missing30774_30776 : List (BitVec (edgeCount 12)) :=
  missing30774_30775 ++ missing30775_30776
abbrev records30774_30776 : List Blob :=
  records30774_30775 ++ records30775_30776
theorem aligned30774_30776 :
    AlignedValid 12 4 missing30774_30776 records30774_30776 :=
  aligned30774_30775.append aligned30775_30776

def missing30772_30776 : List (BitVec (edgeCount 12)) :=
  missing30772_30774 ++ missing30774_30776
abbrev records30772_30776 : List Blob :=
  records30772_30774 ++ records30774_30776
theorem aligned30772_30776 :
    AlignedValid 12 4 missing30772_30776 records30772_30776 :=
  aligned30772_30774.append aligned30774_30776

def missing30768_30776 : List (BitVec (edgeCount 12)) :=
  missing30768_30772 ++ missing30772_30776
abbrev records30768_30776 : List Blob :=
  records30768_30772 ++ records30772_30776
theorem aligned30768_30776 :
    AlignedValid 12 4 missing30768_30776 records30768_30776 :=
  aligned30768_30772.append aligned30772_30776

def missing30776_30777 : List (BitVec (edgeCount 12)) :=
  [missing30776]
abbrev records30776_30777 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30776]
theorem aligned30776_30777 :
    AlignedValid 12 4 missing30776_30777 records30776_30777 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30776
    maskCheck30776 AlignedValid.nil

def missing30777_30778 : List (BitVec (edgeCount 12)) :=
  [missing30777]
abbrev records30777_30778 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30777]
theorem aligned30777_30778 :
    AlignedValid 12 4 missing30777_30778 records30777_30778 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30777
    maskCheck30777 AlignedValid.nil

def missing30776_30778 : List (BitVec (edgeCount 12)) :=
  missing30776_30777 ++ missing30777_30778
abbrev records30776_30778 : List Blob :=
  records30776_30777 ++ records30777_30778
theorem aligned30776_30778 :
    AlignedValid 12 4 missing30776_30778 records30776_30778 :=
  aligned30776_30777.append aligned30777_30778

def missing30778_30779 : List (BitVec (edgeCount 12)) :=
  [missing30778]
abbrev records30778_30779 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30778]
theorem aligned30778_30779 :
    AlignedValid 12 4 missing30778_30779 records30778_30779 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30778
    maskCheck30778 AlignedValid.nil

def missing30779_30780 : List (BitVec (edgeCount 12)) :=
  [missing30779]
abbrev records30779_30780 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30779]
theorem aligned30779_30780 :
    AlignedValid 12 4 missing30779_30780 records30779_30780 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30779
    maskCheck30779 AlignedValid.nil

def missing30778_30780 : List (BitVec (edgeCount 12)) :=
  missing30778_30779 ++ missing30779_30780
abbrev records30778_30780 : List Blob :=
  records30778_30779 ++ records30779_30780
theorem aligned30778_30780 :
    AlignedValid 12 4 missing30778_30780 records30778_30780 :=
  aligned30778_30779.append aligned30779_30780

def missing30776_30780 : List (BitVec (edgeCount 12)) :=
  missing30776_30778 ++ missing30778_30780
abbrev records30776_30780 : List Blob :=
  records30776_30778 ++ records30778_30780
theorem aligned30776_30780 :
    AlignedValid 12 4 missing30776_30780 records30776_30780 :=
  aligned30776_30778.append aligned30778_30780

def missing30780_30781 : List (BitVec (edgeCount 12)) :=
  [missing30780]
abbrev records30780_30781 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30780]
theorem aligned30780_30781 :
    AlignedValid 12 4 missing30780_30781 records30780_30781 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30780
    maskCheck30780 AlignedValid.nil

def missing30781_30782 : List (BitVec (edgeCount 12)) :=
  [missing30781]
abbrev records30781_30782 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30781]
theorem aligned30781_30782 :
    AlignedValid 12 4 missing30781_30782 records30781_30782 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30781
    maskCheck30781 AlignedValid.nil

def missing30780_30782 : List (BitVec (edgeCount 12)) :=
  missing30780_30781 ++ missing30781_30782
abbrev records30780_30782 : List Blob :=
  records30780_30781 ++ records30781_30782
theorem aligned30780_30782 :
    AlignedValid 12 4 missing30780_30782 records30780_30782 :=
  aligned30780_30781.append aligned30781_30782

def missing30782_30783 : List (BitVec (edgeCount 12)) :=
  [missing30782]
abbrev records30782_30783 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30782]
theorem aligned30782_30783 :
    AlignedValid 12 4 missing30782_30783 records30782_30783 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30782
    maskCheck30782 AlignedValid.nil

def missing30783_30784 : List (BitVec (edgeCount 12)) :=
  [missing30783]
abbrev records30783_30784 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30783]
theorem aligned30783_30784 :
    AlignedValid 12 4 missing30783_30784 records30783_30784 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30783
    maskCheck30783 AlignedValid.nil

def missing30782_30784 : List (BitVec (edgeCount 12)) :=
  missing30782_30783 ++ missing30783_30784
abbrev records30782_30784 : List Blob :=
  records30782_30783 ++ records30783_30784
theorem aligned30782_30784 :
    AlignedValid 12 4 missing30782_30784 records30782_30784 :=
  aligned30782_30783.append aligned30783_30784

def missing30780_30784 : List (BitVec (edgeCount 12)) :=
  missing30780_30782 ++ missing30782_30784
abbrev records30780_30784 : List Blob :=
  records30780_30782 ++ records30782_30784
theorem aligned30780_30784 :
    AlignedValid 12 4 missing30780_30784 records30780_30784 :=
  aligned30780_30782.append aligned30782_30784

def missing30776_30784 : List (BitVec (edgeCount 12)) :=
  missing30776_30780 ++ missing30780_30784
abbrev records30776_30784 : List Blob :=
  records30776_30780 ++ records30780_30784
theorem aligned30776_30784 :
    AlignedValid 12 4 missing30776_30784 records30776_30784 :=
  aligned30776_30780.append aligned30780_30784

def missing30768_30784 : List (BitVec (edgeCount 12)) :=
  missing30768_30776 ++ missing30776_30784
abbrev records30768_30784 : List Blob :=
  records30768_30776 ++ records30776_30784
theorem aligned30768_30784 :
    AlignedValid 12 4 missing30768_30784 records30768_30784 :=
  aligned30768_30776.append aligned30776_30784

def missing30752_30784 : List (BitVec (edgeCount 12)) :=
  missing30752_30768 ++ missing30768_30784
abbrev records30752_30784 : List Blob :=
  records30752_30768 ++ records30768_30784
theorem aligned30752_30784 :
    AlignedValid 12 4 missing30752_30784 records30752_30784 :=
  aligned30752_30768.append aligned30768_30784

def missing30720_30784 : List (BitVec (edgeCount 12)) :=
  missing30720_30752 ++ missing30752_30784
abbrev records30720_30784 : List Blob :=
  records30720_30752 ++ records30752_30784
theorem aligned30720_30784 :
    AlignedValid 12 4 missing30720_30784 records30720_30784 :=
  aligned30720_30752.append aligned30752_30784

def missing30784_30785 : List (BitVec (edgeCount 12)) :=
  [missing30784]
abbrev records30784_30785 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30784]
theorem aligned30784_30785 :
    AlignedValid 12 4 missing30784_30785 records30784_30785 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30784
    maskCheck30784 AlignedValid.nil

def missing30785_30786 : List (BitVec (edgeCount 12)) :=
  [missing30785]
abbrev records30785_30786 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30785]
theorem aligned30785_30786 :
    AlignedValid 12 4 missing30785_30786 records30785_30786 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30785
    maskCheck30785 AlignedValid.nil

def missing30784_30786 : List (BitVec (edgeCount 12)) :=
  missing30784_30785 ++ missing30785_30786
abbrev records30784_30786 : List Blob :=
  records30784_30785 ++ records30785_30786
theorem aligned30784_30786 :
    AlignedValid 12 4 missing30784_30786 records30784_30786 :=
  aligned30784_30785.append aligned30785_30786

def missing30786_30787 : List (BitVec (edgeCount 12)) :=
  [missing30786]
abbrev records30786_30787 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30786]
theorem aligned30786_30787 :
    AlignedValid 12 4 missing30786_30787 records30786_30787 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30786
    maskCheck30786 AlignedValid.nil

def missing30787_30788 : List (BitVec (edgeCount 12)) :=
  [missing30787]
abbrev records30787_30788 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30787]
theorem aligned30787_30788 :
    AlignedValid 12 4 missing30787_30788 records30787_30788 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30787
    maskCheck30787 AlignedValid.nil

def missing30786_30788 : List (BitVec (edgeCount 12)) :=
  missing30786_30787 ++ missing30787_30788
abbrev records30786_30788 : List Blob :=
  records30786_30787 ++ records30787_30788
theorem aligned30786_30788 :
    AlignedValid 12 4 missing30786_30788 records30786_30788 :=
  aligned30786_30787.append aligned30787_30788

def missing30784_30788 : List (BitVec (edgeCount 12)) :=
  missing30784_30786 ++ missing30786_30788
abbrev records30784_30788 : List Blob :=
  records30784_30786 ++ records30786_30788
theorem aligned30784_30788 :
    AlignedValid 12 4 missing30784_30788 records30784_30788 :=
  aligned30784_30786.append aligned30786_30788

def missing30788_30789 : List (BitVec (edgeCount 12)) :=
  [missing30788]
abbrev records30788_30789 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30788]
theorem aligned30788_30789 :
    AlignedValid 12 4 missing30788_30789 records30788_30789 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30788
    maskCheck30788 AlignedValid.nil

def missing30789_30790 : List (BitVec (edgeCount 12)) :=
  [missing30789]
abbrev records30789_30790 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30789]
theorem aligned30789_30790 :
    AlignedValid 12 4 missing30789_30790 records30789_30790 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30789
    maskCheck30789 AlignedValid.nil

def missing30788_30790 : List (BitVec (edgeCount 12)) :=
  missing30788_30789 ++ missing30789_30790
abbrev records30788_30790 : List Blob :=
  records30788_30789 ++ records30789_30790
theorem aligned30788_30790 :
    AlignedValid 12 4 missing30788_30790 records30788_30790 :=
  aligned30788_30789.append aligned30789_30790

def missing30790_30791 : List (BitVec (edgeCount 12)) :=
  [missing30790]
abbrev records30790_30791 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30790]
theorem aligned30790_30791 :
    AlignedValid 12 4 missing30790_30791 records30790_30791 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30790
    maskCheck30790 AlignedValid.nil

def missing30791_30792 : List (BitVec (edgeCount 12)) :=
  [missing30791]
abbrev records30791_30792 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30791]
theorem aligned30791_30792 :
    AlignedValid 12 4 missing30791_30792 records30791_30792 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30791
    maskCheck30791 AlignedValid.nil

def missing30790_30792 : List (BitVec (edgeCount 12)) :=
  missing30790_30791 ++ missing30791_30792
abbrev records30790_30792 : List Blob :=
  records30790_30791 ++ records30791_30792
theorem aligned30790_30792 :
    AlignedValid 12 4 missing30790_30792 records30790_30792 :=
  aligned30790_30791.append aligned30791_30792

def missing30788_30792 : List (BitVec (edgeCount 12)) :=
  missing30788_30790 ++ missing30790_30792
abbrev records30788_30792 : List Blob :=
  records30788_30790 ++ records30790_30792
theorem aligned30788_30792 :
    AlignedValid 12 4 missing30788_30792 records30788_30792 :=
  aligned30788_30790.append aligned30790_30792

def missing30784_30792 : List (BitVec (edgeCount 12)) :=
  missing30784_30788 ++ missing30788_30792
abbrev records30784_30792 : List Blob :=
  records30784_30788 ++ records30788_30792
theorem aligned30784_30792 :
    AlignedValid 12 4 missing30784_30792 records30784_30792 :=
  aligned30784_30788.append aligned30788_30792

def missing30792_30793 : List (BitVec (edgeCount 12)) :=
  [missing30792]
abbrev records30792_30793 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30792]
theorem aligned30792_30793 :
    AlignedValid 12 4 missing30792_30793 records30792_30793 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30792
    maskCheck30792 AlignedValid.nil

def missing30793_30794 : List (BitVec (edgeCount 12)) :=
  [missing30793]
abbrev records30793_30794 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30793]
theorem aligned30793_30794 :
    AlignedValid 12 4 missing30793_30794 records30793_30794 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30793
    maskCheck30793 AlignedValid.nil

def missing30792_30794 : List (BitVec (edgeCount 12)) :=
  missing30792_30793 ++ missing30793_30794
abbrev records30792_30794 : List Blob :=
  records30792_30793 ++ records30793_30794
theorem aligned30792_30794 :
    AlignedValid 12 4 missing30792_30794 records30792_30794 :=
  aligned30792_30793.append aligned30793_30794

def missing30794_30795 : List (BitVec (edgeCount 12)) :=
  [missing30794]
abbrev records30794_30795 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30794]
theorem aligned30794_30795 :
    AlignedValid 12 4 missing30794_30795 records30794_30795 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30794
    maskCheck30794 AlignedValid.nil

def missing30795_30796 : List (BitVec (edgeCount 12)) :=
  [missing30795]
abbrev records30795_30796 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30795]
theorem aligned30795_30796 :
    AlignedValid 12 4 missing30795_30796 records30795_30796 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30795
    maskCheck30795 AlignedValid.nil

def missing30794_30796 : List (BitVec (edgeCount 12)) :=
  missing30794_30795 ++ missing30795_30796
abbrev records30794_30796 : List Blob :=
  records30794_30795 ++ records30795_30796
theorem aligned30794_30796 :
    AlignedValid 12 4 missing30794_30796 records30794_30796 :=
  aligned30794_30795.append aligned30795_30796

def missing30792_30796 : List (BitVec (edgeCount 12)) :=
  missing30792_30794 ++ missing30794_30796
abbrev records30792_30796 : List Blob :=
  records30792_30794 ++ records30794_30796
theorem aligned30792_30796 :
    AlignedValid 12 4 missing30792_30796 records30792_30796 :=
  aligned30792_30794.append aligned30794_30796

def missing30796_30797 : List (BitVec (edgeCount 12)) :=
  [missing30796]
abbrev records30796_30797 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30796]
theorem aligned30796_30797 :
    AlignedValid 12 4 missing30796_30797 records30796_30797 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30796
    maskCheck30796 AlignedValid.nil

def missing30797_30798 : List (BitVec (edgeCount 12)) :=
  [missing30797]
abbrev records30797_30798 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30797]
theorem aligned30797_30798 :
    AlignedValid 12 4 missing30797_30798 records30797_30798 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30797
    maskCheck30797 AlignedValid.nil

def missing30796_30798 : List (BitVec (edgeCount 12)) :=
  missing30796_30797 ++ missing30797_30798
abbrev records30796_30798 : List Blob :=
  records30796_30797 ++ records30797_30798
theorem aligned30796_30798 :
    AlignedValid 12 4 missing30796_30798 records30796_30798 :=
  aligned30796_30797.append aligned30797_30798

def missing30798_30799 : List (BitVec (edgeCount 12)) :=
  [missing30798]
abbrev records30798_30799 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30798]
theorem aligned30798_30799 :
    AlignedValid 12 4 missing30798_30799 records30798_30799 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30798
    maskCheck30798 AlignedValid.nil

def missing30799_30800 : List (BitVec (edgeCount 12)) :=
  [missing30799]
abbrev records30799_30800 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30799]
theorem aligned30799_30800 :
    AlignedValid 12 4 missing30799_30800 records30799_30800 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30799
    maskCheck30799 AlignedValid.nil

def missing30798_30800 : List (BitVec (edgeCount 12)) :=
  missing30798_30799 ++ missing30799_30800
abbrev records30798_30800 : List Blob :=
  records30798_30799 ++ records30799_30800
theorem aligned30798_30800 :
    AlignedValid 12 4 missing30798_30800 records30798_30800 :=
  aligned30798_30799.append aligned30799_30800

def missing30796_30800 : List (BitVec (edgeCount 12)) :=
  missing30796_30798 ++ missing30798_30800
abbrev records30796_30800 : List Blob :=
  records30796_30798 ++ records30798_30800
theorem aligned30796_30800 :
    AlignedValid 12 4 missing30796_30800 records30796_30800 :=
  aligned30796_30798.append aligned30798_30800

def missing30792_30800 : List (BitVec (edgeCount 12)) :=
  missing30792_30796 ++ missing30796_30800
abbrev records30792_30800 : List Blob :=
  records30792_30796 ++ records30796_30800
theorem aligned30792_30800 :
    AlignedValid 12 4 missing30792_30800 records30792_30800 :=
  aligned30792_30796.append aligned30796_30800

def missing30784_30800 : List (BitVec (edgeCount 12)) :=
  missing30784_30792 ++ missing30792_30800
abbrev records30784_30800 : List Blob :=
  records30784_30792 ++ records30792_30800
theorem aligned30784_30800 :
    AlignedValid 12 4 missing30784_30800 records30784_30800 :=
  aligned30784_30792.append aligned30792_30800

def missing30800_30801 : List (BitVec (edgeCount 12)) :=
  [missing30800]
abbrev records30800_30801 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30800]
theorem aligned30800_30801 :
    AlignedValid 12 4 missing30800_30801 records30800_30801 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30800
    maskCheck30800 AlignedValid.nil

def missing30801_30802 : List (BitVec (edgeCount 12)) :=
  [missing30801]
abbrev records30801_30802 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30801]
theorem aligned30801_30802 :
    AlignedValid 12 4 missing30801_30802 records30801_30802 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30801
    maskCheck30801 AlignedValid.nil

def missing30800_30802 : List (BitVec (edgeCount 12)) :=
  missing30800_30801 ++ missing30801_30802
abbrev records30800_30802 : List Blob :=
  records30800_30801 ++ records30801_30802
theorem aligned30800_30802 :
    AlignedValid 12 4 missing30800_30802 records30800_30802 :=
  aligned30800_30801.append aligned30801_30802

def missing30802_30803 : List (BitVec (edgeCount 12)) :=
  [missing30802]
abbrev records30802_30803 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30802]
theorem aligned30802_30803 :
    AlignedValid 12 4 missing30802_30803 records30802_30803 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30802
    maskCheck30802 AlignedValid.nil

def missing30803_30804 : List (BitVec (edgeCount 12)) :=
  [missing30803]
abbrev records30803_30804 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30803]
theorem aligned30803_30804 :
    AlignedValid 12 4 missing30803_30804 records30803_30804 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30803
    maskCheck30803 AlignedValid.nil

def missing30802_30804 : List (BitVec (edgeCount 12)) :=
  missing30802_30803 ++ missing30803_30804
abbrev records30802_30804 : List Blob :=
  records30802_30803 ++ records30803_30804
theorem aligned30802_30804 :
    AlignedValid 12 4 missing30802_30804 records30802_30804 :=
  aligned30802_30803.append aligned30803_30804

def missing30800_30804 : List (BitVec (edgeCount 12)) :=
  missing30800_30802 ++ missing30802_30804
abbrev records30800_30804 : List Blob :=
  records30800_30802 ++ records30802_30804
theorem aligned30800_30804 :
    AlignedValid 12 4 missing30800_30804 records30800_30804 :=
  aligned30800_30802.append aligned30802_30804

def missing30804_30805 : List (BitVec (edgeCount 12)) :=
  [missing30804]
abbrev records30804_30805 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30804]
theorem aligned30804_30805 :
    AlignedValid 12 4 missing30804_30805 records30804_30805 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30804
    maskCheck30804 AlignedValid.nil

def missing30805_30806 : List (BitVec (edgeCount 12)) :=
  [missing30805]
abbrev records30805_30806 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30805]
theorem aligned30805_30806 :
    AlignedValid 12 4 missing30805_30806 records30805_30806 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30805
    maskCheck30805 AlignedValid.nil

def missing30804_30806 : List (BitVec (edgeCount 12)) :=
  missing30804_30805 ++ missing30805_30806
abbrev records30804_30806 : List Blob :=
  records30804_30805 ++ records30805_30806
theorem aligned30804_30806 :
    AlignedValid 12 4 missing30804_30806 records30804_30806 :=
  aligned30804_30805.append aligned30805_30806

def missing30806_30807 : List (BitVec (edgeCount 12)) :=
  [missing30806]
abbrev records30806_30807 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30806]
theorem aligned30806_30807 :
    AlignedValid 12 4 missing30806_30807 records30806_30807 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30806
    maskCheck30806 AlignedValid.nil

def missing30807_30808 : List (BitVec (edgeCount 12)) :=
  [missing30807]
abbrev records30807_30808 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30807]
theorem aligned30807_30808 :
    AlignedValid 12 4 missing30807_30808 records30807_30808 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30807
    maskCheck30807 AlignedValid.nil

def missing30806_30808 : List (BitVec (edgeCount 12)) :=
  missing30806_30807 ++ missing30807_30808
abbrev records30806_30808 : List Blob :=
  records30806_30807 ++ records30807_30808
theorem aligned30806_30808 :
    AlignedValid 12 4 missing30806_30808 records30806_30808 :=
  aligned30806_30807.append aligned30807_30808

def missing30804_30808 : List (BitVec (edgeCount 12)) :=
  missing30804_30806 ++ missing30806_30808
abbrev records30804_30808 : List Blob :=
  records30804_30806 ++ records30806_30808
theorem aligned30804_30808 :
    AlignedValid 12 4 missing30804_30808 records30804_30808 :=
  aligned30804_30806.append aligned30806_30808

def missing30800_30808 : List (BitVec (edgeCount 12)) :=
  missing30800_30804 ++ missing30804_30808
abbrev records30800_30808 : List Blob :=
  records30800_30804 ++ records30804_30808
theorem aligned30800_30808 :
    AlignedValid 12 4 missing30800_30808 records30800_30808 :=
  aligned30800_30804.append aligned30804_30808

def missing30808_30809 : List (BitVec (edgeCount 12)) :=
  [missing30808]
abbrev records30808_30809 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30808]
theorem aligned30808_30809 :
    AlignedValid 12 4 missing30808_30809 records30808_30809 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30808
    maskCheck30808 AlignedValid.nil

def missing30809_30810 : List (BitVec (edgeCount 12)) :=
  [missing30809]
abbrev records30809_30810 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30809]
theorem aligned30809_30810 :
    AlignedValid 12 4 missing30809_30810 records30809_30810 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30809
    maskCheck30809 AlignedValid.nil

def missing30808_30810 : List (BitVec (edgeCount 12)) :=
  missing30808_30809 ++ missing30809_30810
abbrev records30808_30810 : List Blob :=
  records30808_30809 ++ records30809_30810
theorem aligned30808_30810 :
    AlignedValid 12 4 missing30808_30810 records30808_30810 :=
  aligned30808_30809.append aligned30809_30810

def missing30810_30811 : List (BitVec (edgeCount 12)) :=
  [missing30810]
abbrev records30810_30811 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30810]
theorem aligned30810_30811 :
    AlignedValid 12 4 missing30810_30811 records30810_30811 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30810
    maskCheck30810 AlignedValid.nil

def missing30811_30812 : List (BitVec (edgeCount 12)) :=
  [missing30811]
abbrev records30811_30812 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30811]
theorem aligned30811_30812 :
    AlignedValid 12 4 missing30811_30812 records30811_30812 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30811
    maskCheck30811 AlignedValid.nil

def missing30810_30812 : List (BitVec (edgeCount 12)) :=
  missing30810_30811 ++ missing30811_30812
abbrev records30810_30812 : List Blob :=
  records30810_30811 ++ records30811_30812
theorem aligned30810_30812 :
    AlignedValid 12 4 missing30810_30812 records30810_30812 :=
  aligned30810_30811.append aligned30811_30812

def missing30808_30812 : List (BitVec (edgeCount 12)) :=
  missing30808_30810 ++ missing30810_30812
abbrev records30808_30812 : List Blob :=
  records30808_30810 ++ records30810_30812
theorem aligned30808_30812 :
    AlignedValid 12 4 missing30808_30812 records30808_30812 :=
  aligned30808_30810.append aligned30810_30812

def missing30812_30813 : List (BitVec (edgeCount 12)) :=
  [missing30812]
abbrev records30812_30813 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30812]
theorem aligned30812_30813 :
    AlignedValid 12 4 missing30812_30813 records30812_30813 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30812
    maskCheck30812 AlignedValid.nil

def missing30813_30814 : List (BitVec (edgeCount 12)) :=
  [missing30813]
abbrev records30813_30814 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30813]
theorem aligned30813_30814 :
    AlignedValid 12 4 missing30813_30814 records30813_30814 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30813
    maskCheck30813 AlignedValid.nil

def missing30812_30814 : List (BitVec (edgeCount 12)) :=
  missing30812_30813 ++ missing30813_30814
abbrev records30812_30814 : List Blob :=
  records30812_30813 ++ records30813_30814
theorem aligned30812_30814 :
    AlignedValid 12 4 missing30812_30814 records30812_30814 :=
  aligned30812_30813.append aligned30813_30814

def missing30814_30815 : List (BitVec (edgeCount 12)) :=
  [missing30814]
abbrev records30814_30815 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30814]
theorem aligned30814_30815 :
    AlignedValid 12 4 missing30814_30815 records30814_30815 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30814
    maskCheck30814 AlignedValid.nil

def missing30815_30816 : List (BitVec (edgeCount 12)) :=
  [missing30815]
abbrev records30815_30816 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30815]
theorem aligned30815_30816 :
    AlignedValid 12 4 missing30815_30816 records30815_30816 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30815
    maskCheck30815 AlignedValid.nil

def missing30814_30816 : List (BitVec (edgeCount 12)) :=
  missing30814_30815 ++ missing30815_30816
abbrev records30814_30816 : List Blob :=
  records30814_30815 ++ records30815_30816
theorem aligned30814_30816 :
    AlignedValid 12 4 missing30814_30816 records30814_30816 :=
  aligned30814_30815.append aligned30815_30816

def missing30812_30816 : List (BitVec (edgeCount 12)) :=
  missing30812_30814 ++ missing30814_30816
abbrev records30812_30816 : List Blob :=
  records30812_30814 ++ records30814_30816
theorem aligned30812_30816 :
    AlignedValid 12 4 missing30812_30816 records30812_30816 :=
  aligned30812_30814.append aligned30814_30816

def missing30808_30816 : List (BitVec (edgeCount 12)) :=
  missing30808_30812 ++ missing30812_30816
abbrev records30808_30816 : List Blob :=
  records30808_30812 ++ records30812_30816
theorem aligned30808_30816 :
    AlignedValid 12 4 missing30808_30816 records30808_30816 :=
  aligned30808_30812.append aligned30812_30816

def missing30800_30816 : List (BitVec (edgeCount 12)) :=
  missing30800_30808 ++ missing30808_30816
abbrev records30800_30816 : List Blob :=
  records30800_30808 ++ records30808_30816
theorem aligned30800_30816 :
    AlignedValid 12 4 missing30800_30816 records30800_30816 :=
  aligned30800_30808.append aligned30808_30816

def missing30784_30816 : List (BitVec (edgeCount 12)) :=
  missing30784_30800 ++ missing30800_30816
abbrev records30784_30816 : List Blob :=
  records30784_30800 ++ records30800_30816
theorem aligned30784_30816 :
    AlignedValid 12 4 missing30784_30816 records30784_30816 :=
  aligned30784_30800.append aligned30800_30816

def missing30816_30817 : List (BitVec (edgeCount 12)) :=
  [missing30816]
abbrev records30816_30817 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30816]
theorem aligned30816_30817 :
    AlignedValid 12 4 missing30816_30817 records30816_30817 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30816
    maskCheck30816 AlignedValid.nil

def missing30817_30818 : List (BitVec (edgeCount 12)) :=
  [missing30817]
abbrev records30817_30818 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30817]
theorem aligned30817_30818 :
    AlignedValid 12 4 missing30817_30818 records30817_30818 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30817
    maskCheck30817 AlignedValid.nil

def missing30816_30818 : List (BitVec (edgeCount 12)) :=
  missing30816_30817 ++ missing30817_30818
abbrev records30816_30818 : List Blob :=
  records30816_30817 ++ records30817_30818
theorem aligned30816_30818 :
    AlignedValid 12 4 missing30816_30818 records30816_30818 :=
  aligned30816_30817.append aligned30817_30818

def missing30818_30819 : List (BitVec (edgeCount 12)) :=
  [missing30818]
abbrev records30818_30819 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30818]
theorem aligned30818_30819 :
    AlignedValid 12 4 missing30818_30819 records30818_30819 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30818
    maskCheck30818 AlignedValid.nil

def missing30819_30820 : List (BitVec (edgeCount 12)) :=
  [missing30819]
abbrev records30819_30820 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30819]
theorem aligned30819_30820 :
    AlignedValid 12 4 missing30819_30820 records30819_30820 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30819
    maskCheck30819 AlignedValid.nil

def missing30818_30820 : List (BitVec (edgeCount 12)) :=
  missing30818_30819 ++ missing30819_30820
abbrev records30818_30820 : List Blob :=
  records30818_30819 ++ records30819_30820
theorem aligned30818_30820 :
    AlignedValid 12 4 missing30818_30820 records30818_30820 :=
  aligned30818_30819.append aligned30819_30820

def missing30816_30820 : List (BitVec (edgeCount 12)) :=
  missing30816_30818 ++ missing30818_30820
abbrev records30816_30820 : List Blob :=
  records30816_30818 ++ records30818_30820
theorem aligned30816_30820 :
    AlignedValid 12 4 missing30816_30820 records30816_30820 :=
  aligned30816_30818.append aligned30818_30820

def missing30820_30821 : List (BitVec (edgeCount 12)) :=
  [missing30820]
abbrev records30820_30821 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30820]
theorem aligned30820_30821 :
    AlignedValid 12 4 missing30820_30821 records30820_30821 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30820
    maskCheck30820 AlignedValid.nil

def missing30821_30822 : List (BitVec (edgeCount 12)) :=
  [missing30821]
abbrev records30821_30822 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30821]
theorem aligned30821_30822 :
    AlignedValid 12 4 missing30821_30822 records30821_30822 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30821
    maskCheck30821 AlignedValid.nil

def missing30820_30822 : List (BitVec (edgeCount 12)) :=
  missing30820_30821 ++ missing30821_30822
abbrev records30820_30822 : List Blob :=
  records30820_30821 ++ records30821_30822
theorem aligned30820_30822 :
    AlignedValid 12 4 missing30820_30822 records30820_30822 :=
  aligned30820_30821.append aligned30821_30822

def missing30822_30823 : List (BitVec (edgeCount 12)) :=
  [missing30822]
abbrev records30822_30823 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30822]
theorem aligned30822_30823 :
    AlignedValid 12 4 missing30822_30823 records30822_30823 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30822
    maskCheck30822 AlignedValid.nil

def missing30823_30824 : List (BitVec (edgeCount 12)) :=
  [missing30823]
abbrev records30823_30824 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30823]
theorem aligned30823_30824 :
    AlignedValid 12 4 missing30823_30824 records30823_30824 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30823
    maskCheck30823 AlignedValid.nil

def missing30822_30824 : List (BitVec (edgeCount 12)) :=
  missing30822_30823 ++ missing30823_30824
abbrev records30822_30824 : List Blob :=
  records30822_30823 ++ records30823_30824
theorem aligned30822_30824 :
    AlignedValid 12 4 missing30822_30824 records30822_30824 :=
  aligned30822_30823.append aligned30823_30824

def missing30820_30824 : List (BitVec (edgeCount 12)) :=
  missing30820_30822 ++ missing30822_30824
abbrev records30820_30824 : List Blob :=
  records30820_30822 ++ records30822_30824
theorem aligned30820_30824 :
    AlignedValid 12 4 missing30820_30824 records30820_30824 :=
  aligned30820_30822.append aligned30822_30824

def missing30816_30824 : List (BitVec (edgeCount 12)) :=
  missing30816_30820 ++ missing30820_30824
abbrev records30816_30824 : List Blob :=
  records30816_30820 ++ records30820_30824
theorem aligned30816_30824 :
    AlignedValid 12 4 missing30816_30824 records30816_30824 :=
  aligned30816_30820.append aligned30820_30824

def missing30824_30825 : List (BitVec (edgeCount 12)) :=
  [missing30824]
abbrev records30824_30825 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30824]
theorem aligned30824_30825 :
    AlignedValid 12 4 missing30824_30825 records30824_30825 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30824
    maskCheck30824 AlignedValid.nil

def missing30825_30826 : List (BitVec (edgeCount 12)) :=
  [missing30825]
abbrev records30825_30826 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30825]
theorem aligned30825_30826 :
    AlignedValid 12 4 missing30825_30826 records30825_30826 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30825
    maskCheck30825 AlignedValid.nil

def missing30824_30826 : List (BitVec (edgeCount 12)) :=
  missing30824_30825 ++ missing30825_30826
abbrev records30824_30826 : List Blob :=
  records30824_30825 ++ records30825_30826
theorem aligned30824_30826 :
    AlignedValid 12 4 missing30824_30826 records30824_30826 :=
  aligned30824_30825.append aligned30825_30826

def missing30826_30827 : List (BitVec (edgeCount 12)) :=
  [missing30826]
abbrev records30826_30827 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30826]
theorem aligned30826_30827 :
    AlignedValid 12 4 missing30826_30827 records30826_30827 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30826
    maskCheck30826 AlignedValid.nil

def missing30827_30828 : List (BitVec (edgeCount 12)) :=
  [missing30827]
abbrev records30827_30828 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30827]
theorem aligned30827_30828 :
    AlignedValid 12 4 missing30827_30828 records30827_30828 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30827
    maskCheck30827 AlignedValid.nil

def missing30826_30828 : List (BitVec (edgeCount 12)) :=
  missing30826_30827 ++ missing30827_30828
abbrev records30826_30828 : List Blob :=
  records30826_30827 ++ records30827_30828
theorem aligned30826_30828 :
    AlignedValid 12 4 missing30826_30828 records30826_30828 :=
  aligned30826_30827.append aligned30827_30828

def missing30824_30828 : List (BitVec (edgeCount 12)) :=
  missing30824_30826 ++ missing30826_30828
abbrev records30824_30828 : List Blob :=
  records30824_30826 ++ records30826_30828
theorem aligned30824_30828 :
    AlignedValid 12 4 missing30824_30828 records30824_30828 :=
  aligned30824_30826.append aligned30826_30828

def missing30828_30829 : List (BitVec (edgeCount 12)) :=
  [missing30828]
abbrev records30828_30829 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30828]
theorem aligned30828_30829 :
    AlignedValid 12 4 missing30828_30829 records30828_30829 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30828
    maskCheck30828 AlignedValid.nil

def missing30829_30830 : List (BitVec (edgeCount 12)) :=
  [missing30829]
abbrev records30829_30830 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30829]
theorem aligned30829_30830 :
    AlignedValid 12 4 missing30829_30830 records30829_30830 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30829
    maskCheck30829 AlignedValid.nil

def missing30828_30830 : List (BitVec (edgeCount 12)) :=
  missing30828_30829 ++ missing30829_30830
abbrev records30828_30830 : List Blob :=
  records30828_30829 ++ records30829_30830
theorem aligned30828_30830 :
    AlignedValid 12 4 missing30828_30830 records30828_30830 :=
  aligned30828_30829.append aligned30829_30830

def missing30830_30831 : List (BitVec (edgeCount 12)) :=
  [missing30830]
abbrev records30830_30831 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30830]
theorem aligned30830_30831 :
    AlignedValid 12 4 missing30830_30831 records30830_30831 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30830
    maskCheck30830 AlignedValid.nil

def missing30831_30832 : List (BitVec (edgeCount 12)) :=
  [missing30831]
abbrev records30831_30832 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30831]
theorem aligned30831_30832 :
    AlignedValid 12 4 missing30831_30832 records30831_30832 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30831
    maskCheck30831 AlignedValid.nil

def missing30830_30832 : List (BitVec (edgeCount 12)) :=
  missing30830_30831 ++ missing30831_30832
abbrev records30830_30832 : List Blob :=
  records30830_30831 ++ records30831_30832
theorem aligned30830_30832 :
    AlignedValid 12 4 missing30830_30832 records30830_30832 :=
  aligned30830_30831.append aligned30831_30832

def missing30828_30832 : List (BitVec (edgeCount 12)) :=
  missing30828_30830 ++ missing30830_30832
abbrev records30828_30832 : List Blob :=
  records30828_30830 ++ records30830_30832
theorem aligned30828_30832 :
    AlignedValid 12 4 missing30828_30832 records30828_30832 :=
  aligned30828_30830.append aligned30830_30832

def missing30824_30832 : List (BitVec (edgeCount 12)) :=
  missing30824_30828 ++ missing30828_30832
abbrev records30824_30832 : List Blob :=
  records30824_30828 ++ records30828_30832
theorem aligned30824_30832 :
    AlignedValid 12 4 missing30824_30832 records30824_30832 :=
  aligned30824_30828.append aligned30828_30832

def missing30816_30832 : List (BitVec (edgeCount 12)) :=
  missing30816_30824 ++ missing30824_30832
abbrev records30816_30832 : List Blob :=
  records30816_30824 ++ records30824_30832
theorem aligned30816_30832 :
    AlignedValid 12 4 missing30816_30832 records30816_30832 :=
  aligned30816_30824.append aligned30824_30832

def missing30832_30833 : List (BitVec (edgeCount 12)) :=
  [missing30832]
abbrev records30832_30833 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30832]
theorem aligned30832_30833 :
    AlignedValid 12 4 missing30832_30833 records30832_30833 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30832
    maskCheck30832 AlignedValid.nil

def missing30833_30834 : List (BitVec (edgeCount 12)) :=
  [missing30833]
abbrev records30833_30834 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30833]
theorem aligned30833_30834 :
    AlignedValid 12 4 missing30833_30834 records30833_30834 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30833
    maskCheck30833 AlignedValid.nil

def missing30832_30834 : List (BitVec (edgeCount 12)) :=
  missing30832_30833 ++ missing30833_30834
abbrev records30832_30834 : List Blob :=
  records30832_30833 ++ records30833_30834
theorem aligned30832_30834 :
    AlignedValid 12 4 missing30832_30834 records30832_30834 :=
  aligned30832_30833.append aligned30833_30834

def missing30834_30835 : List (BitVec (edgeCount 12)) :=
  [missing30834]
abbrev records30834_30835 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30834]
theorem aligned30834_30835 :
    AlignedValid 12 4 missing30834_30835 records30834_30835 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30834
    maskCheck30834 AlignedValid.nil

def missing30835_30836 : List (BitVec (edgeCount 12)) :=
  [missing30835]
abbrev records30835_30836 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30835]
theorem aligned30835_30836 :
    AlignedValid 12 4 missing30835_30836 records30835_30836 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30835
    maskCheck30835 AlignedValid.nil

def missing30834_30836 : List (BitVec (edgeCount 12)) :=
  missing30834_30835 ++ missing30835_30836
abbrev records30834_30836 : List Blob :=
  records30834_30835 ++ records30835_30836
theorem aligned30834_30836 :
    AlignedValid 12 4 missing30834_30836 records30834_30836 :=
  aligned30834_30835.append aligned30835_30836

def missing30832_30836 : List (BitVec (edgeCount 12)) :=
  missing30832_30834 ++ missing30834_30836
abbrev records30832_30836 : List Blob :=
  records30832_30834 ++ records30834_30836
theorem aligned30832_30836 :
    AlignedValid 12 4 missing30832_30836 records30832_30836 :=
  aligned30832_30834.append aligned30834_30836

def missing30836_30837 : List (BitVec (edgeCount 12)) :=
  [missing30836]
abbrev records30836_30837 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30836]
theorem aligned30836_30837 :
    AlignedValid 12 4 missing30836_30837 records30836_30837 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30836
    maskCheck30836 AlignedValid.nil

def missing30837_30838 : List (BitVec (edgeCount 12)) :=
  [missing30837]
abbrev records30837_30838 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30837]
theorem aligned30837_30838 :
    AlignedValid 12 4 missing30837_30838 records30837_30838 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30837
    maskCheck30837 AlignedValid.nil

def missing30836_30838 : List (BitVec (edgeCount 12)) :=
  missing30836_30837 ++ missing30837_30838
abbrev records30836_30838 : List Blob :=
  records30836_30837 ++ records30837_30838
theorem aligned30836_30838 :
    AlignedValid 12 4 missing30836_30838 records30836_30838 :=
  aligned30836_30837.append aligned30837_30838

def missing30838_30839 : List (BitVec (edgeCount 12)) :=
  [missing30838]
abbrev records30838_30839 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30838]
theorem aligned30838_30839 :
    AlignedValid 12 4 missing30838_30839 records30838_30839 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30838
    maskCheck30838 AlignedValid.nil

def missing30839_30840 : List (BitVec (edgeCount 12)) :=
  [missing30839]
abbrev records30839_30840 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30839]
theorem aligned30839_30840 :
    AlignedValid 12 4 missing30839_30840 records30839_30840 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30839
    maskCheck30839 AlignedValid.nil

def missing30838_30840 : List (BitVec (edgeCount 12)) :=
  missing30838_30839 ++ missing30839_30840
abbrev records30838_30840 : List Blob :=
  records30838_30839 ++ records30839_30840
theorem aligned30838_30840 :
    AlignedValid 12 4 missing30838_30840 records30838_30840 :=
  aligned30838_30839.append aligned30839_30840

def missing30836_30840 : List (BitVec (edgeCount 12)) :=
  missing30836_30838 ++ missing30838_30840
abbrev records30836_30840 : List Blob :=
  records30836_30838 ++ records30838_30840
theorem aligned30836_30840 :
    AlignedValid 12 4 missing30836_30840 records30836_30840 :=
  aligned30836_30838.append aligned30838_30840

def missing30832_30840 : List (BitVec (edgeCount 12)) :=
  missing30832_30836 ++ missing30836_30840
abbrev records30832_30840 : List Blob :=
  records30832_30836 ++ records30836_30840
theorem aligned30832_30840 :
    AlignedValid 12 4 missing30832_30840 records30832_30840 :=
  aligned30832_30836.append aligned30836_30840

def missing30840_30841 : List (BitVec (edgeCount 12)) :=
  [missing30840]
abbrev records30840_30841 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30840]
theorem aligned30840_30841 :
    AlignedValid 12 4 missing30840_30841 records30840_30841 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30840
    maskCheck30840 AlignedValid.nil

def missing30841_30842 : List (BitVec (edgeCount 12)) :=
  [missing30841]
abbrev records30841_30842 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30841]
theorem aligned30841_30842 :
    AlignedValid 12 4 missing30841_30842 records30841_30842 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30841
    maskCheck30841 AlignedValid.nil

def missing30840_30842 : List (BitVec (edgeCount 12)) :=
  missing30840_30841 ++ missing30841_30842
abbrev records30840_30842 : List Blob :=
  records30840_30841 ++ records30841_30842
theorem aligned30840_30842 :
    AlignedValid 12 4 missing30840_30842 records30840_30842 :=
  aligned30840_30841.append aligned30841_30842

def missing30842_30843 : List (BitVec (edgeCount 12)) :=
  [missing30842]
abbrev records30842_30843 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30842]
theorem aligned30842_30843 :
    AlignedValid 12 4 missing30842_30843 records30842_30843 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30842
    maskCheck30842 AlignedValid.nil

def missing30843_30844 : List (BitVec (edgeCount 12)) :=
  [missing30843]
abbrev records30843_30844 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30843]
theorem aligned30843_30844 :
    AlignedValid 12 4 missing30843_30844 records30843_30844 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30843
    maskCheck30843 AlignedValid.nil

def missing30842_30844 : List (BitVec (edgeCount 12)) :=
  missing30842_30843 ++ missing30843_30844
abbrev records30842_30844 : List Blob :=
  records30842_30843 ++ records30843_30844
theorem aligned30842_30844 :
    AlignedValid 12 4 missing30842_30844 records30842_30844 :=
  aligned30842_30843.append aligned30843_30844

def missing30840_30844 : List (BitVec (edgeCount 12)) :=
  missing30840_30842 ++ missing30842_30844
abbrev records30840_30844 : List Blob :=
  records30840_30842 ++ records30842_30844
theorem aligned30840_30844 :
    AlignedValid 12 4 missing30840_30844 records30840_30844 :=
  aligned30840_30842.append aligned30842_30844

def missing30844_30845 : List (BitVec (edgeCount 12)) :=
  [missing30844]
abbrev records30844_30845 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30844]
theorem aligned30844_30845 :
    AlignedValid 12 4 missing30844_30845 records30844_30845 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30844
    maskCheck30844 AlignedValid.nil

def missing30845_30846 : List (BitVec (edgeCount 12)) :=
  [missing30845]
abbrev records30845_30846 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30845]
theorem aligned30845_30846 :
    AlignedValid 12 4 missing30845_30846 records30845_30846 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30845
    maskCheck30845 AlignedValid.nil

def missing30844_30846 : List (BitVec (edgeCount 12)) :=
  missing30844_30845 ++ missing30845_30846
abbrev records30844_30846 : List Blob :=
  records30844_30845 ++ records30845_30846
theorem aligned30844_30846 :
    AlignedValid 12 4 missing30844_30846 records30844_30846 :=
  aligned30844_30845.append aligned30845_30846

def missing30846_30847 : List (BitVec (edgeCount 12)) :=
  [missing30846]
abbrev records30846_30847 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30846]
theorem aligned30846_30847 :
    AlignedValid 12 4 missing30846_30847 records30846_30847 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30846
    maskCheck30846 AlignedValid.nil

def missing30847_30848 : List (BitVec (edgeCount 12)) :=
  [missing30847]
abbrev records30847_30848 : List Blob :=
  [StrongPackedBucketN12A4Shard240.record30847]
theorem aligned30847_30848 :
    AlignedValid 12 4 missing30847_30848 records30847_30848 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard240.check30847
    maskCheck30847 AlignedValid.nil

def missing30846_30848 : List (BitVec (edgeCount 12)) :=
  missing30846_30847 ++ missing30847_30848
abbrev records30846_30848 : List Blob :=
  records30846_30847 ++ records30847_30848
theorem aligned30846_30848 :
    AlignedValid 12 4 missing30846_30848 records30846_30848 :=
  aligned30846_30847.append aligned30847_30848

def missing30844_30848 : List (BitVec (edgeCount 12)) :=
  missing30844_30846 ++ missing30846_30848
abbrev records30844_30848 : List Blob :=
  records30844_30846 ++ records30846_30848
theorem aligned30844_30848 :
    AlignedValid 12 4 missing30844_30848 records30844_30848 :=
  aligned30844_30846.append aligned30846_30848

def missing30840_30848 : List (BitVec (edgeCount 12)) :=
  missing30840_30844 ++ missing30844_30848
abbrev records30840_30848 : List Blob :=
  records30840_30844 ++ records30844_30848
theorem aligned30840_30848 :
    AlignedValid 12 4 missing30840_30848 records30840_30848 :=
  aligned30840_30844.append aligned30844_30848

def missing30832_30848 : List (BitVec (edgeCount 12)) :=
  missing30832_30840 ++ missing30840_30848
abbrev records30832_30848 : List Blob :=
  records30832_30840 ++ records30840_30848
theorem aligned30832_30848 :
    AlignedValid 12 4 missing30832_30848 records30832_30848 :=
  aligned30832_30840.append aligned30840_30848

def missing30816_30848 : List (BitVec (edgeCount 12)) :=
  missing30816_30832 ++ missing30832_30848
abbrev records30816_30848 : List Blob :=
  records30816_30832 ++ records30832_30848
theorem aligned30816_30848 :
    AlignedValid 12 4 missing30816_30848 records30816_30848 :=
  aligned30816_30832.append aligned30832_30848

def missing30784_30848 : List (BitVec (edgeCount 12)) :=
  missing30784_30816 ++ missing30816_30848
abbrev records30784_30848 : List Blob :=
  records30784_30816 ++ records30816_30848
theorem aligned30784_30848 :
    AlignedValid 12 4 missing30784_30848 records30784_30848 :=
  aligned30784_30816.append aligned30816_30848

def missing30720_30848 : List (BitVec (edgeCount 12)) :=
  missing30720_30784 ++ missing30784_30848
abbrev records30720_30848 : List Blob :=
  records30720_30784 ++ records30784_30848
theorem aligned30720_30848 :
    AlignedValid 12 4 missing30720_30848 records30720_30848 :=
  aligned30720_30784.append aligned30784_30848

abbrev missing : List (BitVec (edgeCount 12)) := missing30720_30848
abbrev records : List Blob := records30720_30848
theorem aligned : AlignedValid 12 4 missing records := aligned30720_30848

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard240
