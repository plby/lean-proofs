/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard288

/-! Decode-only alignment checks for n=12, a=4, records 36864--36991. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard288

open PackedBucketCertificate

def missing36864 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1550400733709369344
theorem maskCheck36864 :
    checkMaskFor missing36864 StrongPackedBucketN12A4Shard288.record36864 = true := by
  decide

def missing36865 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1622458327747297280
theorem maskCheck36865 :
    checkMaskFor missing36865 StrongPackedBucketN12A4Shard288.record36865 = true := by
  decide

def missing36866 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1658487124766261248
theorem maskCheck36866 :
    checkMaskFor missing36866 StrongPackedBucketN12A4Shard288.record36866 = true := by
  decide

def missing36867 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2054803891974864896
theorem maskCheck36867 :
    checkMaskFor missing36867 StrongPackedBucketN12A4Shard288.record36867 = true := by
  decide

def missing36868 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2090832688993828864
theorem maskCheck36868 :
    checkMaskFor missing36868 StrongPackedBucketN12A4Shard288.record36868 = true := by
  decide

def missing36869 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2162890283031756800
theorem maskCheck36869 :
    checkMaskFor missing36869 StrongPackedBucketN12A4Shard288.record36869 = true := by
  decide

def missing36870 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2559207050240360448
theorem maskCheck36870 :
    checkMaskFor missing36870 StrongPackedBucketN12A4Shard288.record36870 = true := by
  decide

def missing36871 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2703322238316216320
theorem maskCheck36871 :
    checkMaskFor missing36871 StrongPackedBucketN12A4Shard288.record36871 = true := by
  decide

def missing36872 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2775379832354144256
theorem maskCheck36872 :
    checkMaskFor missing36872 StrongPackedBucketN12A4Shard288.record36872 = true := by
  decide

def missing36873 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3207725396581711872
theorem maskCheck36873 :
    checkMaskFor missing36873 StrongPackedBucketN12A4Shard288.record36873 = true := by
  decide

def missing36874 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3568013366771351552
theorem maskCheck36874 :
    checkMaskFor missing36874 StrongPackedBucketN12A4Shard288.record36874 = true := by
  decide

def missing36875 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3640070960809279488
theorem maskCheck36875 :
    checkMaskFor missing36875 StrongPackedBucketN12A4Shard288.record36875 = true := by
  decide

def missing36876 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3676099757828243456
theorem maskCheck36876 :
    checkMaskFor missing36876 StrongPackedBucketN12A4Shard288.record36876 = true := by
  decide

def missing36877 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3784186148885135360
theorem maskCheck36877 :
    checkMaskFor missing36877 StrongPackedBucketN12A4Shard288.record36877 = true := by
  decide

def missing36878 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3820214945904099328
theorem maskCheck36878 :
    checkMaskFor missing36878 StrongPackedBucketN12A4Shard288.record36878 = true := by
  decide

def missing36879 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3892272539942027264
theorem maskCheck36879 :
    checkMaskFor missing36879 StrongPackedBucketN12A4Shard288.record36879 = true := by
  decide

def missing36880 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4324618104169594880
theorem maskCheck36880 :
    checkMaskFor missing36880 StrongPackedBucketN12A4Shard288.record36880 = true := by
  decide

def missing36881 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4865050059454054400
theorem maskCheck36881 :
    checkMaskFor missing36881 StrongPackedBucketN12A4Shard288.record36881 = true := by
  decide

def missing36882 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5009165247529910272
theorem maskCheck36882 :
    checkMaskFor missing36882 StrongPackedBucketN12A4Shard288.record36882 = true := by
  decide

def missing36883 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5117251638586802176
theorem maskCheck36883 :
    checkMaskFor missing36883 StrongPackedBucketN12A4Shard288.record36883 = true := by
  decide

def missing36884 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5549597202814369792
theorem maskCheck36884 :
    checkMaskFor missing36884 StrongPackedBucketN12A4Shard288.record36884 = true := by
  decide

def missing36885 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5873856375985045504
theorem maskCheck36885 :
    checkMaskFor missing36885 StrongPackedBucketN12A4Shard288.record36885 = true := by
  decide

def missing36886 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5981942767041937408
theorem maskCheck36886 :
    checkMaskFor missing36886 StrongPackedBucketN12A4Shard288.record36886 = true := by
  decide

def missing36887 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6126057955117793280
theorem maskCheck36887 :
    checkMaskFor missing36887 StrongPackedBucketN12A4Shard288.record36887 = true := by
  decide

def missing36888 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7026777880591892480
theorem maskCheck36888 :
    checkMaskFor missing36888 StrongPackedBucketN12A4Shard288.record36888 = true := by
  decide

def missing36889 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8143670588179775488
theorem maskCheck36889 :
    checkMaskFor missing36889 StrongPackedBucketN12A4Shard288.record36889 = true := by
  decide

def missing36890 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9476736077881442304
theorem maskCheck36890 :
    checkMaskFor missing36890 StrongPackedBucketN12A4Shard288.record36890 = true := by
  decide

def missing36891 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9620851265957298176
theorem maskCheck36891 :
    checkMaskFor missing36891 StrongPackedBucketN12A4Shard288.record36891 = true := by
  decide

def missing36892 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9692908859995226112
theorem maskCheck36892 :
    checkMaskFor missing36892 StrongPackedBucketN12A4Shard288.record36892 = true := by
  decide

def missing36893 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9728937657014190080
theorem maskCheck36893 :
    checkMaskFor missing36893 StrongPackedBucketN12A4Shard288.record36893 = true := by
  decide

def missing36894 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9909081642109009920
theorem maskCheck36894 :
    checkMaskFor missing36894 StrongPackedBucketN12A4Shard288.record36894 = true := by
  decide

def missing36895 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9981139236146937856
theorem maskCheck36895 :
    checkMaskFor missing36895 StrongPackedBucketN12A4Shard288.record36895 = true := by
  decide

def missing36896 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10017168033165901824
theorem maskCheck36896 :
    checkMaskFor missing36896 StrongPackedBucketN12A4Shard288.record36896 = true := by
  decide

def missing36897 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10125254424222793728
theorem maskCheck36897 :
    checkMaskFor missing36897 StrongPackedBucketN12A4Shard288.record36897 = true := by
  decide

def missing36898 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10161283221241757696
theorem maskCheck36898 :
    checkMaskFor missing36898 StrongPackedBucketN12A4Shard288.record36898 = true := by
  decide

def missing36899 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10233340815279685632
theorem maskCheck36899 :
    checkMaskFor missing36899 StrongPackedBucketN12A4Shard288.record36899 = true := by
  decide

def missing36900 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10485542394412433408
theorem maskCheck36900 :
    checkMaskFor missing36900 StrongPackedBucketN12A4Shard288.record36900 = true := by
  decide

def missing36901 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10557599988450361344
theorem maskCheck36901 :
    checkMaskFor missing36901 StrongPackedBucketN12A4Shard288.record36901 = true := by
  decide

def missing36902 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10593628785469325312
theorem maskCheck36902 :
    checkMaskFor missing36902 StrongPackedBucketN12A4Shard288.record36902 = true := by
  decide

def missing36903 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10701715176526217216
theorem maskCheck36903 :
    checkMaskFor missing36903 StrongPackedBucketN12A4Shard288.record36903 = true := by
  decide

def missing36904 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10737743973545181184
theorem maskCheck36904 :
    checkMaskFor missing36904 StrongPackedBucketN12A4Shard288.record36904 = true := by
  decide

def missing36905 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10809801567583109120
theorem maskCheck36905 :
    checkMaskFor missing36905 StrongPackedBucketN12A4Shard288.record36905 = true := by
  decide

def missing36906 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10989945552677928960
theorem maskCheck36906 :
    checkMaskFor missing36906 StrongPackedBucketN12A4Shard288.record36906 = true := by
  decide

def missing36907 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11025974349696892928
theorem maskCheck36907 :
    checkMaskFor missing36907 StrongPackedBucketN12A4Shard288.record36907 = true := by
  decide

def missing36908 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11098031943734820864
theorem maskCheck36908 :
    checkMaskFor missing36908 StrongPackedBucketN12A4Shard288.record36908 = true := by
  decide

def missing36909 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11242147131810676736
theorem maskCheck36909 :
    checkMaskFor missing36909 StrongPackedBucketN12A4Shard288.record36909 = true := by
  decide

def missing36910 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11638463899019280384
theorem maskCheck36910 :
    checkMaskFor missing36910 StrongPackedBucketN12A4Shard288.record36910 = true := by
  decide

def missing36911 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11710521493057208320
theorem maskCheck36911 :
    checkMaskFor missing36911 StrongPackedBucketN12A4Shard288.record36911 = true := by
  decide

def missing36912 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11854636681133064192
theorem maskCheck36912 :
    checkMaskFor missing36912 StrongPackedBucketN12A4Shard288.record36912 = true := by
  decide

def missing36913 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12142867057284775936
theorem maskCheck36913 :
    checkMaskFor missing36913 StrongPackedBucketN12A4Shard288.record36913 = true := by
  decide

def missing36914 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12719327809588199424
theorem maskCheck36914 :
    checkMaskFor missing36914 StrongPackedBucketN12A4Shard288.record36914 = true := by
  decide

def missing36915 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12755356606607163392
theorem maskCheck36915 :
    checkMaskFor missing36915 StrongPackedBucketN12A4Shard288.record36915 = true := by
  decide

def missing36916 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12827414200645091328
theorem maskCheck36916 :
    checkMaskFor missing36916 StrongPackedBucketN12A4Shard288.record36916 = true := by
  decide

def missing36917 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12971529388720947200
theorem maskCheck36917 :
    checkMaskFor missing36917 StrongPackedBucketN12A4Shard288.record36917 = true := by
  decide

def missing36918 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13259759764872658944
theorem maskCheck36918 :
    checkMaskFor missing36918 StrongPackedBucketN12A4Shard288.record36918 = true := by
  decide

def missing36919 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13944306908232974336
theorem maskCheck36919 :
    checkMaskFor missing36919 StrongPackedBucketN12A4Shard288.record36919 = true := by
  decide

def missing36920 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14052393299289866240
theorem maskCheck36920 :
    checkMaskFor missing36920 StrongPackedBucketN12A4Shard288.record36920 = true := by
  decide

def missing36921 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14196508487365722112
theorem maskCheck36921 :
    checkMaskFor missing36921 StrongPackedBucketN12A4Shard288.record36921 = true := by
  decide

def missing36922 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14484738863517433856
theorem maskCheck36922 :
    checkMaskFor missing36922 StrongPackedBucketN12A4Shard288.record36922 = true := by
  decide

def missing36923 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15061199615820857344
theorem maskCheck36923 :
    checkMaskFor missing36923 StrongPackedBucketN12A4Shard288.record36923 = true := by
  decide

def missing36924 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27779364963515138048
theorem maskCheck36924 :
    checkMaskFor missing36924 StrongPackedBucketN12A4Shard288.record36924 = true := by
  decide

def missing36925 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27851422557553065984
theorem maskCheck36925 :
    checkMaskFor missing36925 StrongPackedBucketN12A4Shard288.record36925 = true := by
  decide

def missing36926 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27887451354572029952
theorem maskCheck36926 :
    checkMaskFor missing36926 StrongPackedBucketN12A4Shard288.record36926 = true := by
  decide

def missing36927 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27995537745628921856
theorem maskCheck36927 :
    checkMaskFor missing36927 StrongPackedBucketN12A4Shard288.record36927 = true := by
  decide

def missing36928 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28031566542647885824
theorem maskCheck36928 :
    checkMaskFor missing36928 StrongPackedBucketN12A4Shard288.record36928 = true := by
  decide

def missing36929 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28103624136685813760
theorem maskCheck36929 :
    checkMaskFor missing36929 StrongPackedBucketN12A4Shard288.record36929 = true := by
  decide

def missing36930 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28535969700913381376
theorem maskCheck36930 :
    checkMaskFor missing36930 StrongPackedBucketN12A4Shard288.record36930 = true := by
  decide

def missing36931 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28860228874084057088
theorem maskCheck36931 :
    checkMaskFor missing36931 StrongPackedBucketN12A4Shard288.record36931 = true := by
  decide

def missing36932 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28896257671103021056
theorem maskCheck36932 :
    checkMaskFor missing36932 StrongPackedBucketN12A4Shard288.record36932 = true := by
  decide

def missing36933 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28968315265140948992
theorem maskCheck36933 :
    checkMaskFor missing36933 StrongPackedBucketN12A4Shard288.record36933 = true := by
  decide

def missing36934 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29112430453216804864
theorem maskCheck36934 :
    checkMaskFor missing36934 StrongPackedBucketN12A4Shard288.record36934 = true := by
  decide

def missing36935 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30013150378690904064
theorem maskCheck36935 :
    checkMaskFor missing36935 StrongPackedBucketN12A4Shard288.record36935 = true := by
  decide

def missing36936 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 31130043086278787072
theorem maskCheck36936 :
    checkMaskFor missing36936 StrongPackedBucketN12A4Shard288.record36936 = true := by
  decide

def missing36937 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32355022184923561984
theorem maskCheck36937 :
    checkMaskFor missing36937 StrongPackedBucketN12A4Shard288.record36937 = true := by
  decide

def missing36938 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37146852188445769728
theorem maskCheck36938 :
    checkMaskFor missing36938 StrongPackedBucketN12A4Shard288.record36938 = true := by
  decide

def missing36939 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37290967376521625600
theorem maskCheck36939 :
    checkMaskFor missing36939 StrongPackedBucketN12A4Shard288.record36939 = true := by
  decide

def missing36940 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37363024970559553536
theorem maskCheck36940 :
    checkMaskFor missing36940 StrongPackedBucketN12A4Shard288.record36940 = true := by
  decide

def missing36941 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37795370534787121152
theorem maskCheck36941 :
    checkMaskFor missing36941 StrongPackedBucketN12A4Shard288.record36941 = true := by
  decide

def missing36942 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38155658504976760832
theorem maskCheck36942 :
    checkMaskFor missing36942 StrongPackedBucketN12A4Shard288.record36942 = true := by
  decide

def missing36943 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38227716099014688768
theorem maskCheck36943 :
    checkMaskFor missing36943 StrongPackedBucketN12A4Shard288.record36943 = true := by
  decide

def missing36944 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38371831287090544640
theorem maskCheck36944 :
    checkMaskFor missing36944 StrongPackedBucketN12A4Shard288.record36944 = true := by
  decide

def missing36945 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40389443920152526848
theorem maskCheck36945 :
    checkMaskFor missing36945 StrongPackedBucketN12A4Shard288.record36945 = true := by
  decide

def missing36946 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41614423018797301760
theorem maskCheck36946 :
    checkMaskFor missing36946 StrongPackedBucketN12A4Shard288.record36946 = true := by
  decide

def missing36947 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46226109037224689664
theorem maskCheck36947 :
    checkMaskFor missing36947 StrongPackedBucketN12A4Shard288.record36947 = true := by
  decide

def missing36948 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46298166631262617600
theorem maskCheck36948 :
    checkMaskFor missing36948 StrongPackedBucketN12A4Shard288.record36948 = true := by
  decide

def missing36949 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46442281819338473472
theorem maskCheck36949 :
    checkMaskFor missing36949 StrongPackedBucketN12A4Shard288.record36949 = true := by
  decide

def missing36950 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46730512195490185216
theorem maskCheck36950 :
    checkMaskFor missing36950 StrongPackedBucketN12A4Shard288.record36950 = true := by
  decide

def missing36951 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47306972947793608704
theorem maskCheck36951 :
    checkMaskFor missing36951 StrongPackedBucketN12A4Shard288.record36951 = true := by
  decide

def missing36952 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64600795516896313344
theorem maskCheck36952 :
    checkMaskFor missing36952 StrongPackedBucketN12A4Shard288.record36952 = true := by
  decide

def missing36953 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 541840707783000064
theorem maskCheck36953 :
    checkMaskFor missing36953 StrongPackedBucketN12A4Shard288.record36953 = true := by
  decide

def missing36954 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 830071083934711808
theorem maskCheck36954 :
    checkMaskFor missing36954 StrongPackedBucketN12A4Shard288.record36954 = true := by
  decide

def missing36955 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 974186272010567680
theorem maskCheck36955 :
    checkMaskFor missing36955 StrongPackedBucketN12A4Shard288.record36955 = true := by
  decide

def missing36956 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1046243866048495616
theorem maskCheck36956 :
    checkMaskFor missing36956 StrongPackedBucketN12A4Shard288.record36956 = true := by
  decide

def missing36957 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1838877400465702912
theorem maskCheck36957 :
    checkMaskFor missing36957 StrongPackedBucketN12A4Shard288.record36957 = true := by
  decide

def missing36958 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1910934994503630848
theorem maskCheck36958 :
    checkMaskFor missing36958 StrongPackedBucketN12A4Shard288.record36958 = true := by
  decide

def missing36959 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2163136573636378624
theorem maskCheck36959 :
    checkMaskFor missing36959 StrongPackedBucketN12A4Shard288.record36959 = true := by
  decide

def missing36960 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2559453340844982272
theorem maskCheck36960 :
    checkMaskFor missing36960 StrongPackedBucketN12A4Shard288.record36960 = true := by
  decide

def missing36961 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2775626122958766080
theorem maskCheck36961 :
    checkMaskFor missing36961 StrongPackedBucketN12A4Shard288.record36961 = true := by
  decide

def missing36962 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2991798905072549888
theorem maskCheck36962 :
    checkMaskFor missing36962 StrongPackedBucketN12A4Shard288.record36962 = true := by
  decide

def missing36963 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3063856499110477824
theorem maskCheck36963 :
    checkMaskFor missing36963 StrongPackedBucketN12A4Shard288.record36963 = true := by
  decide

def missing36964 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3207971687186333696
theorem maskCheck36964 :
    checkMaskFor missing36964 StrongPackedBucketN12A4Shard288.record36964 = true := by
  decide

def missing36965 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4072662815641468928
theorem maskCheck36965 :
    checkMaskFor missing36965 StrongPackedBucketN12A4Shard288.record36965 = true := by
  decide

def missing36966 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7027024171196514304
theorem maskCheck36966 :
    checkMaskFor missing36966 StrongPackedBucketN12A4Shard288.record36966 = true := by
  decide

def missing36967 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9476982368486064128
theorem maskCheck36967 :
    checkMaskFor missing36967 StrongPackedBucketN12A4Shard288.record36967 = true := by
  decide

def missing36968 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9693155150599847936
theorem maskCheck36968 :
    checkMaskFor missing36968 StrongPackedBucketN12A4Shard288.record36968 = true := by
  decide

def missing36969 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9909327932713631744
theorem maskCheck36969 :
    checkMaskFor missing36969 StrongPackedBucketN12A4Shard288.record36969 = true := by
  decide

def missing36970 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9981385526751559680
theorem maskCheck36970 :
    checkMaskFor missing36970 StrongPackedBucketN12A4Shard288.record36970 = true := by
  decide

def missing36971 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10125500714827415552
theorem maskCheck36971 :
    checkMaskFor missing36971 StrongPackedBucketN12A4Shard288.record36971 = true := by
  decide

def missing36972 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10233587105884307456
theorem maskCheck36972 :
    checkMaskFor missing36972 StrongPackedBucketN12A4Shard288.record36972 = true := by
  decide

def missing36973 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10990191843282550784
theorem maskCheck36973 :
    checkMaskFor missing36973 StrongPackedBucketN12A4Shard288.record36973 = true := by
  decide

def missing36974 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11098278234339442688
theorem maskCheck36974 :
    checkMaskFor missing36974 StrongPackedBucketN12A4Shard288.record36974 = true := by
  decide

def missing36975 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11638710189623902208
theorem maskCheck36975 :
    checkMaskFor missing36975 StrongPackedBucketN12A4Shard288.record36975 = true := by
  decide

def missing36976 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11710767783661830144
theorem maskCheck36976 :
    checkMaskFor missing36976 StrongPackedBucketN12A4Shard288.record36976 = true := by
  decide

def missing36977 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12143113347889397760
theorem maskCheck36977 :
    checkMaskFor missing36977 StrongPackedBucketN12A4Shard288.record36977 = true := by
  decide

def missing36978 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18700354405340839936
theorem maskCheck36978 :
    checkMaskFor missing36978 StrongPackedBucketN12A4Shard288.record36978 = true := by
  decide

def missing36979 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18844469593416695808
theorem maskCheck36979 :
    checkMaskFor missing36979 StrongPackedBucketN12A4Shard288.record36979 = true := by
  decide

def missing36980 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18916527187454623744
theorem maskCheck36980 :
    checkMaskFor missing36980 StrongPackedBucketN12A4Shard288.record36980 = true := by
  decide

def missing36981 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19132699969568407552
theorem maskCheck36981 :
    checkMaskFor missing36981 StrongPackedBucketN12A4Shard288.record36981 = true := by
  decide

def missing36982 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19204757563606335488
theorem maskCheck36982 :
    checkMaskFor missing36982 StrongPackedBucketN12A4Shard288.record36982 = true := by
  decide

def missing36983 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19348872751682191360
theorem maskCheck36983 :
    checkMaskFor missing36983 StrongPackedBucketN12A4Shard288.record36983 = true := by
  decide

def missing36984 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19456959142739083264
theorem maskCheck36984 :
    checkMaskFor missing36984 StrongPackedBucketN12A4Shard288.record36984 = true := by
  decide

def missing36985 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19709160721871831040
theorem maskCheck36985 :
    checkMaskFor missing36985 StrongPackedBucketN12A4Shard288.record36985 = true := by
  decide

def missing36986 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19781218315909758976
theorem maskCheck36986 :
    checkMaskFor missing36986 StrongPackedBucketN12A4Shard288.record36986 = true := by
  decide

def missing36987 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19925333503985614848
theorem maskCheck36987 :
    checkMaskFor missing36987 StrongPackedBucketN12A4Shard288.record36987 = true := by
  decide

def missing36988 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20033419895042506752
theorem maskCheck36988 :
    checkMaskFor missing36988 StrongPackedBucketN12A4Shard288.record36988 = true := by
  decide

def missing36989 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20213563880137326592
theorem maskCheck36989 :
    checkMaskFor missing36989 StrongPackedBucketN12A4Shard288.record36989 = true := by
  decide

def missing36990 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20321650271194218496
theorem maskCheck36990 :
    checkMaskFor missing36990 StrongPackedBucketN12A4Shard288.record36990 = true := by
  decide

def missing36991 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20465765459270074368
theorem maskCheck36991 :
    checkMaskFor missing36991 StrongPackedBucketN12A4Shard288.record36991 = true := by
  decide

def missing36864_36865 : List (BitVec (edgeCount 12)) :=
  [missing36864]
abbrev records36864_36865 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36864]
theorem aligned36864_36865 :
    AlignedValid 12 4 missing36864_36865 records36864_36865 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36864
    maskCheck36864 AlignedValid.nil

def missing36865_36866 : List (BitVec (edgeCount 12)) :=
  [missing36865]
abbrev records36865_36866 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36865]
theorem aligned36865_36866 :
    AlignedValid 12 4 missing36865_36866 records36865_36866 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36865
    maskCheck36865 AlignedValid.nil

def missing36864_36866 : List (BitVec (edgeCount 12)) :=
  missing36864_36865 ++ missing36865_36866
abbrev records36864_36866 : List Blob :=
  records36864_36865 ++ records36865_36866
theorem aligned36864_36866 :
    AlignedValid 12 4 missing36864_36866 records36864_36866 :=
  aligned36864_36865.append aligned36865_36866

def missing36866_36867 : List (BitVec (edgeCount 12)) :=
  [missing36866]
abbrev records36866_36867 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36866]
theorem aligned36866_36867 :
    AlignedValid 12 4 missing36866_36867 records36866_36867 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36866
    maskCheck36866 AlignedValid.nil

def missing36867_36868 : List (BitVec (edgeCount 12)) :=
  [missing36867]
abbrev records36867_36868 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36867]
theorem aligned36867_36868 :
    AlignedValid 12 4 missing36867_36868 records36867_36868 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36867
    maskCheck36867 AlignedValid.nil

def missing36866_36868 : List (BitVec (edgeCount 12)) :=
  missing36866_36867 ++ missing36867_36868
abbrev records36866_36868 : List Blob :=
  records36866_36867 ++ records36867_36868
theorem aligned36866_36868 :
    AlignedValid 12 4 missing36866_36868 records36866_36868 :=
  aligned36866_36867.append aligned36867_36868

def missing36864_36868 : List (BitVec (edgeCount 12)) :=
  missing36864_36866 ++ missing36866_36868
abbrev records36864_36868 : List Blob :=
  records36864_36866 ++ records36866_36868
theorem aligned36864_36868 :
    AlignedValid 12 4 missing36864_36868 records36864_36868 :=
  aligned36864_36866.append aligned36866_36868

def missing36868_36869 : List (BitVec (edgeCount 12)) :=
  [missing36868]
abbrev records36868_36869 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36868]
theorem aligned36868_36869 :
    AlignedValid 12 4 missing36868_36869 records36868_36869 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36868
    maskCheck36868 AlignedValid.nil

def missing36869_36870 : List (BitVec (edgeCount 12)) :=
  [missing36869]
abbrev records36869_36870 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36869]
theorem aligned36869_36870 :
    AlignedValid 12 4 missing36869_36870 records36869_36870 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36869
    maskCheck36869 AlignedValid.nil

def missing36868_36870 : List (BitVec (edgeCount 12)) :=
  missing36868_36869 ++ missing36869_36870
abbrev records36868_36870 : List Blob :=
  records36868_36869 ++ records36869_36870
theorem aligned36868_36870 :
    AlignedValid 12 4 missing36868_36870 records36868_36870 :=
  aligned36868_36869.append aligned36869_36870

def missing36870_36871 : List (BitVec (edgeCount 12)) :=
  [missing36870]
abbrev records36870_36871 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36870]
theorem aligned36870_36871 :
    AlignedValid 12 4 missing36870_36871 records36870_36871 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36870
    maskCheck36870 AlignedValid.nil

def missing36871_36872 : List (BitVec (edgeCount 12)) :=
  [missing36871]
abbrev records36871_36872 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36871]
theorem aligned36871_36872 :
    AlignedValid 12 4 missing36871_36872 records36871_36872 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36871
    maskCheck36871 AlignedValid.nil

def missing36870_36872 : List (BitVec (edgeCount 12)) :=
  missing36870_36871 ++ missing36871_36872
abbrev records36870_36872 : List Blob :=
  records36870_36871 ++ records36871_36872
theorem aligned36870_36872 :
    AlignedValid 12 4 missing36870_36872 records36870_36872 :=
  aligned36870_36871.append aligned36871_36872

def missing36868_36872 : List (BitVec (edgeCount 12)) :=
  missing36868_36870 ++ missing36870_36872
abbrev records36868_36872 : List Blob :=
  records36868_36870 ++ records36870_36872
theorem aligned36868_36872 :
    AlignedValid 12 4 missing36868_36872 records36868_36872 :=
  aligned36868_36870.append aligned36870_36872

def missing36864_36872 : List (BitVec (edgeCount 12)) :=
  missing36864_36868 ++ missing36868_36872
abbrev records36864_36872 : List Blob :=
  records36864_36868 ++ records36868_36872
theorem aligned36864_36872 :
    AlignedValid 12 4 missing36864_36872 records36864_36872 :=
  aligned36864_36868.append aligned36868_36872

def missing36872_36873 : List (BitVec (edgeCount 12)) :=
  [missing36872]
abbrev records36872_36873 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36872]
theorem aligned36872_36873 :
    AlignedValid 12 4 missing36872_36873 records36872_36873 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36872
    maskCheck36872 AlignedValid.nil

def missing36873_36874 : List (BitVec (edgeCount 12)) :=
  [missing36873]
abbrev records36873_36874 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36873]
theorem aligned36873_36874 :
    AlignedValid 12 4 missing36873_36874 records36873_36874 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36873
    maskCheck36873 AlignedValid.nil

def missing36872_36874 : List (BitVec (edgeCount 12)) :=
  missing36872_36873 ++ missing36873_36874
abbrev records36872_36874 : List Blob :=
  records36872_36873 ++ records36873_36874
theorem aligned36872_36874 :
    AlignedValid 12 4 missing36872_36874 records36872_36874 :=
  aligned36872_36873.append aligned36873_36874

def missing36874_36875 : List (BitVec (edgeCount 12)) :=
  [missing36874]
abbrev records36874_36875 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36874]
theorem aligned36874_36875 :
    AlignedValid 12 4 missing36874_36875 records36874_36875 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36874
    maskCheck36874 AlignedValid.nil

def missing36875_36876 : List (BitVec (edgeCount 12)) :=
  [missing36875]
abbrev records36875_36876 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36875]
theorem aligned36875_36876 :
    AlignedValid 12 4 missing36875_36876 records36875_36876 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36875
    maskCheck36875 AlignedValid.nil

def missing36874_36876 : List (BitVec (edgeCount 12)) :=
  missing36874_36875 ++ missing36875_36876
abbrev records36874_36876 : List Blob :=
  records36874_36875 ++ records36875_36876
theorem aligned36874_36876 :
    AlignedValid 12 4 missing36874_36876 records36874_36876 :=
  aligned36874_36875.append aligned36875_36876

def missing36872_36876 : List (BitVec (edgeCount 12)) :=
  missing36872_36874 ++ missing36874_36876
abbrev records36872_36876 : List Blob :=
  records36872_36874 ++ records36874_36876
theorem aligned36872_36876 :
    AlignedValid 12 4 missing36872_36876 records36872_36876 :=
  aligned36872_36874.append aligned36874_36876

def missing36876_36877 : List (BitVec (edgeCount 12)) :=
  [missing36876]
abbrev records36876_36877 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36876]
theorem aligned36876_36877 :
    AlignedValid 12 4 missing36876_36877 records36876_36877 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36876
    maskCheck36876 AlignedValid.nil

def missing36877_36878 : List (BitVec (edgeCount 12)) :=
  [missing36877]
abbrev records36877_36878 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36877]
theorem aligned36877_36878 :
    AlignedValid 12 4 missing36877_36878 records36877_36878 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36877
    maskCheck36877 AlignedValid.nil

def missing36876_36878 : List (BitVec (edgeCount 12)) :=
  missing36876_36877 ++ missing36877_36878
abbrev records36876_36878 : List Blob :=
  records36876_36877 ++ records36877_36878
theorem aligned36876_36878 :
    AlignedValid 12 4 missing36876_36878 records36876_36878 :=
  aligned36876_36877.append aligned36877_36878

def missing36878_36879 : List (BitVec (edgeCount 12)) :=
  [missing36878]
abbrev records36878_36879 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36878]
theorem aligned36878_36879 :
    AlignedValid 12 4 missing36878_36879 records36878_36879 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36878
    maskCheck36878 AlignedValid.nil

def missing36879_36880 : List (BitVec (edgeCount 12)) :=
  [missing36879]
abbrev records36879_36880 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36879]
theorem aligned36879_36880 :
    AlignedValid 12 4 missing36879_36880 records36879_36880 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36879
    maskCheck36879 AlignedValid.nil

def missing36878_36880 : List (BitVec (edgeCount 12)) :=
  missing36878_36879 ++ missing36879_36880
abbrev records36878_36880 : List Blob :=
  records36878_36879 ++ records36879_36880
theorem aligned36878_36880 :
    AlignedValid 12 4 missing36878_36880 records36878_36880 :=
  aligned36878_36879.append aligned36879_36880

def missing36876_36880 : List (BitVec (edgeCount 12)) :=
  missing36876_36878 ++ missing36878_36880
abbrev records36876_36880 : List Blob :=
  records36876_36878 ++ records36878_36880
theorem aligned36876_36880 :
    AlignedValid 12 4 missing36876_36880 records36876_36880 :=
  aligned36876_36878.append aligned36878_36880

def missing36872_36880 : List (BitVec (edgeCount 12)) :=
  missing36872_36876 ++ missing36876_36880
abbrev records36872_36880 : List Blob :=
  records36872_36876 ++ records36876_36880
theorem aligned36872_36880 :
    AlignedValid 12 4 missing36872_36880 records36872_36880 :=
  aligned36872_36876.append aligned36876_36880

def missing36864_36880 : List (BitVec (edgeCount 12)) :=
  missing36864_36872 ++ missing36872_36880
abbrev records36864_36880 : List Blob :=
  records36864_36872 ++ records36872_36880
theorem aligned36864_36880 :
    AlignedValid 12 4 missing36864_36880 records36864_36880 :=
  aligned36864_36872.append aligned36872_36880

def missing36880_36881 : List (BitVec (edgeCount 12)) :=
  [missing36880]
abbrev records36880_36881 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36880]
theorem aligned36880_36881 :
    AlignedValid 12 4 missing36880_36881 records36880_36881 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36880
    maskCheck36880 AlignedValid.nil

def missing36881_36882 : List (BitVec (edgeCount 12)) :=
  [missing36881]
abbrev records36881_36882 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36881]
theorem aligned36881_36882 :
    AlignedValid 12 4 missing36881_36882 records36881_36882 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36881
    maskCheck36881 AlignedValid.nil

def missing36880_36882 : List (BitVec (edgeCount 12)) :=
  missing36880_36881 ++ missing36881_36882
abbrev records36880_36882 : List Blob :=
  records36880_36881 ++ records36881_36882
theorem aligned36880_36882 :
    AlignedValid 12 4 missing36880_36882 records36880_36882 :=
  aligned36880_36881.append aligned36881_36882

def missing36882_36883 : List (BitVec (edgeCount 12)) :=
  [missing36882]
abbrev records36882_36883 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36882]
theorem aligned36882_36883 :
    AlignedValid 12 4 missing36882_36883 records36882_36883 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36882
    maskCheck36882 AlignedValid.nil

def missing36883_36884 : List (BitVec (edgeCount 12)) :=
  [missing36883]
abbrev records36883_36884 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36883]
theorem aligned36883_36884 :
    AlignedValid 12 4 missing36883_36884 records36883_36884 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36883
    maskCheck36883 AlignedValid.nil

def missing36882_36884 : List (BitVec (edgeCount 12)) :=
  missing36882_36883 ++ missing36883_36884
abbrev records36882_36884 : List Blob :=
  records36882_36883 ++ records36883_36884
theorem aligned36882_36884 :
    AlignedValid 12 4 missing36882_36884 records36882_36884 :=
  aligned36882_36883.append aligned36883_36884

def missing36880_36884 : List (BitVec (edgeCount 12)) :=
  missing36880_36882 ++ missing36882_36884
abbrev records36880_36884 : List Blob :=
  records36880_36882 ++ records36882_36884
theorem aligned36880_36884 :
    AlignedValid 12 4 missing36880_36884 records36880_36884 :=
  aligned36880_36882.append aligned36882_36884

def missing36884_36885 : List (BitVec (edgeCount 12)) :=
  [missing36884]
abbrev records36884_36885 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36884]
theorem aligned36884_36885 :
    AlignedValid 12 4 missing36884_36885 records36884_36885 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36884
    maskCheck36884 AlignedValid.nil

def missing36885_36886 : List (BitVec (edgeCount 12)) :=
  [missing36885]
abbrev records36885_36886 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36885]
theorem aligned36885_36886 :
    AlignedValid 12 4 missing36885_36886 records36885_36886 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36885
    maskCheck36885 AlignedValid.nil

def missing36884_36886 : List (BitVec (edgeCount 12)) :=
  missing36884_36885 ++ missing36885_36886
abbrev records36884_36886 : List Blob :=
  records36884_36885 ++ records36885_36886
theorem aligned36884_36886 :
    AlignedValid 12 4 missing36884_36886 records36884_36886 :=
  aligned36884_36885.append aligned36885_36886

def missing36886_36887 : List (BitVec (edgeCount 12)) :=
  [missing36886]
abbrev records36886_36887 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36886]
theorem aligned36886_36887 :
    AlignedValid 12 4 missing36886_36887 records36886_36887 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36886
    maskCheck36886 AlignedValid.nil

def missing36887_36888 : List (BitVec (edgeCount 12)) :=
  [missing36887]
abbrev records36887_36888 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36887]
theorem aligned36887_36888 :
    AlignedValid 12 4 missing36887_36888 records36887_36888 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36887
    maskCheck36887 AlignedValid.nil

def missing36886_36888 : List (BitVec (edgeCount 12)) :=
  missing36886_36887 ++ missing36887_36888
abbrev records36886_36888 : List Blob :=
  records36886_36887 ++ records36887_36888
theorem aligned36886_36888 :
    AlignedValid 12 4 missing36886_36888 records36886_36888 :=
  aligned36886_36887.append aligned36887_36888

def missing36884_36888 : List (BitVec (edgeCount 12)) :=
  missing36884_36886 ++ missing36886_36888
abbrev records36884_36888 : List Blob :=
  records36884_36886 ++ records36886_36888
theorem aligned36884_36888 :
    AlignedValid 12 4 missing36884_36888 records36884_36888 :=
  aligned36884_36886.append aligned36886_36888

def missing36880_36888 : List (BitVec (edgeCount 12)) :=
  missing36880_36884 ++ missing36884_36888
abbrev records36880_36888 : List Blob :=
  records36880_36884 ++ records36884_36888
theorem aligned36880_36888 :
    AlignedValid 12 4 missing36880_36888 records36880_36888 :=
  aligned36880_36884.append aligned36884_36888

def missing36888_36889 : List (BitVec (edgeCount 12)) :=
  [missing36888]
abbrev records36888_36889 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36888]
theorem aligned36888_36889 :
    AlignedValid 12 4 missing36888_36889 records36888_36889 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36888
    maskCheck36888 AlignedValid.nil

def missing36889_36890 : List (BitVec (edgeCount 12)) :=
  [missing36889]
abbrev records36889_36890 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36889]
theorem aligned36889_36890 :
    AlignedValid 12 4 missing36889_36890 records36889_36890 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36889
    maskCheck36889 AlignedValid.nil

def missing36888_36890 : List (BitVec (edgeCount 12)) :=
  missing36888_36889 ++ missing36889_36890
abbrev records36888_36890 : List Blob :=
  records36888_36889 ++ records36889_36890
theorem aligned36888_36890 :
    AlignedValid 12 4 missing36888_36890 records36888_36890 :=
  aligned36888_36889.append aligned36889_36890

def missing36890_36891 : List (BitVec (edgeCount 12)) :=
  [missing36890]
abbrev records36890_36891 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36890]
theorem aligned36890_36891 :
    AlignedValid 12 4 missing36890_36891 records36890_36891 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36890
    maskCheck36890 AlignedValid.nil

def missing36891_36892 : List (BitVec (edgeCount 12)) :=
  [missing36891]
abbrev records36891_36892 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36891]
theorem aligned36891_36892 :
    AlignedValid 12 4 missing36891_36892 records36891_36892 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36891
    maskCheck36891 AlignedValid.nil

def missing36890_36892 : List (BitVec (edgeCount 12)) :=
  missing36890_36891 ++ missing36891_36892
abbrev records36890_36892 : List Blob :=
  records36890_36891 ++ records36891_36892
theorem aligned36890_36892 :
    AlignedValid 12 4 missing36890_36892 records36890_36892 :=
  aligned36890_36891.append aligned36891_36892

def missing36888_36892 : List (BitVec (edgeCount 12)) :=
  missing36888_36890 ++ missing36890_36892
abbrev records36888_36892 : List Blob :=
  records36888_36890 ++ records36890_36892
theorem aligned36888_36892 :
    AlignedValid 12 4 missing36888_36892 records36888_36892 :=
  aligned36888_36890.append aligned36890_36892

def missing36892_36893 : List (BitVec (edgeCount 12)) :=
  [missing36892]
abbrev records36892_36893 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36892]
theorem aligned36892_36893 :
    AlignedValid 12 4 missing36892_36893 records36892_36893 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36892
    maskCheck36892 AlignedValid.nil

def missing36893_36894 : List (BitVec (edgeCount 12)) :=
  [missing36893]
abbrev records36893_36894 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36893]
theorem aligned36893_36894 :
    AlignedValid 12 4 missing36893_36894 records36893_36894 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36893
    maskCheck36893 AlignedValid.nil

def missing36892_36894 : List (BitVec (edgeCount 12)) :=
  missing36892_36893 ++ missing36893_36894
abbrev records36892_36894 : List Blob :=
  records36892_36893 ++ records36893_36894
theorem aligned36892_36894 :
    AlignedValid 12 4 missing36892_36894 records36892_36894 :=
  aligned36892_36893.append aligned36893_36894

def missing36894_36895 : List (BitVec (edgeCount 12)) :=
  [missing36894]
abbrev records36894_36895 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36894]
theorem aligned36894_36895 :
    AlignedValid 12 4 missing36894_36895 records36894_36895 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36894
    maskCheck36894 AlignedValid.nil

def missing36895_36896 : List (BitVec (edgeCount 12)) :=
  [missing36895]
abbrev records36895_36896 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36895]
theorem aligned36895_36896 :
    AlignedValid 12 4 missing36895_36896 records36895_36896 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36895
    maskCheck36895 AlignedValid.nil

def missing36894_36896 : List (BitVec (edgeCount 12)) :=
  missing36894_36895 ++ missing36895_36896
abbrev records36894_36896 : List Blob :=
  records36894_36895 ++ records36895_36896
theorem aligned36894_36896 :
    AlignedValid 12 4 missing36894_36896 records36894_36896 :=
  aligned36894_36895.append aligned36895_36896

def missing36892_36896 : List (BitVec (edgeCount 12)) :=
  missing36892_36894 ++ missing36894_36896
abbrev records36892_36896 : List Blob :=
  records36892_36894 ++ records36894_36896
theorem aligned36892_36896 :
    AlignedValid 12 4 missing36892_36896 records36892_36896 :=
  aligned36892_36894.append aligned36894_36896

def missing36888_36896 : List (BitVec (edgeCount 12)) :=
  missing36888_36892 ++ missing36892_36896
abbrev records36888_36896 : List Blob :=
  records36888_36892 ++ records36892_36896
theorem aligned36888_36896 :
    AlignedValid 12 4 missing36888_36896 records36888_36896 :=
  aligned36888_36892.append aligned36892_36896

def missing36880_36896 : List (BitVec (edgeCount 12)) :=
  missing36880_36888 ++ missing36888_36896
abbrev records36880_36896 : List Blob :=
  records36880_36888 ++ records36888_36896
theorem aligned36880_36896 :
    AlignedValid 12 4 missing36880_36896 records36880_36896 :=
  aligned36880_36888.append aligned36888_36896

def missing36864_36896 : List (BitVec (edgeCount 12)) :=
  missing36864_36880 ++ missing36880_36896
abbrev records36864_36896 : List Blob :=
  records36864_36880 ++ records36880_36896
theorem aligned36864_36896 :
    AlignedValid 12 4 missing36864_36896 records36864_36896 :=
  aligned36864_36880.append aligned36880_36896

def missing36896_36897 : List (BitVec (edgeCount 12)) :=
  [missing36896]
abbrev records36896_36897 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36896]
theorem aligned36896_36897 :
    AlignedValid 12 4 missing36896_36897 records36896_36897 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36896
    maskCheck36896 AlignedValid.nil

def missing36897_36898 : List (BitVec (edgeCount 12)) :=
  [missing36897]
abbrev records36897_36898 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36897]
theorem aligned36897_36898 :
    AlignedValid 12 4 missing36897_36898 records36897_36898 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36897
    maskCheck36897 AlignedValid.nil

def missing36896_36898 : List (BitVec (edgeCount 12)) :=
  missing36896_36897 ++ missing36897_36898
abbrev records36896_36898 : List Blob :=
  records36896_36897 ++ records36897_36898
theorem aligned36896_36898 :
    AlignedValid 12 4 missing36896_36898 records36896_36898 :=
  aligned36896_36897.append aligned36897_36898

def missing36898_36899 : List (BitVec (edgeCount 12)) :=
  [missing36898]
abbrev records36898_36899 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36898]
theorem aligned36898_36899 :
    AlignedValid 12 4 missing36898_36899 records36898_36899 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36898
    maskCheck36898 AlignedValid.nil

def missing36899_36900 : List (BitVec (edgeCount 12)) :=
  [missing36899]
abbrev records36899_36900 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36899]
theorem aligned36899_36900 :
    AlignedValid 12 4 missing36899_36900 records36899_36900 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36899
    maskCheck36899 AlignedValid.nil

def missing36898_36900 : List (BitVec (edgeCount 12)) :=
  missing36898_36899 ++ missing36899_36900
abbrev records36898_36900 : List Blob :=
  records36898_36899 ++ records36899_36900
theorem aligned36898_36900 :
    AlignedValid 12 4 missing36898_36900 records36898_36900 :=
  aligned36898_36899.append aligned36899_36900

def missing36896_36900 : List (BitVec (edgeCount 12)) :=
  missing36896_36898 ++ missing36898_36900
abbrev records36896_36900 : List Blob :=
  records36896_36898 ++ records36898_36900
theorem aligned36896_36900 :
    AlignedValid 12 4 missing36896_36900 records36896_36900 :=
  aligned36896_36898.append aligned36898_36900

def missing36900_36901 : List (BitVec (edgeCount 12)) :=
  [missing36900]
abbrev records36900_36901 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36900]
theorem aligned36900_36901 :
    AlignedValid 12 4 missing36900_36901 records36900_36901 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36900
    maskCheck36900 AlignedValid.nil

def missing36901_36902 : List (BitVec (edgeCount 12)) :=
  [missing36901]
abbrev records36901_36902 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36901]
theorem aligned36901_36902 :
    AlignedValid 12 4 missing36901_36902 records36901_36902 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36901
    maskCheck36901 AlignedValid.nil

def missing36900_36902 : List (BitVec (edgeCount 12)) :=
  missing36900_36901 ++ missing36901_36902
abbrev records36900_36902 : List Blob :=
  records36900_36901 ++ records36901_36902
theorem aligned36900_36902 :
    AlignedValid 12 4 missing36900_36902 records36900_36902 :=
  aligned36900_36901.append aligned36901_36902

def missing36902_36903 : List (BitVec (edgeCount 12)) :=
  [missing36902]
abbrev records36902_36903 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36902]
theorem aligned36902_36903 :
    AlignedValid 12 4 missing36902_36903 records36902_36903 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36902
    maskCheck36902 AlignedValid.nil

def missing36903_36904 : List (BitVec (edgeCount 12)) :=
  [missing36903]
abbrev records36903_36904 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36903]
theorem aligned36903_36904 :
    AlignedValid 12 4 missing36903_36904 records36903_36904 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36903
    maskCheck36903 AlignedValid.nil

def missing36902_36904 : List (BitVec (edgeCount 12)) :=
  missing36902_36903 ++ missing36903_36904
abbrev records36902_36904 : List Blob :=
  records36902_36903 ++ records36903_36904
theorem aligned36902_36904 :
    AlignedValid 12 4 missing36902_36904 records36902_36904 :=
  aligned36902_36903.append aligned36903_36904

def missing36900_36904 : List (BitVec (edgeCount 12)) :=
  missing36900_36902 ++ missing36902_36904
abbrev records36900_36904 : List Blob :=
  records36900_36902 ++ records36902_36904
theorem aligned36900_36904 :
    AlignedValid 12 4 missing36900_36904 records36900_36904 :=
  aligned36900_36902.append aligned36902_36904

def missing36896_36904 : List (BitVec (edgeCount 12)) :=
  missing36896_36900 ++ missing36900_36904
abbrev records36896_36904 : List Blob :=
  records36896_36900 ++ records36900_36904
theorem aligned36896_36904 :
    AlignedValid 12 4 missing36896_36904 records36896_36904 :=
  aligned36896_36900.append aligned36900_36904

def missing36904_36905 : List (BitVec (edgeCount 12)) :=
  [missing36904]
abbrev records36904_36905 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36904]
theorem aligned36904_36905 :
    AlignedValid 12 4 missing36904_36905 records36904_36905 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36904
    maskCheck36904 AlignedValid.nil

def missing36905_36906 : List (BitVec (edgeCount 12)) :=
  [missing36905]
abbrev records36905_36906 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36905]
theorem aligned36905_36906 :
    AlignedValid 12 4 missing36905_36906 records36905_36906 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36905
    maskCheck36905 AlignedValid.nil

def missing36904_36906 : List (BitVec (edgeCount 12)) :=
  missing36904_36905 ++ missing36905_36906
abbrev records36904_36906 : List Blob :=
  records36904_36905 ++ records36905_36906
theorem aligned36904_36906 :
    AlignedValid 12 4 missing36904_36906 records36904_36906 :=
  aligned36904_36905.append aligned36905_36906

def missing36906_36907 : List (BitVec (edgeCount 12)) :=
  [missing36906]
abbrev records36906_36907 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36906]
theorem aligned36906_36907 :
    AlignedValid 12 4 missing36906_36907 records36906_36907 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36906
    maskCheck36906 AlignedValid.nil

def missing36907_36908 : List (BitVec (edgeCount 12)) :=
  [missing36907]
abbrev records36907_36908 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36907]
theorem aligned36907_36908 :
    AlignedValid 12 4 missing36907_36908 records36907_36908 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36907
    maskCheck36907 AlignedValid.nil

def missing36906_36908 : List (BitVec (edgeCount 12)) :=
  missing36906_36907 ++ missing36907_36908
abbrev records36906_36908 : List Blob :=
  records36906_36907 ++ records36907_36908
theorem aligned36906_36908 :
    AlignedValid 12 4 missing36906_36908 records36906_36908 :=
  aligned36906_36907.append aligned36907_36908

def missing36904_36908 : List (BitVec (edgeCount 12)) :=
  missing36904_36906 ++ missing36906_36908
abbrev records36904_36908 : List Blob :=
  records36904_36906 ++ records36906_36908
theorem aligned36904_36908 :
    AlignedValid 12 4 missing36904_36908 records36904_36908 :=
  aligned36904_36906.append aligned36906_36908

def missing36908_36909 : List (BitVec (edgeCount 12)) :=
  [missing36908]
abbrev records36908_36909 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36908]
theorem aligned36908_36909 :
    AlignedValid 12 4 missing36908_36909 records36908_36909 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36908
    maskCheck36908 AlignedValid.nil

def missing36909_36910 : List (BitVec (edgeCount 12)) :=
  [missing36909]
abbrev records36909_36910 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36909]
theorem aligned36909_36910 :
    AlignedValid 12 4 missing36909_36910 records36909_36910 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36909
    maskCheck36909 AlignedValid.nil

def missing36908_36910 : List (BitVec (edgeCount 12)) :=
  missing36908_36909 ++ missing36909_36910
abbrev records36908_36910 : List Blob :=
  records36908_36909 ++ records36909_36910
theorem aligned36908_36910 :
    AlignedValid 12 4 missing36908_36910 records36908_36910 :=
  aligned36908_36909.append aligned36909_36910

def missing36910_36911 : List (BitVec (edgeCount 12)) :=
  [missing36910]
abbrev records36910_36911 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36910]
theorem aligned36910_36911 :
    AlignedValid 12 4 missing36910_36911 records36910_36911 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36910
    maskCheck36910 AlignedValid.nil

def missing36911_36912 : List (BitVec (edgeCount 12)) :=
  [missing36911]
abbrev records36911_36912 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36911]
theorem aligned36911_36912 :
    AlignedValid 12 4 missing36911_36912 records36911_36912 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36911
    maskCheck36911 AlignedValid.nil

def missing36910_36912 : List (BitVec (edgeCount 12)) :=
  missing36910_36911 ++ missing36911_36912
abbrev records36910_36912 : List Blob :=
  records36910_36911 ++ records36911_36912
theorem aligned36910_36912 :
    AlignedValid 12 4 missing36910_36912 records36910_36912 :=
  aligned36910_36911.append aligned36911_36912

def missing36908_36912 : List (BitVec (edgeCount 12)) :=
  missing36908_36910 ++ missing36910_36912
abbrev records36908_36912 : List Blob :=
  records36908_36910 ++ records36910_36912
theorem aligned36908_36912 :
    AlignedValid 12 4 missing36908_36912 records36908_36912 :=
  aligned36908_36910.append aligned36910_36912

def missing36904_36912 : List (BitVec (edgeCount 12)) :=
  missing36904_36908 ++ missing36908_36912
abbrev records36904_36912 : List Blob :=
  records36904_36908 ++ records36908_36912
theorem aligned36904_36912 :
    AlignedValid 12 4 missing36904_36912 records36904_36912 :=
  aligned36904_36908.append aligned36908_36912

def missing36896_36912 : List (BitVec (edgeCount 12)) :=
  missing36896_36904 ++ missing36904_36912
abbrev records36896_36912 : List Blob :=
  records36896_36904 ++ records36904_36912
theorem aligned36896_36912 :
    AlignedValid 12 4 missing36896_36912 records36896_36912 :=
  aligned36896_36904.append aligned36904_36912

def missing36912_36913 : List (BitVec (edgeCount 12)) :=
  [missing36912]
abbrev records36912_36913 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36912]
theorem aligned36912_36913 :
    AlignedValid 12 4 missing36912_36913 records36912_36913 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36912
    maskCheck36912 AlignedValid.nil

def missing36913_36914 : List (BitVec (edgeCount 12)) :=
  [missing36913]
abbrev records36913_36914 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36913]
theorem aligned36913_36914 :
    AlignedValid 12 4 missing36913_36914 records36913_36914 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36913
    maskCheck36913 AlignedValid.nil

def missing36912_36914 : List (BitVec (edgeCount 12)) :=
  missing36912_36913 ++ missing36913_36914
abbrev records36912_36914 : List Blob :=
  records36912_36913 ++ records36913_36914
theorem aligned36912_36914 :
    AlignedValid 12 4 missing36912_36914 records36912_36914 :=
  aligned36912_36913.append aligned36913_36914

def missing36914_36915 : List (BitVec (edgeCount 12)) :=
  [missing36914]
abbrev records36914_36915 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36914]
theorem aligned36914_36915 :
    AlignedValid 12 4 missing36914_36915 records36914_36915 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36914
    maskCheck36914 AlignedValid.nil

def missing36915_36916 : List (BitVec (edgeCount 12)) :=
  [missing36915]
abbrev records36915_36916 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36915]
theorem aligned36915_36916 :
    AlignedValid 12 4 missing36915_36916 records36915_36916 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36915
    maskCheck36915 AlignedValid.nil

def missing36914_36916 : List (BitVec (edgeCount 12)) :=
  missing36914_36915 ++ missing36915_36916
abbrev records36914_36916 : List Blob :=
  records36914_36915 ++ records36915_36916
theorem aligned36914_36916 :
    AlignedValid 12 4 missing36914_36916 records36914_36916 :=
  aligned36914_36915.append aligned36915_36916

def missing36912_36916 : List (BitVec (edgeCount 12)) :=
  missing36912_36914 ++ missing36914_36916
abbrev records36912_36916 : List Blob :=
  records36912_36914 ++ records36914_36916
theorem aligned36912_36916 :
    AlignedValid 12 4 missing36912_36916 records36912_36916 :=
  aligned36912_36914.append aligned36914_36916

def missing36916_36917 : List (BitVec (edgeCount 12)) :=
  [missing36916]
abbrev records36916_36917 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36916]
theorem aligned36916_36917 :
    AlignedValid 12 4 missing36916_36917 records36916_36917 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36916
    maskCheck36916 AlignedValid.nil

def missing36917_36918 : List (BitVec (edgeCount 12)) :=
  [missing36917]
abbrev records36917_36918 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36917]
theorem aligned36917_36918 :
    AlignedValid 12 4 missing36917_36918 records36917_36918 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36917
    maskCheck36917 AlignedValid.nil

def missing36916_36918 : List (BitVec (edgeCount 12)) :=
  missing36916_36917 ++ missing36917_36918
abbrev records36916_36918 : List Blob :=
  records36916_36917 ++ records36917_36918
theorem aligned36916_36918 :
    AlignedValid 12 4 missing36916_36918 records36916_36918 :=
  aligned36916_36917.append aligned36917_36918

def missing36918_36919 : List (BitVec (edgeCount 12)) :=
  [missing36918]
abbrev records36918_36919 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36918]
theorem aligned36918_36919 :
    AlignedValid 12 4 missing36918_36919 records36918_36919 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36918
    maskCheck36918 AlignedValid.nil

def missing36919_36920 : List (BitVec (edgeCount 12)) :=
  [missing36919]
abbrev records36919_36920 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36919]
theorem aligned36919_36920 :
    AlignedValid 12 4 missing36919_36920 records36919_36920 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36919
    maskCheck36919 AlignedValid.nil

def missing36918_36920 : List (BitVec (edgeCount 12)) :=
  missing36918_36919 ++ missing36919_36920
abbrev records36918_36920 : List Blob :=
  records36918_36919 ++ records36919_36920
theorem aligned36918_36920 :
    AlignedValid 12 4 missing36918_36920 records36918_36920 :=
  aligned36918_36919.append aligned36919_36920

def missing36916_36920 : List (BitVec (edgeCount 12)) :=
  missing36916_36918 ++ missing36918_36920
abbrev records36916_36920 : List Blob :=
  records36916_36918 ++ records36918_36920
theorem aligned36916_36920 :
    AlignedValid 12 4 missing36916_36920 records36916_36920 :=
  aligned36916_36918.append aligned36918_36920

def missing36912_36920 : List (BitVec (edgeCount 12)) :=
  missing36912_36916 ++ missing36916_36920
abbrev records36912_36920 : List Blob :=
  records36912_36916 ++ records36916_36920
theorem aligned36912_36920 :
    AlignedValid 12 4 missing36912_36920 records36912_36920 :=
  aligned36912_36916.append aligned36916_36920

def missing36920_36921 : List (BitVec (edgeCount 12)) :=
  [missing36920]
abbrev records36920_36921 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36920]
theorem aligned36920_36921 :
    AlignedValid 12 4 missing36920_36921 records36920_36921 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36920
    maskCheck36920 AlignedValid.nil

def missing36921_36922 : List (BitVec (edgeCount 12)) :=
  [missing36921]
abbrev records36921_36922 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36921]
theorem aligned36921_36922 :
    AlignedValid 12 4 missing36921_36922 records36921_36922 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36921
    maskCheck36921 AlignedValid.nil

def missing36920_36922 : List (BitVec (edgeCount 12)) :=
  missing36920_36921 ++ missing36921_36922
abbrev records36920_36922 : List Blob :=
  records36920_36921 ++ records36921_36922
theorem aligned36920_36922 :
    AlignedValid 12 4 missing36920_36922 records36920_36922 :=
  aligned36920_36921.append aligned36921_36922

def missing36922_36923 : List (BitVec (edgeCount 12)) :=
  [missing36922]
abbrev records36922_36923 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36922]
theorem aligned36922_36923 :
    AlignedValid 12 4 missing36922_36923 records36922_36923 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36922
    maskCheck36922 AlignedValid.nil

def missing36923_36924 : List (BitVec (edgeCount 12)) :=
  [missing36923]
abbrev records36923_36924 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36923]
theorem aligned36923_36924 :
    AlignedValid 12 4 missing36923_36924 records36923_36924 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36923
    maskCheck36923 AlignedValid.nil

def missing36922_36924 : List (BitVec (edgeCount 12)) :=
  missing36922_36923 ++ missing36923_36924
abbrev records36922_36924 : List Blob :=
  records36922_36923 ++ records36923_36924
theorem aligned36922_36924 :
    AlignedValid 12 4 missing36922_36924 records36922_36924 :=
  aligned36922_36923.append aligned36923_36924

def missing36920_36924 : List (BitVec (edgeCount 12)) :=
  missing36920_36922 ++ missing36922_36924
abbrev records36920_36924 : List Blob :=
  records36920_36922 ++ records36922_36924
theorem aligned36920_36924 :
    AlignedValid 12 4 missing36920_36924 records36920_36924 :=
  aligned36920_36922.append aligned36922_36924

def missing36924_36925 : List (BitVec (edgeCount 12)) :=
  [missing36924]
abbrev records36924_36925 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36924]
theorem aligned36924_36925 :
    AlignedValid 12 4 missing36924_36925 records36924_36925 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36924
    maskCheck36924 AlignedValid.nil

def missing36925_36926 : List (BitVec (edgeCount 12)) :=
  [missing36925]
abbrev records36925_36926 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36925]
theorem aligned36925_36926 :
    AlignedValid 12 4 missing36925_36926 records36925_36926 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36925
    maskCheck36925 AlignedValid.nil

def missing36924_36926 : List (BitVec (edgeCount 12)) :=
  missing36924_36925 ++ missing36925_36926
abbrev records36924_36926 : List Blob :=
  records36924_36925 ++ records36925_36926
theorem aligned36924_36926 :
    AlignedValid 12 4 missing36924_36926 records36924_36926 :=
  aligned36924_36925.append aligned36925_36926

def missing36926_36927 : List (BitVec (edgeCount 12)) :=
  [missing36926]
abbrev records36926_36927 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36926]
theorem aligned36926_36927 :
    AlignedValid 12 4 missing36926_36927 records36926_36927 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36926
    maskCheck36926 AlignedValid.nil

def missing36927_36928 : List (BitVec (edgeCount 12)) :=
  [missing36927]
abbrev records36927_36928 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36927]
theorem aligned36927_36928 :
    AlignedValid 12 4 missing36927_36928 records36927_36928 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36927
    maskCheck36927 AlignedValid.nil

def missing36926_36928 : List (BitVec (edgeCount 12)) :=
  missing36926_36927 ++ missing36927_36928
abbrev records36926_36928 : List Blob :=
  records36926_36927 ++ records36927_36928
theorem aligned36926_36928 :
    AlignedValid 12 4 missing36926_36928 records36926_36928 :=
  aligned36926_36927.append aligned36927_36928

def missing36924_36928 : List (BitVec (edgeCount 12)) :=
  missing36924_36926 ++ missing36926_36928
abbrev records36924_36928 : List Blob :=
  records36924_36926 ++ records36926_36928
theorem aligned36924_36928 :
    AlignedValid 12 4 missing36924_36928 records36924_36928 :=
  aligned36924_36926.append aligned36926_36928

def missing36920_36928 : List (BitVec (edgeCount 12)) :=
  missing36920_36924 ++ missing36924_36928
abbrev records36920_36928 : List Blob :=
  records36920_36924 ++ records36924_36928
theorem aligned36920_36928 :
    AlignedValid 12 4 missing36920_36928 records36920_36928 :=
  aligned36920_36924.append aligned36924_36928

def missing36912_36928 : List (BitVec (edgeCount 12)) :=
  missing36912_36920 ++ missing36920_36928
abbrev records36912_36928 : List Blob :=
  records36912_36920 ++ records36920_36928
theorem aligned36912_36928 :
    AlignedValid 12 4 missing36912_36928 records36912_36928 :=
  aligned36912_36920.append aligned36920_36928

def missing36896_36928 : List (BitVec (edgeCount 12)) :=
  missing36896_36912 ++ missing36912_36928
abbrev records36896_36928 : List Blob :=
  records36896_36912 ++ records36912_36928
theorem aligned36896_36928 :
    AlignedValid 12 4 missing36896_36928 records36896_36928 :=
  aligned36896_36912.append aligned36912_36928

def missing36864_36928 : List (BitVec (edgeCount 12)) :=
  missing36864_36896 ++ missing36896_36928
abbrev records36864_36928 : List Blob :=
  records36864_36896 ++ records36896_36928
theorem aligned36864_36928 :
    AlignedValid 12 4 missing36864_36928 records36864_36928 :=
  aligned36864_36896.append aligned36896_36928

def missing36928_36929 : List (BitVec (edgeCount 12)) :=
  [missing36928]
abbrev records36928_36929 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36928]
theorem aligned36928_36929 :
    AlignedValid 12 4 missing36928_36929 records36928_36929 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36928
    maskCheck36928 AlignedValid.nil

def missing36929_36930 : List (BitVec (edgeCount 12)) :=
  [missing36929]
abbrev records36929_36930 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36929]
theorem aligned36929_36930 :
    AlignedValid 12 4 missing36929_36930 records36929_36930 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36929
    maskCheck36929 AlignedValid.nil

def missing36928_36930 : List (BitVec (edgeCount 12)) :=
  missing36928_36929 ++ missing36929_36930
abbrev records36928_36930 : List Blob :=
  records36928_36929 ++ records36929_36930
theorem aligned36928_36930 :
    AlignedValid 12 4 missing36928_36930 records36928_36930 :=
  aligned36928_36929.append aligned36929_36930

def missing36930_36931 : List (BitVec (edgeCount 12)) :=
  [missing36930]
abbrev records36930_36931 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36930]
theorem aligned36930_36931 :
    AlignedValid 12 4 missing36930_36931 records36930_36931 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36930
    maskCheck36930 AlignedValid.nil

def missing36931_36932 : List (BitVec (edgeCount 12)) :=
  [missing36931]
abbrev records36931_36932 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36931]
theorem aligned36931_36932 :
    AlignedValid 12 4 missing36931_36932 records36931_36932 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36931
    maskCheck36931 AlignedValid.nil

def missing36930_36932 : List (BitVec (edgeCount 12)) :=
  missing36930_36931 ++ missing36931_36932
abbrev records36930_36932 : List Blob :=
  records36930_36931 ++ records36931_36932
theorem aligned36930_36932 :
    AlignedValid 12 4 missing36930_36932 records36930_36932 :=
  aligned36930_36931.append aligned36931_36932

def missing36928_36932 : List (BitVec (edgeCount 12)) :=
  missing36928_36930 ++ missing36930_36932
abbrev records36928_36932 : List Blob :=
  records36928_36930 ++ records36930_36932
theorem aligned36928_36932 :
    AlignedValid 12 4 missing36928_36932 records36928_36932 :=
  aligned36928_36930.append aligned36930_36932

def missing36932_36933 : List (BitVec (edgeCount 12)) :=
  [missing36932]
abbrev records36932_36933 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36932]
theorem aligned36932_36933 :
    AlignedValid 12 4 missing36932_36933 records36932_36933 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36932
    maskCheck36932 AlignedValid.nil

def missing36933_36934 : List (BitVec (edgeCount 12)) :=
  [missing36933]
abbrev records36933_36934 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36933]
theorem aligned36933_36934 :
    AlignedValid 12 4 missing36933_36934 records36933_36934 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36933
    maskCheck36933 AlignedValid.nil

def missing36932_36934 : List (BitVec (edgeCount 12)) :=
  missing36932_36933 ++ missing36933_36934
abbrev records36932_36934 : List Blob :=
  records36932_36933 ++ records36933_36934
theorem aligned36932_36934 :
    AlignedValid 12 4 missing36932_36934 records36932_36934 :=
  aligned36932_36933.append aligned36933_36934

def missing36934_36935 : List (BitVec (edgeCount 12)) :=
  [missing36934]
abbrev records36934_36935 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36934]
theorem aligned36934_36935 :
    AlignedValid 12 4 missing36934_36935 records36934_36935 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36934
    maskCheck36934 AlignedValid.nil

def missing36935_36936 : List (BitVec (edgeCount 12)) :=
  [missing36935]
abbrev records36935_36936 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36935]
theorem aligned36935_36936 :
    AlignedValid 12 4 missing36935_36936 records36935_36936 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36935
    maskCheck36935 AlignedValid.nil

def missing36934_36936 : List (BitVec (edgeCount 12)) :=
  missing36934_36935 ++ missing36935_36936
abbrev records36934_36936 : List Blob :=
  records36934_36935 ++ records36935_36936
theorem aligned36934_36936 :
    AlignedValid 12 4 missing36934_36936 records36934_36936 :=
  aligned36934_36935.append aligned36935_36936

def missing36932_36936 : List (BitVec (edgeCount 12)) :=
  missing36932_36934 ++ missing36934_36936
abbrev records36932_36936 : List Blob :=
  records36932_36934 ++ records36934_36936
theorem aligned36932_36936 :
    AlignedValid 12 4 missing36932_36936 records36932_36936 :=
  aligned36932_36934.append aligned36934_36936

def missing36928_36936 : List (BitVec (edgeCount 12)) :=
  missing36928_36932 ++ missing36932_36936
abbrev records36928_36936 : List Blob :=
  records36928_36932 ++ records36932_36936
theorem aligned36928_36936 :
    AlignedValid 12 4 missing36928_36936 records36928_36936 :=
  aligned36928_36932.append aligned36932_36936

def missing36936_36937 : List (BitVec (edgeCount 12)) :=
  [missing36936]
abbrev records36936_36937 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36936]
theorem aligned36936_36937 :
    AlignedValid 12 4 missing36936_36937 records36936_36937 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36936
    maskCheck36936 AlignedValid.nil

def missing36937_36938 : List (BitVec (edgeCount 12)) :=
  [missing36937]
abbrev records36937_36938 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36937]
theorem aligned36937_36938 :
    AlignedValid 12 4 missing36937_36938 records36937_36938 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36937
    maskCheck36937 AlignedValid.nil

def missing36936_36938 : List (BitVec (edgeCount 12)) :=
  missing36936_36937 ++ missing36937_36938
abbrev records36936_36938 : List Blob :=
  records36936_36937 ++ records36937_36938
theorem aligned36936_36938 :
    AlignedValid 12 4 missing36936_36938 records36936_36938 :=
  aligned36936_36937.append aligned36937_36938

def missing36938_36939 : List (BitVec (edgeCount 12)) :=
  [missing36938]
abbrev records36938_36939 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36938]
theorem aligned36938_36939 :
    AlignedValid 12 4 missing36938_36939 records36938_36939 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36938
    maskCheck36938 AlignedValid.nil

def missing36939_36940 : List (BitVec (edgeCount 12)) :=
  [missing36939]
abbrev records36939_36940 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36939]
theorem aligned36939_36940 :
    AlignedValid 12 4 missing36939_36940 records36939_36940 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36939
    maskCheck36939 AlignedValid.nil

def missing36938_36940 : List (BitVec (edgeCount 12)) :=
  missing36938_36939 ++ missing36939_36940
abbrev records36938_36940 : List Blob :=
  records36938_36939 ++ records36939_36940
theorem aligned36938_36940 :
    AlignedValid 12 4 missing36938_36940 records36938_36940 :=
  aligned36938_36939.append aligned36939_36940

def missing36936_36940 : List (BitVec (edgeCount 12)) :=
  missing36936_36938 ++ missing36938_36940
abbrev records36936_36940 : List Blob :=
  records36936_36938 ++ records36938_36940
theorem aligned36936_36940 :
    AlignedValid 12 4 missing36936_36940 records36936_36940 :=
  aligned36936_36938.append aligned36938_36940

def missing36940_36941 : List (BitVec (edgeCount 12)) :=
  [missing36940]
abbrev records36940_36941 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36940]
theorem aligned36940_36941 :
    AlignedValid 12 4 missing36940_36941 records36940_36941 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36940
    maskCheck36940 AlignedValid.nil

def missing36941_36942 : List (BitVec (edgeCount 12)) :=
  [missing36941]
abbrev records36941_36942 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36941]
theorem aligned36941_36942 :
    AlignedValid 12 4 missing36941_36942 records36941_36942 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36941
    maskCheck36941 AlignedValid.nil

def missing36940_36942 : List (BitVec (edgeCount 12)) :=
  missing36940_36941 ++ missing36941_36942
abbrev records36940_36942 : List Blob :=
  records36940_36941 ++ records36941_36942
theorem aligned36940_36942 :
    AlignedValid 12 4 missing36940_36942 records36940_36942 :=
  aligned36940_36941.append aligned36941_36942

def missing36942_36943 : List (BitVec (edgeCount 12)) :=
  [missing36942]
abbrev records36942_36943 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36942]
theorem aligned36942_36943 :
    AlignedValid 12 4 missing36942_36943 records36942_36943 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36942
    maskCheck36942 AlignedValid.nil

def missing36943_36944 : List (BitVec (edgeCount 12)) :=
  [missing36943]
abbrev records36943_36944 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36943]
theorem aligned36943_36944 :
    AlignedValid 12 4 missing36943_36944 records36943_36944 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36943
    maskCheck36943 AlignedValid.nil

def missing36942_36944 : List (BitVec (edgeCount 12)) :=
  missing36942_36943 ++ missing36943_36944
abbrev records36942_36944 : List Blob :=
  records36942_36943 ++ records36943_36944
theorem aligned36942_36944 :
    AlignedValid 12 4 missing36942_36944 records36942_36944 :=
  aligned36942_36943.append aligned36943_36944

def missing36940_36944 : List (BitVec (edgeCount 12)) :=
  missing36940_36942 ++ missing36942_36944
abbrev records36940_36944 : List Blob :=
  records36940_36942 ++ records36942_36944
theorem aligned36940_36944 :
    AlignedValid 12 4 missing36940_36944 records36940_36944 :=
  aligned36940_36942.append aligned36942_36944

def missing36936_36944 : List (BitVec (edgeCount 12)) :=
  missing36936_36940 ++ missing36940_36944
abbrev records36936_36944 : List Blob :=
  records36936_36940 ++ records36940_36944
theorem aligned36936_36944 :
    AlignedValid 12 4 missing36936_36944 records36936_36944 :=
  aligned36936_36940.append aligned36940_36944

def missing36928_36944 : List (BitVec (edgeCount 12)) :=
  missing36928_36936 ++ missing36936_36944
abbrev records36928_36944 : List Blob :=
  records36928_36936 ++ records36936_36944
theorem aligned36928_36944 :
    AlignedValid 12 4 missing36928_36944 records36928_36944 :=
  aligned36928_36936.append aligned36936_36944

def missing36944_36945 : List (BitVec (edgeCount 12)) :=
  [missing36944]
abbrev records36944_36945 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36944]
theorem aligned36944_36945 :
    AlignedValid 12 4 missing36944_36945 records36944_36945 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36944
    maskCheck36944 AlignedValid.nil

def missing36945_36946 : List (BitVec (edgeCount 12)) :=
  [missing36945]
abbrev records36945_36946 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36945]
theorem aligned36945_36946 :
    AlignedValid 12 4 missing36945_36946 records36945_36946 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36945
    maskCheck36945 AlignedValid.nil

def missing36944_36946 : List (BitVec (edgeCount 12)) :=
  missing36944_36945 ++ missing36945_36946
abbrev records36944_36946 : List Blob :=
  records36944_36945 ++ records36945_36946
theorem aligned36944_36946 :
    AlignedValid 12 4 missing36944_36946 records36944_36946 :=
  aligned36944_36945.append aligned36945_36946

def missing36946_36947 : List (BitVec (edgeCount 12)) :=
  [missing36946]
abbrev records36946_36947 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36946]
theorem aligned36946_36947 :
    AlignedValid 12 4 missing36946_36947 records36946_36947 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36946
    maskCheck36946 AlignedValid.nil

def missing36947_36948 : List (BitVec (edgeCount 12)) :=
  [missing36947]
abbrev records36947_36948 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36947]
theorem aligned36947_36948 :
    AlignedValid 12 4 missing36947_36948 records36947_36948 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36947
    maskCheck36947 AlignedValid.nil

def missing36946_36948 : List (BitVec (edgeCount 12)) :=
  missing36946_36947 ++ missing36947_36948
abbrev records36946_36948 : List Blob :=
  records36946_36947 ++ records36947_36948
theorem aligned36946_36948 :
    AlignedValid 12 4 missing36946_36948 records36946_36948 :=
  aligned36946_36947.append aligned36947_36948

def missing36944_36948 : List (BitVec (edgeCount 12)) :=
  missing36944_36946 ++ missing36946_36948
abbrev records36944_36948 : List Blob :=
  records36944_36946 ++ records36946_36948
theorem aligned36944_36948 :
    AlignedValid 12 4 missing36944_36948 records36944_36948 :=
  aligned36944_36946.append aligned36946_36948

def missing36948_36949 : List (BitVec (edgeCount 12)) :=
  [missing36948]
abbrev records36948_36949 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36948]
theorem aligned36948_36949 :
    AlignedValid 12 4 missing36948_36949 records36948_36949 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36948
    maskCheck36948 AlignedValid.nil

def missing36949_36950 : List (BitVec (edgeCount 12)) :=
  [missing36949]
abbrev records36949_36950 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36949]
theorem aligned36949_36950 :
    AlignedValid 12 4 missing36949_36950 records36949_36950 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36949
    maskCheck36949 AlignedValid.nil

def missing36948_36950 : List (BitVec (edgeCount 12)) :=
  missing36948_36949 ++ missing36949_36950
abbrev records36948_36950 : List Blob :=
  records36948_36949 ++ records36949_36950
theorem aligned36948_36950 :
    AlignedValid 12 4 missing36948_36950 records36948_36950 :=
  aligned36948_36949.append aligned36949_36950

def missing36950_36951 : List (BitVec (edgeCount 12)) :=
  [missing36950]
abbrev records36950_36951 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36950]
theorem aligned36950_36951 :
    AlignedValid 12 4 missing36950_36951 records36950_36951 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36950
    maskCheck36950 AlignedValid.nil

def missing36951_36952 : List (BitVec (edgeCount 12)) :=
  [missing36951]
abbrev records36951_36952 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36951]
theorem aligned36951_36952 :
    AlignedValid 12 4 missing36951_36952 records36951_36952 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36951
    maskCheck36951 AlignedValid.nil

def missing36950_36952 : List (BitVec (edgeCount 12)) :=
  missing36950_36951 ++ missing36951_36952
abbrev records36950_36952 : List Blob :=
  records36950_36951 ++ records36951_36952
theorem aligned36950_36952 :
    AlignedValid 12 4 missing36950_36952 records36950_36952 :=
  aligned36950_36951.append aligned36951_36952

def missing36948_36952 : List (BitVec (edgeCount 12)) :=
  missing36948_36950 ++ missing36950_36952
abbrev records36948_36952 : List Blob :=
  records36948_36950 ++ records36950_36952
theorem aligned36948_36952 :
    AlignedValid 12 4 missing36948_36952 records36948_36952 :=
  aligned36948_36950.append aligned36950_36952

def missing36944_36952 : List (BitVec (edgeCount 12)) :=
  missing36944_36948 ++ missing36948_36952
abbrev records36944_36952 : List Blob :=
  records36944_36948 ++ records36948_36952
theorem aligned36944_36952 :
    AlignedValid 12 4 missing36944_36952 records36944_36952 :=
  aligned36944_36948.append aligned36948_36952

def missing36952_36953 : List (BitVec (edgeCount 12)) :=
  [missing36952]
abbrev records36952_36953 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36952]
theorem aligned36952_36953 :
    AlignedValid 12 4 missing36952_36953 records36952_36953 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36952
    maskCheck36952 AlignedValid.nil

def missing36953_36954 : List (BitVec (edgeCount 12)) :=
  [missing36953]
abbrev records36953_36954 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36953]
theorem aligned36953_36954 :
    AlignedValid 12 4 missing36953_36954 records36953_36954 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36953
    maskCheck36953 AlignedValid.nil

def missing36952_36954 : List (BitVec (edgeCount 12)) :=
  missing36952_36953 ++ missing36953_36954
abbrev records36952_36954 : List Blob :=
  records36952_36953 ++ records36953_36954
theorem aligned36952_36954 :
    AlignedValid 12 4 missing36952_36954 records36952_36954 :=
  aligned36952_36953.append aligned36953_36954

def missing36954_36955 : List (BitVec (edgeCount 12)) :=
  [missing36954]
abbrev records36954_36955 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36954]
theorem aligned36954_36955 :
    AlignedValid 12 4 missing36954_36955 records36954_36955 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36954
    maskCheck36954 AlignedValid.nil

def missing36955_36956 : List (BitVec (edgeCount 12)) :=
  [missing36955]
abbrev records36955_36956 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36955]
theorem aligned36955_36956 :
    AlignedValid 12 4 missing36955_36956 records36955_36956 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36955
    maskCheck36955 AlignedValid.nil

def missing36954_36956 : List (BitVec (edgeCount 12)) :=
  missing36954_36955 ++ missing36955_36956
abbrev records36954_36956 : List Blob :=
  records36954_36955 ++ records36955_36956
theorem aligned36954_36956 :
    AlignedValid 12 4 missing36954_36956 records36954_36956 :=
  aligned36954_36955.append aligned36955_36956

def missing36952_36956 : List (BitVec (edgeCount 12)) :=
  missing36952_36954 ++ missing36954_36956
abbrev records36952_36956 : List Blob :=
  records36952_36954 ++ records36954_36956
theorem aligned36952_36956 :
    AlignedValid 12 4 missing36952_36956 records36952_36956 :=
  aligned36952_36954.append aligned36954_36956

def missing36956_36957 : List (BitVec (edgeCount 12)) :=
  [missing36956]
abbrev records36956_36957 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36956]
theorem aligned36956_36957 :
    AlignedValid 12 4 missing36956_36957 records36956_36957 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36956
    maskCheck36956 AlignedValid.nil

def missing36957_36958 : List (BitVec (edgeCount 12)) :=
  [missing36957]
abbrev records36957_36958 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36957]
theorem aligned36957_36958 :
    AlignedValid 12 4 missing36957_36958 records36957_36958 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36957
    maskCheck36957 AlignedValid.nil

def missing36956_36958 : List (BitVec (edgeCount 12)) :=
  missing36956_36957 ++ missing36957_36958
abbrev records36956_36958 : List Blob :=
  records36956_36957 ++ records36957_36958
theorem aligned36956_36958 :
    AlignedValid 12 4 missing36956_36958 records36956_36958 :=
  aligned36956_36957.append aligned36957_36958

def missing36958_36959 : List (BitVec (edgeCount 12)) :=
  [missing36958]
abbrev records36958_36959 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36958]
theorem aligned36958_36959 :
    AlignedValid 12 4 missing36958_36959 records36958_36959 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36958
    maskCheck36958 AlignedValid.nil

def missing36959_36960 : List (BitVec (edgeCount 12)) :=
  [missing36959]
abbrev records36959_36960 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36959]
theorem aligned36959_36960 :
    AlignedValid 12 4 missing36959_36960 records36959_36960 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36959
    maskCheck36959 AlignedValid.nil

def missing36958_36960 : List (BitVec (edgeCount 12)) :=
  missing36958_36959 ++ missing36959_36960
abbrev records36958_36960 : List Blob :=
  records36958_36959 ++ records36959_36960
theorem aligned36958_36960 :
    AlignedValid 12 4 missing36958_36960 records36958_36960 :=
  aligned36958_36959.append aligned36959_36960

def missing36956_36960 : List (BitVec (edgeCount 12)) :=
  missing36956_36958 ++ missing36958_36960
abbrev records36956_36960 : List Blob :=
  records36956_36958 ++ records36958_36960
theorem aligned36956_36960 :
    AlignedValid 12 4 missing36956_36960 records36956_36960 :=
  aligned36956_36958.append aligned36958_36960

def missing36952_36960 : List (BitVec (edgeCount 12)) :=
  missing36952_36956 ++ missing36956_36960
abbrev records36952_36960 : List Blob :=
  records36952_36956 ++ records36956_36960
theorem aligned36952_36960 :
    AlignedValid 12 4 missing36952_36960 records36952_36960 :=
  aligned36952_36956.append aligned36956_36960

def missing36944_36960 : List (BitVec (edgeCount 12)) :=
  missing36944_36952 ++ missing36952_36960
abbrev records36944_36960 : List Blob :=
  records36944_36952 ++ records36952_36960
theorem aligned36944_36960 :
    AlignedValid 12 4 missing36944_36960 records36944_36960 :=
  aligned36944_36952.append aligned36952_36960

def missing36928_36960 : List (BitVec (edgeCount 12)) :=
  missing36928_36944 ++ missing36944_36960
abbrev records36928_36960 : List Blob :=
  records36928_36944 ++ records36944_36960
theorem aligned36928_36960 :
    AlignedValid 12 4 missing36928_36960 records36928_36960 :=
  aligned36928_36944.append aligned36944_36960

def missing36960_36961 : List (BitVec (edgeCount 12)) :=
  [missing36960]
abbrev records36960_36961 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36960]
theorem aligned36960_36961 :
    AlignedValid 12 4 missing36960_36961 records36960_36961 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36960
    maskCheck36960 AlignedValid.nil

def missing36961_36962 : List (BitVec (edgeCount 12)) :=
  [missing36961]
abbrev records36961_36962 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36961]
theorem aligned36961_36962 :
    AlignedValid 12 4 missing36961_36962 records36961_36962 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36961
    maskCheck36961 AlignedValid.nil

def missing36960_36962 : List (BitVec (edgeCount 12)) :=
  missing36960_36961 ++ missing36961_36962
abbrev records36960_36962 : List Blob :=
  records36960_36961 ++ records36961_36962
theorem aligned36960_36962 :
    AlignedValid 12 4 missing36960_36962 records36960_36962 :=
  aligned36960_36961.append aligned36961_36962

def missing36962_36963 : List (BitVec (edgeCount 12)) :=
  [missing36962]
abbrev records36962_36963 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36962]
theorem aligned36962_36963 :
    AlignedValid 12 4 missing36962_36963 records36962_36963 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36962
    maskCheck36962 AlignedValid.nil

def missing36963_36964 : List (BitVec (edgeCount 12)) :=
  [missing36963]
abbrev records36963_36964 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36963]
theorem aligned36963_36964 :
    AlignedValid 12 4 missing36963_36964 records36963_36964 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36963
    maskCheck36963 AlignedValid.nil

def missing36962_36964 : List (BitVec (edgeCount 12)) :=
  missing36962_36963 ++ missing36963_36964
abbrev records36962_36964 : List Blob :=
  records36962_36963 ++ records36963_36964
theorem aligned36962_36964 :
    AlignedValid 12 4 missing36962_36964 records36962_36964 :=
  aligned36962_36963.append aligned36963_36964

def missing36960_36964 : List (BitVec (edgeCount 12)) :=
  missing36960_36962 ++ missing36962_36964
abbrev records36960_36964 : List Blob :=
  records36960_36962 ++ records36962_36964
theorem aligned36960_36964 :
    AlignedValid 12 4 missing36960_36964 records36960_36964 :=
  aligned36960_36962.append aligned36962_36964

def missing36964_36965 : List (BitVec (edgeCount 12)) :=
  [missing36964]
abbrev records36964_36965 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36964]
theorem aligned36964_36965 :
    AlignedValid 12 4 missing36964_36965 records36964_36965 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36964
    maskCheck36964 AlignedValid.nil

def missing36965_36966 : List (BitVec (edgeCount 12)) :=
  [missing36965]
abbrev records36965_36966 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36965]
theorem aligned36965_36966 :
    AlignedValid 12 4 missing36965_36966 records36965_36966 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36965
    maskCheck36965 AlignedValid.nil

def missing36964_36966 : List (BitVec (edgeCount 12)) :=
  missing36964_36965 ++ missing36965_36966
abbrev records36964_36966 : List Blob :=
  records36964_36965 ++ records36965_36966
theorem aligned36964_36966 :
    AlignedValid 12 4 missing36964_36966 records36964_36966 :=
  aligned36964_36965.append aligned36965_36966

def missing36966_36967 : List (BitVec (edgeCount 12)) :=
  [missing36966]
abbrev records36966_36967 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36966]
theorem aligned36966_36967 :
    AlignedValid 12 4 missing36966_36967 records36966_36967 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36966
    maskCheck36966 AlignedValid.nil

def missing36967_36968 : List (BitVec (edgeCount 12)) :=
  [missing36967]
abbrev records36967_36968 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36967]
theorem aligned36967_36968 :
    AlignedValid 12 4 missing36967_36968 records36967_36968 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36967
    maskCheck36967 AlignedValid.nil

def missing36966_36968 : List (BitVec (edgeCount 12)) :=
  missing36966_36967 ++ missing36967_36968
abbrev records36966_36968 : List Blob :=
  records36966_36967 ++ records36967_36968
theorem aligned36966_36968 :
    AlignedValid 12 4 missing36966_36968 records36966_36968 :=
  aligned36966_36967.append aligned36967_36968

def missing36964_36968 : List (BitVec (edgeCount 12)) :=
  missing36964_36966 ++ missing36966_36968
abbrev records36964_36968 : List Blob :=
  records36964_36966 ++ records36966_36968
theorem aligned36964_36968 :
    AlignedValid 12 4 missing36964_36968 records36964_36968 :=
  aligned36964_36966.append aligned36966_36968

def missing36960_36968 : List (BitVec (edgeCount 12)) :=
  missing36960_36964 ++ missing36964_36968
abbrev records36960_36968 : List Blob :=
  records36960_36964 ++ records36964_36968
theorem aligned36960_36968 :
    AlignedValid 12 4 missing36960_36968 records36960_36968 :=
  aligned36960_36964.append aligned36964_36968

def missing36968_36969 : List (BitVec (edgeCount 12)) :=
  [missing36968]
abbrev records36968_36969 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36968]
theorem aligned36968_36969 :
    AlignedValid 12 4 missing36968_36969 records36968_36969 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36968
    maskCheck36968 AlignedValid.nil

def missing36969_36970 : List (BitVec (edgeCount 12)) :=
  [missing36969]
abbrev records36969_36970 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36969]
theorem aligned36969_36970 :
    AlignedValid 12 4 missing36969_36970 records36969_36970 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36969
    maskCheck36969 AlignedValid.nil

def missing36968_36970 : List (BitVec (edgeCount 12)) :=
  missing36968_36969 ++ missing36969_36970
abbrev records36968_36970 : List Blob :=
  records36968_36969 ++ records36969_36970
theorem aligned36968_36970 :
    AlignedValid 12 4 missing36968_36970 records36968_36970 :=
  aligned36968_36969.append aligned36969_36970

def missing36970_36971 : List (BitVec (edgeCount 12)) :=
  [missing36970]
abbrev records36970_36971 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36970]
theorem aligned36970_36971 :
    AlignedValid 12 4 missing36970_36971 records36970_36971 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36970
    maskCheck36970 AlignedValid.nil

def missing36971_36972 : List (BitVec (edgeCount 12)) :=
  [missing36971]
abbrev records36971_36972 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36971]
theorem aligned36971_36972 :
    AlignedValid 12 4 missing36971_36972 records36971_36972 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36971
    maskCheck36971 AlignedValid.nil

def missing36970_36972 : List (BitVec (edgeCount 12)) :=
  missing36970_36971 ++ missing36971_36972
abbrev records36970_36972 : List Blob :=
  records36970_36971 ++ records36971_36972
theorem aligned36970_36972 :
    AlignedValid 12 4 missing36970_36972 records36970_36972 :=
  aligned36970_36971.append aligned36971_36972

def missing36968_36972 : List (BitVec (edgeCount 12)) :=
  missing36968_36970 ++ missing36970_36972
abbrev records36968_36972 : List Blob :=
  records36968_36970 ++ records36970_36972
theorem aligned36968_36972 :
    AlignedValid 12 4 missing36968_36972 records36968_36972 :=
  aligned36968_36970.append aligned36970_36972

def missing36972_36973 : List (BitVec (edgeCount 12)) :=
  [missing36972]
abbrev records36972_36973 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36972]
theorem aligned36972_36973 :
    AlignedValid 12 4 missing36972_36973 records36972_36973 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36972
    maskCheck36972 AlignedValid.nil

def missing36973_36974 : List (BitVec (edgeCount 12)) :=
  [missing36973]
abbrev records36973_36974 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36973]
theorem aligned36973_36974 :
    AlignedValid 12 4 missing36973_36974 records36973_36974 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36973
    maskCheck36973 AlignedValid.nil

def missing36972_36974 : List (BitVec (edgeCount 12)) :=
  missing36972_36973 ++ missing36973_36974
abbrev records36972_36974 : List Blob :=
  records36972_36973 ++ records36973_36974
theorem aligned36972_36974 :
    AlignedValid 12 4 missing36972_36974 records36972_36974 :=
  aligned36972_36973.append aligned36973_36974

def missing36974_36975 : List (BitVec (edgeCount 12)) :=
  [missing36974]
abbrev records36974_36975 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36974]
theorem aligned36974_36975 :
    AlignedValid 12 4 missing36974_36975 records36974_36975 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36974
    maskCheck36974 AlignedValid.nil

def missing36975_36976 : List (BitVec (edgeCount 12)) :=
  [missing36975]
abbrev records36975_36976 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36975]
theorem aligned36975_36976 :
    AlignedValid 12 4 missing36975_36976 records36975_36976 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36975
    maskCheck36975 AlignedValid.nil

def missing36974_36976 : List (BitVec (edgeCount 12)) :=
  missing36974_36975 ++ missing36975_36976
abbrev records36974_36976 : List Blob :=
  records36974_36975 ++ records36975_36976
theorem aligned36974_36976 :
    AlignedValid 12 4 missing36974_36976 records36974_36976 :=
  aligned36974_36975.append aligned36975_36976

def missing36972_36976 : List (BitVec (edgeCount 12)) :=
  missing36972_36974 ++ missing36974_36976
abbrev records36972_36976 : List Blob :=
  records36972_36974 ++ records36974_36976
theorem aligned36972_36976 :
    AlignedValid 12 4 missing36972_36976 records36972_36976 :=
  aligned36972_36974.append aligned36974_36976

def missing36968_36976 : List (BitVec (edgeCount 12)) :=
  missing36968_36972 ++ missing36972_36976
abbrev records36968_36976 : List Blob :=
  records36968_36972 ++ records36972_36976
theorem aligned36968_36976 :
    AlignedValid 12 4 missing36968_36976 records36968_36976 :=
  aligned36968_36972.append aligned36972_36976

def missing36960_36976 : List (BitVec (edgeCount 12)) :=
  missing36960_36968 ++ missing36968_36976
abbrev records36960_36976 : List Blob :=
  records36960_36968 ++ records36968_36976
theorem aligned36960_36976 :
    AlignedValid 12 4 missing36960_36976 records36960_36976 :=
  aligned36960_36968.append aligned36968_36976

def missing36976_36977 : List (BitVec (edgeCount 12)) :=
  [missing36976]
abbrev records36976_36977 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36976]
theorem aligned36976_36977 :
    AlignedValid 12 4 missing36976_36977 records36976_36977 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36976
    maskCheck36976 AlignedValid.nil

def missing36977_36978 : List (BitVec (edgeCount 12)) :=
  [missing36977]
abbrev records36977_36978 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36977]
theorem aligned36977_36978 :
    AlignedValid 12 4 missing36977_36978 records36977_36978 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36977
    maskCheck36977 AlignedValid.nil

def missing36976_36978 : List (BitVec (edgeCount 12)) :=
  missing36976_36977 ++ missing36977_36978
abbrev records36976_36978 : List Blob :=
  records36976_36977 ++ records36977_36978
theorem aligned36976_36978 :
    AlignedValid 12 4 missing36976_36978 records36976_36978 :=
  aligned36976_36977.append aligned36977_36978

def missing36978_36979 : List (BitVec (edgeCount 12)) :=
  [missing36978]
abbrev records36978_36979 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36978]
theorem aligned36978_36979 :
    AlignedValid 12 4 missing36978_36979 records36978_36979 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36978
    maskCheck36978 AlignedValid.nil

def missing36979_36980 : List (BitVec (edgeCount 12)) :=
  [missing36979]
abbrev records36979_36980 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36979]
theorem aligned36979_36980 :
    AlignedValid 12 4 missing36979_36980 records36979_36980 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36979
    maskCheck36979 AlignedValid.nil

def missing36978_36980 : List (BitVec (edgeCount 12)) :=
  missing36978_36979 ++ missing36979_36980
abbrev records36978_36980 : List Blob :=
  records36978_36979 ++ records36979_36980
theorem aligned36978_36980 :
    AlignedValid 12 4 missing36978_36980 records36978_36980 :=
  aligned36978_36979.append aligned36979_36980

def missing36976_36980 : List (BitVec (edgeCount 12)) :=
  missing36976_36978 ++ missing36978_36980
abbrev records36976_36980 : List Blob :=
  records36976_36978 ++ records36978_36980
theorem aligned36976_36980 :
    AlignedValid 12 4 missing36976_36980 records36976_36980 :=
  aligned36976_36978.append aligned36978_36980

def missing36980_36981 : List (BitVec (edgeCount 12)) :=
  [missing36980]
abbrev records36980_36981 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36980]
theorem aligned36980_36981 :
    AlignedValid 12 4 missing36980_36981 records36980_36981 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36980
    maskCheck36980 AlignedValid.nil

def missing36981_36982 : List (BitVec (edgeCount 12)) :=
  [missing36981]
abbrev records36981_36982 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36981]
theorem aligned36981_36982 :
    AlignedValid 12 4 missing36981_36982 records36981_36982 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36981
    maskCheck36981 AlignedValid.nil

def missing36980_36982 : List (BitVec (edgeCount 12)) :=
  missing36980_36981 ++ missing36981_36982
abbrev records36980_36982 : List Blob :=
  records36980_36981 ++ records36981_36982
theorem aligned36980_36982 :
    AlignedValid 12 4 missing36980_36982 records36980_36982 :=
  aligned36980_36981.append aligned36981_36982

def missing36982_36983 : List (BitVec (edgeCount 12)) :=
  [missing36982]
abbrev records36982_36983 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36982]
theorem aligned36982_36983 :
    AlignedValid 12 4 missing36982_36983 records36982_36983 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36982
    maskCheck36982 AlignedValid.nil

def missing36983_36984 : List (BitVec (edgeCount 12)) :=
  [missing36983]
abbrev records36983_36984 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36983]
theorem aligned36983_36984 :
    AlignedValid 12 4 missing36983_36984 records36983_36984 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36983
    maskCheck36983 AlignedValid.nil

def missing36982_36984 : List (BitVec (edgeCount 12)) :=
  missing36982_36983 ++ missing36983_36984
abbrev records36982_36984 : List Blob :=
  records36982_36983 ++ records36983_36984
theorem aligned36982_36984 :
    AlignedValid 12 4 missing36982_36984 records36982_36984 :=
  aligned36982_36983.append aligned36983_36984

def missing36980_36984 : List (BitVec (edgeCount 12)) :=
  missing36980_36982 ++ missing36982_36984
abbrev records36980_36984 : List Blob :=
  records36980_36982 ++ records36982_36984
theorem aligned36980_36984 :
    AlignedValid 12 4 missing36980_36984 records36980_36984 :=
  aligned36980_36982.append aligned36982_36984

def missing36976_36984 : List (BitVec (edgeCount 12)) :=
  missing36976_36980 ++ missing36980_36984
abbrev records36976_36984 : List Blob :=
  records36976_36980 ++ records36980_36984
theorem aligned36976_36984 :
    AlignedValid 12 4 missing36976_36984 records36976_36984 :=
  aligned36976_36980.append aligned36980_36984

def missing36984_36985 : List (BitVec (edgeCount 12)) :=
  [missing36984]
abbrev records36984_36985 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36984]
theorem aligned36984_36985 :
    AlignedValid 12 4 missing36984_36985 records36984_36985 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36984
    maskCheck36984 AlignedValid.nil

def missing36985_36986 : List (BitVec (edgeCount 12)) :=
  [missing36985]
abbrev records36985_36986 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36985]
theorem aligned36985_36986 :
    AlignedValid 12 4 missing36985_36986 records36985_36986 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36985
    maskCheck36985 AlignedValid.nil

def missing36984_36986 : List (BitVec (edgeCount 12)) :=
  missing36984_36985 ++ missing36985_36986
abbrev records36984_36986 : List Blob :=
  records36984_36985 ++ records36985_36986
theorem aligned36984_36986 :
    AlignedValid 12 4 missing36984_36986 records36984_36986 :=
  aligned36984_36985.append aligned36985_36986

def missing36986_36987 : List (BitVec (edgeCount 12)) :=
  [missing36986]
abbrev records36986_36987 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36986]
theorem aligned36986_36987 :
    AlignedValid 12 4 missing36986_36987 records36986_36987 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36986
    maskCheck36986 AlignedValid.nil

def missing36987_36988 : List (BitVec (edgeCount 12)) :=
  [missing36987]
abbrev records36987_36988 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36987]
theorem aligned36987_36988 :
    AlignedValid 12 4 missing36987_36988 records36987_36988 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36987
    maskCheck36987 AlignedValid.nil

def missing36986_36988 : List (BitVec (edgeCount 12)) :=
  missing36986_36987 ++ missing36987_36988
abbrev records36986_36988 : List Blob :=
  records36986_36987 ++ records36987_36988
theorem aligned36986_36988 :
    AlignedValid 12 4 missing36986_36988 records36986_36988 :=
  aligned36986_36987.append aligned36987_36988

def missing36984_36988 : List (BitVec (edgeCount 12)) :=
  missing36984_36986 ++ missing36986_36988
abbrev records36984_36988 : List Blob :=
  records36984_36986 ++ records36986_36988
theorem aligned36984_36988 :
    AlignedValid 12 4 missing36984_36988 records36984_36988 :=
  aligned36984_36986.append aligned36986_36988

def missing36988_36989 : List (BitVec (edgeCount 12)) :=
  [missing36988]
abbrev records36988_36989 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36988]
theorem aligned36988_36989 :
    AlignedValid 12 4 missing36988_36989 records36988_36989 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36988
    maskCheck36988 AlignedValid.nil

def missing36989_36990 : List (BitVec (edgeCount 12)) :=
  [missing36989]
abbrev records36989_36990 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36989]
theorem aligned36989_36990 :
    AlignedValid 12 4 missing36989_36990 records36989_36990 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36989
    maskCheck36989 AlignedValid.nil

def missing36988_36990 : List (BitVec (edgeCount 12)) :=
  missing36988_36989 ++ missing36989_36990
abbrev records36988_36990 : List Blob :=
  records36988_36989 ++ records36989_36990
theorem aligned36988_36990 :
    AlignedValid 12 4 missing36988_36990 records36988_36990 :=
  aligned36988_36989.append aligned36989_36990

def missing36990_36991 : List (BitVec (edgeCount 12)) :=
  [missing36990]
abbrev records36990_36991 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36990]
theorem aligned36990_36991 :
    AlignedValid 12 4 missing36990_36991 records36990_36991 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36990
    maskCheck36990 AlignedValid.nil

def missing36991_36992 : List (BitVec (edgeCount 12)) :=
  [missing36991]
abbrev records36991_36992 : List Blob :=
  [StrongPackedBucketN12A4Shard288.record36991]
theorem aligned36991_36992 :
    AlignedValid 12 4 missing36991_36992 records36991_36992 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard288.check36991
    maskCheck36991 AlignedValid.nil

def missing36990_36992 : List (BitVec (edgeCount 12)) :=
  missing36990_36991 ++ missing36991_36992
abbrev records36990_36992 : List Blob :=
  records36990_36991 ++ records36991_36992
theorem aligned36990_36992 :
    AlignedValid 12 4 missing36990_36992 records36990_36992 :=
  aligned36990_36991.append aligned36991_36992

def missing36988_36992 : List (BitVec (edgeCount 12)) :=
  missing36988_36990 ++ missing36990_36992
abbrev records36988_36992 : List Blob :=
  records36988_36990 ++ records36990_36992
theorem aligned36988_36992 :
    AlignedValid 12 4 missing36988_36992 records36988_36992 :=
  aligned36988_36990.append aligned36990_36992

def missing36984_36992 : List (BitVec (edgeCount 12)) :=
  missing36984_36988 ++ missing36988_36992
abbrev records36984_36992 : List Blob :=
  records36984_36988 ++ records36988_36992
theorem aligned36984_36992 :
    AlignedValid 12 4 missing36984_36992 records36984_36992 :=
  aligned36984_36988.append aligned36988_36992

def missing36976_36992 : List (BitVec (edgeCount 12)) :=
  missing36976_36984 ++ missing36984_36992
abbrev records36976_36992 : List Blob :=
  records36976_36984 ++ records36984_36992
theorem aligned36976_36992 :
    AlignedValid 12 4 missing36976_36992 records36976_36992 :=
  aligned36976_36984.append aligned36984_36992

def missing36960_36992 : List (BitVec (edgeCount 12)) :=
  missing36960_36976 ++ missing36976_36992
abbrev records36960_36992 : List Blob :=
  records36960_36976 ++ records36976_36992
theorem aligned36960_36992 :
    AlignedValid 12 4 missing36960_36992 records36960_36992 :=
  aligned36960_36976.append aligned36976_36992

def missing36928_36992 : List (BitVec (edgeCount 12)) :=
  missing36928_36960 ++ missing36960_36992
abbrev records36928_36992 : List Blob :=
  records36928_36960 ++ records36960_36992
theorem aligned36928_36992 :
    AlignedValid 12 4 missing36928_36992 records36928_36992 :=
  aligned36928_36960.append aligned36960_36992

def missing36864_36992 : List (BitVec (edgeCount 12)) :=
  missing36864_36928 ++ missing36928_36992
abbrev records36864_36992 : List Blob :=
  records36864_36928 ++ records36928_36992
theorem aligned36864_36992 :
    AlignedValid 12 4 missing36864_36992 records36864_36992 :=
  aligned36864_36928.append aligned36928_36992

abbrev missing : List (BitVec (edgeCount 12)) := missing36864_36992
abbrev records : List Blob := records36864_36992
theorem aligned : AlignedValid 12 4 missing records := aligned36864_36992

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard288
