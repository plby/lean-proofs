/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A3Shard030

/-! Decode-only alignment checks for n=12, a=3, records 3840--3967. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard030

open PackedBucketCertificate

def missing3840 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19212462525819912192
theorem maskCheck3840 :
    checkMaskFor missing3840 StrongPackedBucketN12A3Shard030.record3840 = true := by
  decide

def missing3841 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19248491322838876160
theorem maskCheck3841 :
    checkMaskFor missing3841 StrongPackedBucketN12A3Shard030.record3841 = true := by
  decide

def missing3842 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19464664104952659968
theorem maskCheck3842 :
    checkMaskFor missing3842 StrongPackedBucketN12A3Shard030.record3842 = true := by
  decide

def missing3843 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20221268842350903296
theorem maskCheck3843 :
    checkMaskFor missing3843 StrongPackedBucketN12A3Shard030.record3843 = true := by
  decide

def missing3844 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20257297639369867264
theorem maskCheck3844 :
    checkMaskFor missing3844 StrongPackedBucketN12A3Shard030.record3844 = true := by
  decide

def missing3845 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20329355233407795200
theorem maskCheck3845 :
    checkMaskFor missing3845 StrongPackedBucketN12A3Shard030.record3845 = true := by
  decide

def missing3846 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22491083054545633280
theorem maskCheck3846 :
    checkMaskFor missing3846 StrongPackedBucketN12A3Shard030.record3846 = true := by
  decide

def missing3847 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27787316216333336576
theorem maskCheck3847 :
    checkMaskFor missing3847 StrongPackedBucketN12A3Shard030.record3847 = true := by
  decide

def missing3848 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27859373810371264512
theorem maskCheck3848 :
    checkMaskFor missing3848 StrongPackedBucketN12A3Shard030.record3848 = true := by
  decide

def missing3849 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28291719374598832128
theorem maskCheck3849 :
    checkMaskFor missing3849 StrongPackedBucketN12A3Shard030.record3849 = true := by
  decide

def missing3850 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46234060290042888192
theorem maskCheck3850 :
    checkMaskFor missing3850 StrongPackedBucketN12A3Shard030.record3850 = true := by
  decide

def missing3851 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46306117884080816128
theorem maskCheck3851 :
    checkMaskFor missing3851 StrongPackedBucketN12A3Shard030.record3851 = true := by
  decide

def missing3852 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55457432326897664000
theorem maskCheck3852 :
    checkMaskFor missing3852 StrongPackedBucketN12A3Shard030.record3852 = true := by
  decide

def missing3853 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55529489920935591936
theorem maskCheck3853 :
    checkMaskFor missing3853 StrongPackedBucketN12A3Shard030.record3853 = true := by
  decide

def missing3854 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55565518717954555904
theorem maskCheck3854 :
    checkMaskFor missing3854 StrongPackedBucketN12A3Shard030.record3854 = true := by
  decide

def missing3855 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55781691500068339712
theorem maskCheck3855 :
    checkMaskFor missing3855 StrongPackedBucketN12A3Shard030.record3855 = true := by
  decide

def missing3856 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55961835485163159552
theorem maskCheck3856 :
    checkMaskFor missing3856 StrongPackedBucketN12A3Shard030.record3856 = true := by
  decide

def missing3857 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55997864282182123520
theorem maskCheck3857 :
    checkMaskFor missing3857 StrongPackedBucketN12A3Shard030.record3857 = true := by
  decide

def missing3858 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56069921876220051456
theorem maskCheck3858 :
    checkMaskFor missing3858 StrongPackedBucketN12A3Shard030.record3858 = true := by
  decide

def missing3859 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57078728192751042560
theorem maskCheck3859 :
    checkMaskFor missing3859 StrongPackedBucketN12A3Shard030.record3859 = true := by
  decide

def missing3860 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64608746769714511872
theorem maskCheck3860 :
    checkMaskFor missing3860 StrongPackedBucketN12A3Shard030.record3860 = true := by
  decide

def missing3861 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 550038251205820416
theorem maskCheck3861 :
    checkMaskFor missing3861 StrongPackedBucketN12A3Shard030.record3861 = true := by
  decide

def missing3862 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 838268627357532160
theorem maskCheck3862 :
    checkMaskFor missing3862 StrongPackedBucketN12A3Shard030.record3862 = true := by
  decide

def missing3863 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1090470206490279936
theorem maskCheck3863 :
    checkMaskFor missing3863 StrongPackedBucketN12A3Shard030.record3863 = true := by
  decide

def missing3864 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1414729379660955648
theorem maskCheck3864 :
    checkMaskFor missing3864 StrongPackedBucketN12A3Shard030.record3864 = true := by
  decide

def missing3865 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1666930958793703424
theorem maskCheck3865 :
    checkMaskFor missing3865 StrongPackedBucketN12A3Shard030.record3865 = true := by
  decide

def missing3866 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1847074943888523264
theorem maskCheck3866 :
    checkMaskFor missing3866 StrongPackedBucketN12A3Shard030.record3866 = true := by
  decide

def missing3867 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1955161334945415168
theorem maskCheck3867 :
    checkMaskFor missing3867 StrongPackedBucketN12A3Shard030.record3867 = true := by
  decide

def missing3868 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3576457200798793728
theorem maskCheck3868 :
    checkMaskFor missing3868 StrongPackedBucketN12A3Shard030.record3868 = true := by
  decide

def missing3869 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3684543591855685632
theorem maskCheck3869 :
    checkMaskFor missing3869 StrongPackedBucketN12A3Shard030.record3869 = true := by
  decide

def missing3870 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4080860359064289280
theorem maskCheck3870 :
    checkMaskFor missing3870 StrongPackedBucketN12A3Shard030.record3870 = true := by
  decide

def missing3871 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4116889156083253248
theorem maskCheck3871 :
    checkMaskFor missing3871 StrongPackedBucketN12A3Shard030.record3871 = true := by
  decide

def missing3872 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8116085625188253696
theorem maskCheck3872 :
    checkMaskFor missing3872 StrongPackedBucketN12A3Shard030.record3872 = true := by
  decide

def missing3873 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8152114422207217664
theorem maskCheck3873 :
    checkMaskFor missing3873 StrongPackedBucketN12A3Shard030.record3873 = true := by
  decide

def missing3874 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8656517580472713216
theorem maskCheck3874 :
    checkMaskFor missing3874 StrongPackedBucketN12A3Shard030.record3874 = true := by
  decide

def missing3875 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9485179911908884480
theorem maskCheck3875 :
    checkMaskFor missing3875 StrongPackedBucketN12A3Shard030.record3875 = true := by
  decide

def missing3876 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9917525476136452096
theorem maskCheck3876 :
    checkMaskFor missing3876 StrongPackedBucketN12A3Shard030.record3876 = true := by
  decide

def missing3877 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10493986228439875584
theorem maskCheck3877 :
    checkMaskFor missing3877 StrongPackedBucketN12A3Shard030.record3877 = true := by
  decide

def missing3878 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10998389386705371136
theorem maskCheck3878 :
    checkMaskFor missing3878 StrongPackedBucketN12A3Shard030.record3878 = true := by
  decide

def missing3879 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12727771643615641600
theorem maskCheck3879 :
    checkMaskFor missing3879 StrongPackedBucketN12A3Shard030.record3879 = true := by
  decide

def missing3880 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18708551948763660288
theorem maskCheck3880 :
    checkMaskFor missing3880 StrongPackedBucketN12A3Shard030.record3880 = true := by
  decide

def missing3881 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18960753527896408064
theorem maskCheck3881 :
    checkMaskFor missing3881 StrongPackedBucketN12A3Shard030.record3881 = true := by
  decide

def missing3882 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19717358265294651392
theorem maskCheck3882 :
    checkMaskFor missing3882 StrongPackedBucketN12A3Shard030.record3882 = true := by
  decide

def missing3883 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19825444656351543296
theorem maskCheck3883 :
    checkMaskFor missing3883 StrongPackedBucketN12A3Shard030.record3883 = true := by
  decide

def missing3884 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21951143680470417408
theorem maskCheck3884 :
    checkMaskFor missing3884 StrongPackedBucketN12A3Shard030.record3884 = true := by
  decide

def missing3885 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21987172477489381376
theorem maskCheck3885 :
    checkMaskFor missing3885 StrongPackedBucketN12A3Shard030.record3885 = true := by
  decide

def missing3886 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 26526800901878841344
theorem maskCheck3886 :
    checkMaskFor missing3886 StrongPackedBucketN12A3Shard030.record3886 = true := by
  decide

def missing3887 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27787808797542580224
theorem maskCheck3887 :
    checkMaskFor missing3887 StrongPackedBucketN12A3Shard030.record3887 = true := by
  decide

def missing3888 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28868672708111499264
theorem maskCheck3888 :
    checkMaskFor missing3888 StrongPackedBucketN12A3Shard030.record3888 = true := by
  decide

def missing3889 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37155296022473211904
theorem maskCheck3889 :
    checkMaskFor missing3889 StrongPackedBucketN12A3Shard030.record3889 = true := by
  decide

def missing3890 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37407497601605959680
theorem maskCheck3890 :
    checkMaskFor missing3890 StrongPackedBucketN12A3Shard030.record3890 = true := by
  decide

def missing3891 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46234552871252131840
theorem maskCheck3891 :
    checkMaskFor missing3891 StrongPackedBucketN12A3Shard030.record3891 = true := by
  decide

def missing3892 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46738956029517627392
theorem maskCheck3892 :
    checkMaskFor missing3892 StrongPackedBucketN12A3Shard030.record3892 = true := by
  decide

def missing3893 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47315416781821050880
theorem maskCheck3893 :
    checkMaskFor missing3893 StrongPackedBucketN12A3Shard030.record3893 = true := by
  decide

def missing3894 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55457924908106907648
theorem maskCheck3894 :
    checkMaskFor missing3894 StrongPackedBucketN12A3Shard030.record3894 = true := by
  decide

def missing3895 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55566011299163799552
theorem maskCheck3895 :
    checkMaskFor missing3895 StrongPackedBucketN12A3Shard030.record3895 = true := by
  decide

def missing3896 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55962328066372403200
theorem maskCheck3896 :
    checkMaskFor missing3896 StrongPackedBucketN12A3Shard030.record3896 = true := by
  decide

def missing3897 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55998356863391367168
theorem maskCheck3897 :
    checkMaskFor missing3897 StrongPackedBucketN12A3Shard030.record3897 = true := by
  decide

def missing3898 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56538788818675826688
theorem maskCheck3898 :
    checkMaskFor missing3898 StrongPackedBucketN12A3Shard030.record3898 = true := by
  decide

def missing3899 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56574817615694790656
theorem maskCheck3899 :
    checkMaskFor missing3899 StrongPackedBucketN12A3Shard030.record3899 = true := by
  decide

def missing3900 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57079220773960286208
theorem maskCheck3900 :
    checkMaskFor missing3900 StrongPackedBucketN12A3Shard030.record3900 = true := by
  decide

def missing3901 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58808603030870556672
theorem maskCheck3901 :
    checkMaskFor missing3901 StrongPackedBucketN12A3Shard030.record3901 = true := by
  decide

def missing3902 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64609239350923755520
theorem maskCheck3902 :
    checkMaskFor missing3902 StrongPackedBucketN12A3Shard030.record3902 = true := by
  decide

def missing3903 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081127999786450944
theorem maskCheck3903 :
    checkMaskFor missing3903 StrongPackedBucketN12A3Shard030.record3903 = true := by
  decide

def missing3904 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2089934316317442048
theorem maskCheck3904 :
    checkMaskFor missing3904 StrongPackedBucketN12A3Shard030.record3904 = true := by
  decide

def missing3905 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2161991910355369984
theorem maskCheck3905 :
    checkMaskFor missing3905 StrongPackedBucketN12A3Shard030.record3905 = true := by
  decide

def missing3906 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4323719731493208064
theorem maskCheck3906 :
    checkMaskFor missing3906 StrongPackedBucketN12A3Shard030.record3906 = true := by
  decide

def missing3907 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9475837705205055488
theorem maskCheck3907 :
    checkMaskFor missing3907 StrongPackedBucketN12A3Shard030.record3907 = true := by
  decide

def missing3908 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9692010487318839296
theorem maskCheck3908 :
    checkMaskFor missing3908 StrongPackedBucketN12A3Shard030.record3908 = true := by
  decide

def missing3909 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9728039284337803264
theorem maskCheck3909 :
    checkMaskFor missing3909 StrongPackedBucketN12A3Shard030.record3909 = true := by
  decide

def missing3910 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10160384848565370880
theorem maskCheck3910 :
    checkMaskFor missing3910 StrongPackedBucketN12A3Shard030.record3910 = true := by
  decide

def missing3911 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10232442442603298816
theorem maskCheck3911 :
    checkMaskFor missing3911 StrongPackedBucketN12A3Shard030.record3911 = true := by
  decide

def missing3912 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11241248759134289920
theorem maskCheck3912 :
    checkMaskFor missing3912 StrongPackedBucketN12A3Shard030.record3912 = true := by
  decide

def missing3913 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699209742059831296
theorem maskCheck3913 :
    checkMaskFor missing3913 StrongPackedBucketN12A3Shard030.record3913 = true := by
  decide

def missing3914 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18843324930135687168
theorem maskCheck3914 :
    checkMaskFor missing3914 StrongPackedBucketN12A3Shard030.record3914 = true := by
  decide

def missing3915 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18915382524173615104
theorem maskCheck3915 :
    checkMaskFor missing3915 StrongPackedBucketN12A3Shard030.record3915 = true := by
  decide

def missing3916 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18951411321192579072
theorem maskCheck3916 :
    checkMaskFor missing3916 StrongPackedBucketN12A3Shard030.record3916 = true := by
  decide

def missing3917 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27778466590838751232
theorem maskCheck3917 :
    checkMaskFor missing3917 StrongPackedBucketN12A3Shard030.record3917 = true := by
  decide

def missing3918 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27850524184876679168
theorem maskCheck3918 :
    checkMaskFor missing3918 StrongPackedBucketN12A3Shard030.record3918 = true := by
  decide

def missing3919 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27886552981895643136
theorem maskCheck3919 :
    checkMaskFor missing3919 StrongPackedBucketN12A3Shard030.record3919 = true := by
  decide

def missing3920 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28030668169971499008
theorem maskCheck3920 :
    checkMaskFor missing3920 StrongPackedBucketN12A3Shard030.record3920 = true := by
  decide

def missing3921 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28102725764009426944
theorem maskCheck3921 :
    checkMaskFor missing3921 StrongPackedBucketN12A3Shard030.record3921 = true := by
  decide

def missing3922 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37145953815769382912
theorem maskCheck3922 :
    checkMaskFor missing3922 StrongPackedBucketN12A3Shard030.record3922 = true := by
  decide

def missing3923 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37290069003845238784
theorem maskCheck3923 :
    checkMaskFor missing3923 StrongPackedBucketN12A3Shard030.record3923 = true := by
  decide

def missing3924 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37902558553167626240
theorem maskCheck3924 :
    checkMaskFor missing3924 StrongPackedBucketN12A3Shard030.record3924 = true := by
  decide

def missing3925 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38911364869698617344
theorem maskCheck3925 :
    checkMaskFor missing3925 StrongPackedBucketN12A3Shard030.record3925 = true := by
  decide

def missing3926 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46225210664548302848
theorem maskCheck3926 :
    checkMaskFor missing3926 StrongPackedBucketN12A3Shard030.record3926 = true := by
  decide

def missing3927 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46297268258586230784
theorem maskCheck3927 :
    checkMaskFor missing3927 StrongPackedBucketN12A3Shard030.record3927 = true := by
  decide

def missing3928 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46333297055605194752
theorem maskCheck3928 :
    checkMaskFor missing3928 StrongPackedBucketN12A3Shard030.record3928 = true := by
  decide

def missing3929 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46441383446662086656
theorem maskCheck3929 :
    checkMaskFor missing3929 StrongPackedBucketN12A3Shard030.record3929 = true := by
  decide

def missing3930 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46477412243681050624
theorem maskCheck3930 :
    checkMaskFor missing3930 StrongPackedBucketN12A3Shard030.record3930 = true := by
  decide

def missing3931 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46549469837718978560
theorem maskCheck3931 :
    checkMaskFor missing3931 StrongPackedBucketN12A3Shard030.record3931 = true := by
  decide

def missing3932 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46981815401946546176
theorem maskCheck3932 :
    checkMaskFor missing3932 StrongPackedBucketN12A3Shard030.record3932 = true := by
  decide

def missing3933 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55520640295441006592
theorem maskCheck3933 :
    checkMaskFor missing3933 StrongPackedBucketN12A3Shard030.record3933 = true := by
  decide

def missing3934 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55556669092459970560
theorem maskCheck3934 :
    checkMaskFor missing3934 StrongPackedBucketN12A3Shard030.record3934 = true := by
  decide

def missing3935 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55700784280535826432
theorem maskCheck3935 :
    checkMaskFor missing3935 StrongPackedBucketN12A3Shard030.record3935 = true := by
  decide

def missing3936 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55772841874573754368
theorem maskCheck3936 :
    checkMaskFor missing3936 StrongPackedBucketN12A3Shard030.record3936 = true := by
  decide

def missing3937 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56205187438801321984
theorem maskCheck3937 :
    checkMaskFor missing3937 StrongPackedBucketN12A3Shard030.record3937 = true := by
  decide

def missing3938 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64599897144219926528
theorem maskCheck3938 :
    checkMaskFor missing3938 StrongPackedBucketN12A3Shard030.record3938 = true := by
  decide

def missing3939 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64635925941238890496
theorem maskCheck3939 :
    checkMaskFor missing3939 StrongPackedBucketN12A3Shard030.record3939 = true := by
  decide

def missing3940 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64707983535276818432
theorem maskCheck3940 :
    checkMaskFor missing3940 StrongPackedBucketN12A3Shard030.record3940 = true := by
  decide

def missing3941 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64852098723352674304
theorem maskCheck3941 :
    checkMaskFor missing3941 StrongPackedBucketN12A3Shard030.record3941 = true := by
  decide

def missing3942 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 540907150734524416
theorem maskCheck3942 :
    checkMaskFor missing3942 StrongPackedBucketN12A3Shard030.record3942 = true := by
  decide

def missing3943 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 829137526886236160
theorem maskCheck3943 :
    checkMaskFor missing3943 StrongPackedBucketN12A3Shard030.record3943 = true := by
  decide

def missing3944 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1045310309000019968
theorem maskCheck3944 :
    checkMaskFor missing3944 StrongPackedBucketN12A3Shard030.record3944 = true := by
  decide

def missing3945 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081339106018983936
theorem maskCheck3945 :
    checkMaskFor missing3945 StrongPackedBucketN12A3Shard030.record3945 = true := by
  decide

def missing3946 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1946030234474119168
theorem maskCheck3946 :
    checkMaskFor missing3946 StrongPackedBucketN12A3Shard030.record3946 = true := by
  decide

def missing3947 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2162203016587902976
theorem maskCheck3947 :
    checkMaskFor missing3947 StrongPackedBucketN12A3Shard030.record3947 = true := by
  decide

def missing3948 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4107758055611957248
theorem maskCheck3948 :
    checkMaskFor missing3948 StrongPackedBucketN12A3Shard030.record3948 = true := by
  decide

def missing3949 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4179815649649885184
theorem maskCheck3949 :
    checkMaskFor missing3949 StrongPackedBucketN12A3Shard030.record3949 = true := by
  decide

def missing3950 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8647386480001417216
theorem maskCheck3950 :
    checkMaskFor missing3950 StrongPackedBucketN12A3Shard030.record3950 = true := by
  decide

def missing3951 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9476048811437588480
theorem maskCheck3951 :
    checkMaskFor missing3951 StrongPackedBucketN12A3Shard030.record3951 = true := by
  decide

def missing3952 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9692221593551372288
theorem maskCheck3952 :
    checkMaskFor missing3952 StrongPackedBucketN12A3Shard030.record3952 = true := by
  decide

def missing3953 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9728250390570336256
theorem maskCheck3953 :
    checkMaskFor missing3953 StrongPackedBucketN12A3Shard030.record3953 = true := by
  decide

def missing3954 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9908394375665156096
theorem maskCheck3954 :
    checkMaskFor missing3954 StrongPackedBucketN12A3Shard030.record3954 = true := by
  decide

def missing3955 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9980451969703084032
theorem maskCheck3955 :
    checkMaskFor missing3955 StrongPackedBucketN12A3Shard030.record3955 = true := by
  decide

def missing3956 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10016480766722048000
theorem maskCheck3956 :
    checkMaskFor missing3956 StrongPackedBucketN12A3Shard030.record3956 = true := by
  decide

def missing3957 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10232653548835831808
theorem maskCheck3957 :
    checkMaskFor missing3957 StrongPackedBucketN12A3Shard030.record3957 = true := by
  decide

def missing3958 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11025287083253039104
theorem maskCheck3958 :
    checkMaskFor missing3958 StrongPackedBucketN12A3Shard030.record3958 = true := by
  decide

def missing3959 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11097344677290967040
theorem maskCheck3959 :
    checkMaskFor missing3959 StrongPackedBucketN12A3Shard030.record3959 = true := by
  decide

def missing3960 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13259072498428805120
theorem maskCheck3960 :
    checkMaskFor missing3960 StrongPackedBucketN12A3Shard030.record3960 = true := by
  decide

def missing3961 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699420848292364288
theorem maskCheck3961 :
    checkMaskFor missing3961 StrongPackedBucketN12A3Shard030.record3961 = true := by
  decide

def missing3962 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18915593630406148096
theorem maskCheck3962 :
    checkMaskFor missing3962 StrongPackedBucketN12A3Shard030.record3962 = true := by
  decide

def missing3963 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18951622427425112064
theorem maskCheck3963 :
    checkMaskFor missing3963 StrongPackedBucketN12A3Shard030.record3963 = true := by
  decide

def missing3964 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19131766412519931904
theorem maskCheck3964 :
    checkMaskFor missing3964 StrongPackedBucketN12A3Shard030.record3964 = true := by
  decide

def missing3965 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19203824006557859840
theorem maskCheck3965 :
    checkMaskFor missing3965 StrongPackedBucketN12A3Shard030.record3965 = true := by
  decide

def missing3966 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19239852803576823808
theorem maskCheck3966 :
    checkMaskFor missing3966 StrongPackedBucketN12A3Shard030.record3966 = true := by
  decide

def missing3967 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19456025585690607616
theorem maskCheck3967 :
    checkMaskFor missing3967 StrongPackedBucketN12A3Shard030.record3967 = true := by
  decide

def missing3840_3841 : List (BitVec (edgeCount 12)) :=
  [missing3840]
abbrev records3840_3841 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3840]
theorem aligned3840_3841 :
    AlignedValid 12 3 missing3840_3841 records3840_3841 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3840
    maskCheck3840 AlignedValid.nil

def missing3841_3842 : List (BitVec (edgeCount 12)) :=
  [missing3841]
abbrev records3841_3842 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3841]
theorem aligned3841_3842 :
    AlignedValid 12 3 missing3841_3842 records3841_3842 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3841
    maskCheck3841 AlignedValid.nil

def missing3840_3842 : List (BitVec (edgeCount 12)) :=
  missing3840_3841 ++ missing3841_3842
abbrev records3840_3842 : List Blob :=
  records3840_3841 ++ records3841_3842
theorem aligned3840_3842 :
    AlignedValid 12 3 missing3840_3842 records3840_3842 :=
  aligned3840_3841.append aligned3841_3842

def missing3842_3843 : List (BitVec (edgeCount 12)) :=
  [missing3842]
abbrev records3842_3843 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3842]
theorem aligned3842_3843 :
    AlignedValid 12 3 missing3842_3843 records3842_3843 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3842
    maskCheck3842 AlignedValid.nil

def missing3843_3844 : List (BitVec (edgeCount 12)) :=
  [missing3843]
abbrev records3843_3844 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3843]
theorem aligned3843_3844 :
    AlignedValid 12 3 missing3843_3844 records3843_3844 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3843
    maskCheck3843 AlignedValid.nil

def missing3842_3844 : List (BitVec (edgeCount 12)) :=
  missing3842_3843 ++ missing3843_3844
abbrev records3842_3844 : List Blob :=
  records3842_3843 ++ records3843_3844
theorem aligned3842_3844 :
    AlignedValid 12 3 missing3842_3844 records3842_3844 :=
  aligned3842_3843.append aligned3843_3844

def missing3840_3844 : List (BitVec (edgeCount 12)) :=
  missing3840_3842 ++ missing3842_3844
abbrev records3840_3844 : List Blob :=
  records3840_3842 ++ records3842_3844
theorem aligned3840_3844 :
    AlignedValid 12 3 missing3840_3844 records3840_3844 :=
  aligned3840_3842.append aligned3842_3844

def missing3844_3845 : List (BitVec (edgeCount 12)) :=
  [missing3844]
abbrev records3844_3845 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3844]
theorem aligned3844_3845 :
    AlignedValid 12 3 missing3844_3845 records3844_3845 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3844
    maskCheck3844 AlignedValid.nil

def missing3845_3846 : List (BitVec (edgeCount 12)) :=
  [missing3845]
abbrev records3845_3846 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3845]
theorem aligned3845_3846 :
    AlignedValid 12 3 missing3845_3846 records3845_3846 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3845
    maskCheck3845 AlignedValid.nil

def missing3844_3846 : List (BitVec (edgeCount 12)) :=
  missing3844_3845 ++ missing3845_3846
abbrev records3844_3846 : List Blob :=
  records3844_3845 ++ records3845_3846
theorem aligned3844_3846 :
    AlignedValid 12 3 missing3844_3846 records3844_3846 :=
  aligned3844_3845.append aligned3845_3846

def missing3846_3847 : List (BitVec (edgeCount 12)) :=
  [missing3846]
abbrev records3846_3847 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3846]
theorem aligned3846_3847 :
    AlignedValid 12 3 missing3846_3847 records3846_3847 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3846
    maskCheck3846 AlignedValid.nil

def missing3847_3848 : List (BitVec (edgeCount 12)) :=
  [missing3847]
abbrev records3847_3848 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3847]
theorem aligned3847_3848 :
    AlignedValid 12 3 missing3847_3848 records3847_3848 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3847
    maskCheck3847 AlignedValid.nil

def missing3846_3848 : List (BitVec (edgeCount 12)) :=
  missing3846_3847 ++ missing3847_3848
abbrev records3846_3848 : List Blob :=
  records3846_3847 ++ records3847_3848
theorem aligned3846_3848 :
    AlignedValid 12 3 missing3846_3848 records3846_3848 :=
  aligned3846_3847.append aligned3847_3848

def missing3844_3848 : List (BitVec (edgeCount 12)) :=
  missing3844_3846 ++ missing3846_3848
abbrev records3844_3848 : List Blob :=
  records3844_3846 ++ records3846_3848
theorem aligned3844_3848 :
    AlignedValid 12 3 missing3844_3848 records3844_3848 :=
  aligned3844_3846.append aligned3846_3848

def missing3840_3848 : List (BitVec (edgeCount 12)) :=
  missing3840_3844 ++ missing3844_3848
abbrev records3840_3848 : List Blob :=
  records3840_3844 ++ records3844_3848
theorem aligned3840_3848 :
    AlignedValid 12 3 missing3840_3848 records3840_3848 :=
  aligned3840_3844.append aligned3844_3848

def missing3848_3849 : List (BitVec (edgeCount 12)) :=
  [missing3848]
abbrev records3848_3849 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3848]
theorem aligned3848_3849 :
    AlignedValid 12 3 missing3848_3849 records3848_3849 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3848
    maskCheck3848 AlignedValid.nil

def missing3849_3850 : List (BitVec (edgeCount 12)) :=
  [missing3849]
abbrev records3849_3850 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3849]
theorem aligned3849_3850 :
    AlignedValid 12 3 missing3849_3850 records3849_3850 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3849
    maskCheck3849 AlignedValid.nil

def missing3848_3850 : List (BitVec (edgeCount 12)) :=
  missing3848_3849 ++ missing3849_3850
abbrev records3848_3850 : List Blob :=
  records3848_3849 ++ records3849_3850
theorem aligned3848_3850 :
    AlignedValid 12 3 missing3848_3850 records3848_3850 :=
  aligned3848_3849.append aligned3849_3850

def missing3850_3851 : List (BitVec (edgeCount 12)) :=
  [missing3850]
abbrev records3850_3851 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3850]
theorem aligned3850_3851 :
    AlignedValid 12 3 missing3850_3851 records3850_3851 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3850
    maskCheck3850 AlignedValid.nil

def missing3851_3852 : List (BitVec (edgeCount 12)) :=
  [missing3851]
abbrev records3851_3852 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3851]
theorem aligned3851_3852 :
    AlignedValid 12 3 missing3851_3852 records3851_3852 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3851
    maskCheck3851 AlignedValid.nil

def missing3850_3852 : List (BitVec (edgeCount 12)) :=
  missing3850_3851 ++ missing3851_3852
abbrev records3850_3852 : List Blob :=
  records3850_3851 ++ records3851_3852
theorem aligned3850_3852 :
    AlignedValid 12 3 missing3850_3852 records3850_3852 :=
  aligned3850_3851.append aligned3851_3852

def missing3848_3852 : List (BitVec (edgeCount 12)) :=
  missing3848_3850 ++ missing3850_3852
abbrev records3848_3852 : List Blob :=
  records3848_3850 ++ records3850_3852
theorem aligned3848_3852 :
    AlignedValid 12 3 missing3848_3852 records3848_3852 :=
  aligned3848_3850.append aligned3850_3852

def missing3852_3853 : List (BitVec (edgeCount 12)) :=
  [missing3852]
abbrev records3852_3853 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3852]
theorem aligned3852_3853 :
    AlignedValid 12 3 missing3852_3853 records3852_3853 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3852
    maskCheck3852 AlignedValid.nil

def missing3853_3854 : List (BitVec (edgeCount 12)) :=
  [missing3853]
abbrev records3853_3854 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3853]
theorem aligned3853_3854 :
    AlignedValid 12 3 missing3853_3854 records3853_3854 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3853
    maskCheck3853 AlignedValid.nil

def missing3852_3854 : List (BitVec (edgeCount 12)) :=
  missing3852_3853 ++ missing3853_3854
abbrev records3852_3854 : List Blob :=
  records3852_3853 ++ records3853_3854
theorem aligned3852_3854 :
    AlignedValid 12 3 missing3852_3854 records3852_3854 :=
  aligned3852_3853.append aligned3853_3854

def missing3854_3855 : List (BitVec (edgeCount 12)) :=
  [missing3854]
abbrev records3854_3855 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3854]
theorem aligned3854_3855 :
    AlignedValid 12 3 missing3854_3855 records3854_3855 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3854
    maskCheck3854 AlignedValid.nil

def missing3855_3856 : List (BitVec (edgeCount 12)) :=
  [missing3855]
abbrev records3855_3856 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3855]
theorem aligned3855_3856 :
    AlignedValid 12 3 missing3855_3856 records3855_3856 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3855
    maskCheck3855 AlignedValid.nil

def missing3854_3856 : List (BitVec (edgeCount 12)) :=
  missing3854_3855 ++ missing3855_3856
abbrev records3854_3856 : List Blob :=
  records3854_3855 ++ records3855_3856
theorem aligned3854_3856 :
    AlignedValid 12 3 missing3854_3856 records3854_3856 :=
  aligned3854_3855.append aligned3855_3856

def missing3852_3856 : List (BitVec (edgeCount 12)) :=
  missing3852_3854 ++ missing3854_3856
abbrev records3852_3856 : List Blob :=
  records3852_3854 ++ records3854_3856
theorem aligned3852_3856 :
    AlignedValid 12 3 missing3852_3856 records3852_3856 :=
  aligned3852_3854.append aligned3854_3856

def missing3848_3856 : List (BitVec (edgeCount 12)) :=
  missing3848_3852 ++ missing3852_3856
abbrev records3848_3856 : List Blob :=
  records3848_3852 ++ records3852_3856
theorem aligned3848_3856 :
    AlignedValid 12 3 missing3848_3856 records3848_3856 :=
  aligned3848_3852.append aligned3852_3856

def missing3840_3856 : List (BitVec (edgeCount 12)) :=
  missing3840_3848 ++ missing3848_3856
abbrev records3840_3856 : List Blob :=
  records3840_3848 ++ records3848_3856
theorem aligned3840_3856 :
    AlignedValid 12 3 missing3840_3856 records3840_3856 :=
  aligned3840_3848.append aligned3848_3856

def missing3856_3857 : List (BitVec (edgeCount 12)) :=
  [missing3856]
abbrev records3856_3857 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3856]
theorem aligned3856_3857 :
    AlignedValid 12 3 missing3856_3857 records3856_3857 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3856
    maskCheck3856 AlignedValid.nil

def missing3857_3858 : List (BitVec (edgeCount 12)) :=
  [missing3857]
abbrev records3857_3858 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3857]
theorem aligned3857_3858 :
    AlignedValid 12 3 missing3857_3858 records3857_3858 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3857
    maskCheck3857 AlignedValid.nil

def missing3856_3858 : List (BitVec (edgeCount 12)) :=
  missing3856_3857 ++ missing3857_3858
abbrev records3856_3858 : List Blob :=
  records3856_3857 ++ records3857_3858
theorem aligned3856_3858 :
    AlignedValid 12 3 missing3856_3858 records3856_3858 :=
  aligned3856_3857.append aligned3857_3858

def missing3858_3859 : List (BitVec (edgeCount 12)) :=
  [missing3858]
abbrev records3858_3859 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3858]
theorem aligned3858_3859 :
    AlignedValid 12 3 missing3858_3859 records3858_3859 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3858
    maskCheck3858 AlignedValid.nil

def missing3859_3860 : List (BitVec (edgeCount 12)) :=
  [missing3859]
abbrev records3859_3860 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3859]
theorem aligned3859_3860 :
    AlignedValid 12 3 missing3859_3860 records3859_3860 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3859
    maskCheck3859 AlignedValid.nil

def missing3858_3860 : List (BitVec (edgeCount 12)) :=
  missing3858_3859 ++ missing3859_3860
abbrev records3858_3860 : List Blob :=
  records3858_3859 ++ records3859_3860
theorem aligned3858_3860 :
    AlignedValid 12 3 missing3858_3860 records3858_3860 :=
  aligned3858_3859.append aligned3859_3860

def missing3856_3860 : List (BitVec (edgeCount 12)) :=
  missing3856_3858 ++ missing3858_3860
abbrev records3856_3860 : List Blob :=
  records3856_3858 ++ records3858_3860
theorem aligned3856_3860 :
    AlignedValid 12 3 missing3856_3860 records3856_3860 :=
  aligned3856_3858.append aligned3858_3860

def missing3860_3861 : List (BitVec (edgeCount 12)) :=
  [missing3860]
abbrev records3860_3861 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3860]
theorem aligned3860_3861 :
    AlignedValid 12 3 missing3860_3861 records3860_3861 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3860
    maskCheck3860 AlignedValid.nil

def missing3861_3862 : List (BitVec (edgeCount 12)) :=
  [missing3861]
abbrev records3861_3862 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3861]
theorem aligned3861_3862 :
    AlignedValid 12 3 missing3861_3862 records3861_3862 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3861
    maskCheck3861 AlignedValid.nil

def missing3860_3862 : List (BitVec (edgeCount 12)) :=
  missing3860_3861 ++ missing3861_3862
abbrev records3860_3862 : List Blob :=
  records3860_3861 ++ records3861_3862
theorem aligned3860_3862 :
    AlignedValid 12 3 missing3860_3862 records3860_3862 :=
  aligned3860_3861.append aligned3861_3862

def missing3862_3863 : List (BitVec (edgeCount 12)) :=
  [missing3862]
abbrev records3862_3863 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3862]
theorem aligned3862_3863 :
    AlignedValid 12 3 missing3862_3863 records3862_3863 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3862
    maskCheck3862 AlignedValid.nil

def missing3863_3864 : List (BitVec (edgeCount 12)) :=
  [missing3863]
abbrev records3863_3864 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3863]
theorem aligned3863_3864 :
    AlignedValid 12 3 missing3863_3864 records3863_3864 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3863
    maskCheck3863 AlignedValid.nil

def missing3862_3864 : List (BitVec (edgeCount 12)) :=
  missing3862_3863 ++ missing3863_3864
abbrev records3862_3864 : List Blob :=
  records3862_3863 ++ records3863_3864
theorem aligned3862_3864 :
    AlignedValid 12 3 missing3862_3864 records3862_3864 :=
  aligned3862_3863.append aligned3863_3864

def missing3860_3864 : List (BitVec (edgeCount 12)) :=
  missing3860_3862 ++ missing3862_3864
abbrev records3860_3864 : List Blob :=
  records3860_3862 ++ records3862_3864
theorem aligned3860_3864 :
    AlignedValid 12 3 missing3860_3864 records3860_3864 :=
  aligned3860_3862.append aligned3862_3864

def missing3856_3864 : List (BitVec (edgeCount 12)) :=
  missing3856_3860 ++ missing3860_3864
abbrev records3856_3864 : List Blob :=
  records3856_3860 ++ records3860_3864
theorem aligned3856_3864 :
    AlignedValid 12 3 missing3856_3864 records3856_3864 :=
  aligned3856_3860.append aligned3860_3864

def missing3864_3865 : List (BitVec (edgeCount 12)) :=
  [missing3864]
abbrev records3864_3865 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3864]
theorem aligned3864_3865 :
    AlignedValid 12 3 missing3864_3865 records3864_3865 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3864
    maskCheck3864 AlignedValid.nil

def missing3865_3866 : List (BitVec (edgeCount 12)) :=
  [missing3865]
abbrev records3865_3866 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3865]
theorem aligned3865_3866 :
    AlignedValid 12 3 missing3865_3866 records3865_3866 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3865
    maskCheck3865 AlignedValid.nil

def missing3864_3866 : List (BitVec (edgeCount 12)) :=
  missing3864_3865 ++ missing3865_3866
abbrev records3864_3866 : List Blob :=
  records3864_3865 ++ records3865_3866
theorem aligned3864_3866 :
    AlignedValid 12 3 missing3864_3866 records3864_3866 :=
  aligned3864_3865.append aligned3865_3866

def missing3866_3867 : List (BitVec (edgeCount 12)) :=
  [missing3866]
abbrev records3866_3867 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3866]
theorem aligned3866_3867 :
    AlignedValid 12 3 missing3866_3867 records3866_3867 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3866
    maskCheck3866 AlignedValid.nil

def missing3867_3868 : List (BitVec (edgeCount 12)) :=
  [missing3867]
abbrev records3867_3868 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3867]
theorem aligned3867_3868 :
    AlignedValid 12 3 missing3867_3868 records3867_3868 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3867
    maskCheck3867 AlignedValid.nil

def missing3866_3868 : List (BitVec (edgeCount 12)) :=
  missing3866_3867 ++ missing3867_3868
abbrev records3866_3868 : List Blob :=
  records3866_3867 ++ records3867_3868
theorem aligned3866_3868 :
    AlignedValid 12 3 missing3866_3868 records3866_3868 :=
  aligned3866_3867.append aligned3867_3868

def missing3864_3868 : List (BitVec (edgeCount 12)) :=
  missing3864_3866 ++ missing3866_3868
abbrev records3864_3868 : List Blob :=
  records3864_3866 ++ records3866_3868
theorem aligned3864_3868 :
    AlignedValid 12 3 missing3864_3868 records3864_3868 :=
  aligned3864_3866.append aligned3866_3868

def missing3868_3869 : List (BitVec (edgeCount 12)) :=
  [missing3868]
abbrev records3868_3869 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3868]
theorem aligned3868_3869 :
    AlignedValid 12 3 missing3868_3869 records3868_3869 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3868
    maskCheck3868 AlignedValid.nil

def missing3869_3870 : List (BitVec (edgeCount 12)) :=
  [missing3869]
abbrev records3869_3870 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3869]
theorem aligned3869_3870 :
    AlignedValid 12 3 missing3869_3870 records3869_3870 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3869
    maskCheck3869 AlignedValid.nil

def missing3868_3870 : List (BitVec (edgeCount 12)) :=
  missing3868_3869 ++ missing3869_3870
abbrev records3868_3870 : List Blob :=
  records3868_3869 ++ records3869_3870
theorem aligned3868_3870 :
    AlignedValid 12 3 missing3868_3870 records3868_3870 :=
  aligned3868_3869.append aligned3869_3870

def missing3870_3871 : List (BitVec (edgeCount 12)) :=
  [missing3870]
abbrev records3870_3871 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3870]
theorem aligned3870_3871 :
    AlignedValid 12 3 missing3870_3871 records3870_3871 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3870
    maskCheck3870 AlignedValid.nil

def missing3871_3872 : List (BitVec (edgeCount 12)) :=
  [missing3871]
abbrev records3871_3872 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3871]
theorem aligned3871_3872 :
    AlignedValid 12 3 missing3871_3872 records3871_3872 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3871
    maskCheck3871 AlignedValid.nil

def missing3870_3872 : List (BitVec (edgeCount 12)) :=
  missing3870_3871 ++ missing3871_3872
abbrev records3870_3872 : List Blob :=
  records3870_3871 ++ records3871_3872
theorem aligned3870_3872 :
    AlignedValid 12 3 missing3870_3872 records3870_3872 :=
  aligned3870_3871.append aligned3871_3872

def missing3868_3872 : List (BitVec (edgeCount 12)) :=
  missing3868_3870 ++ missing3870_3872
abbrev records3868_3872 : List Blob :=
  records3868_3870 ++ records3870_3872
theorem aligned3868_3872 :
    AlignedValid 12 3 missing3868_3872 records3868_3872 :=
  aligned3868_3870.append aligned3870_3872

def missing3864_3872 : List (BitVec (edgeCount 12)) :=
  missing3864_3868 ++ missing3868_3872
abbrev records3864_3872 : List Blob :=
  records3864_3868 ++ records3868_3872
theorem aligned3864_3872 :
    AlignedValid 12 3 missing3864_3872 records3864_3872 :=
  aligned3864_3868.append aligned3868_3872

def missing3856_3872 : List (BitVec (edgeCount 12)) :=
  missing3856_3864 ++ missing3864_3872
abbrev records3856_3872 : List Blob :=
  records3856_3864 ++ records3864_3872
theorem aligned3856_3872 :
    AlignedValid 12 3 missing3856_3872 records3856_3872 :=
  aligned3856_3864.append aligned3864_3872

def missing3840_3872 : List (BitVec (edgeCount 12)) :=
  missing3840_3856 ++ missing3856_3872
abbrev records3840_3872 : List Blob :=
  records3840_3856 ++ records3856_3872
theorem aligned3840_3872 :
    AlignedValid 12 3 missing3840_3872 records3840_3872 :=
  aligned3840_3856.append aligned3856_3872

def missing3872_3873 : List (BitVec (edgeCount 12)) :=
  [missing3872]
abbrev records3872_3873 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3872]
theorem aligned3872_3873 :
    AlignedValid 12 3 missing3872_3873 records3872_3873 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3872
    maskCheck3872 AlignedValid.nil

def missing3873_3874 : List (BitVec (edgeCount 12)) :=
  [missing3873]
abbrev records3873_3874 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3873]
theorem aligned3873_3874 :
    AlignedValid 12 3 missing3873_3874 records3873_3874 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3873
    maskCheck3873 AlignedValid.nil

def missing3872_3874 : List (BitVec (edgeCount 12)) :=
  missing3872_3873 ++ missing3873_3874
abbrev records3872_3874 : List Blob :=
  records3872_3873 ++ records3873_3874
theorem aligned3872_3874 :
    AlignedValid 12 3 missing3872_3874 records3872_3874 :=
  aligned3872_3873.append aligned3873_3874

def missing3874_3875 : List (BitVec (edgeCount 12)) :=
  [missing3874]
abbrev records3874_3875 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3874]
theorem aligned3874_3875 :
    AlignedValid 12 3 missing3874_3875 records3874_3875 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3874
    maskCheck3874 AlignedValid.nil

def missing3875_3876 : List (BitVec (edgeCount 12)) :=
  [missing3875]
abbrev records3875_3876 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3875]
theorem aligned3875_3876 :
    AlignedValid 12 3 missing3875_3876 records3875_3876 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3875
    maskCheck3875 AlignedValid.nil

def missing3874_3876 : List (BitVec (edgeCount 12)) :=
  missing3874_3875 ++ missing3875_3876
abbrev records3874_3876 : List Blob :=
  records3874_3875 ++ records3875_3876
theorem aligned3874_3876 :
    AlignedValid 12 3 missing3874_3876 records3874_3876 :=
  aligned3874_3875.append aligned3875_3876

def missing3872_3876 : List (BitVec (edgeCount 12)) :=
  missing3872_3874 ++ missing3874_3876
abbrev records3872_3876 : List Blob :=
  records3872_3874 ++ records3874_3876
theorem aligned3872_3876 :
    AlignedValid 12 3 missing3872_3876 records3872_3876 :=
  aligned3872_3874.append aligned3874_3876

def missing3876_3877 : List (BitVec (edgeCount 12)) :=
  [missing3876]
abbrev records3876_3877 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3876]
theorem aligned3876_3877 :
    AlignedValid 12 3 missing3876_3877 records3876_3877 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3876
    maskCheck3876 AlignedValid.nil

def missing3877_3878 : List (BitVec (edgeCount 12)) :=
  [missing3877]
abbrev records3877_3878 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3877]
theorem aligned3877_3878 :
    AlignedValid 12 3 missing3877_3878 records3877_3878 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3877
    maskCheck3877 AlignedValid.nil

def missing3876_3878 : List (BitVec (edgeCount 12)) :=
  missing3876_3877 ++ missing3877_3878
abbrev records3876_3878 : List Blob :=
  records3876_3877 ++ records3877_3878
theorem aligned3876_3878 :
    AlignedValid 12 3 missing3876_3878 records3876_3878 :=
  aligned3876_3877.append aligned3877_3878

def missing3878_3879 : List (BitVec (edgeCount 12)) :=
  [missing3878]
abbrev records3878_3879 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3878]
theorem aligned3878_3879 :
    AlignedValid 12 3 missing3878_3879 records3878_3879 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3878
    maskCheck3878 AlignedValid.nil

def missing3879_3880 : List (BitVec (edgeCount 12)) :=
  [missing3879]
abbrev records3879_3880 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3879]
theorem aligned3879_3880 :
    AlignedValid 12 3 missing3879_3880 records3879_3880 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3879
    maskCheck3879 AlignedValid.nil

def missing3878_3880 : List (BitVec (edgeCount 12)) :=
  missing3878_3879 ++ missing3879_3880
abbrev records3878_3880 : List Blob :=
  records3878_3879 ++ records3879_3880
theorem aligned3878_3880 :
    AlignedValid 12 3 missing3878_3880 records3878_3880 :=
  aligned3878_3879.append aligned3879_3880

def missing3876_3880 : List (BitVec (edgeCount 12)) :=
  missing3876_3878 ++ missing3878_3880
abbrev records3876_3880 : List Blob :=
  records3876_3878 ++ records3878_3880
theorem aligned3876_3880 :
    AlignedValid 12 3 missing3876_3880 records3876_3880 :=
  aligned3876_3878.append aligned3878_3880

def missing3872_3880 : List (BitVec (edgeCount 12)) :=
  missing3872_3876 ++ missing3876_3880
abbrev records3872_3880 : List Blob :=
  records3872_3876 ++ records3876_3880
theorem aligned3872_3880 :
    AlignedValid 12 3 missing3872_3880 records3872_3880 :=
  aligned3872_3876.append aligned3876_3880

def missing3880_3881 : List (BitVec (edgeCount 12)) :=
  [missing3880]
abbrev records3880_3881 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3880]
theorem aligned3880_3881 :
    AlignedValid 12 3 missing3880_3881 records3880_3881 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3880
    maskCheck3880 AlignedValid.nil

def missing3881_3882 : List (BitVec (edgeCount 12)) :=
  [missing3881]
abbrev records3881_3882 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3881]
theorem aligned3881_3882 :
    AlignedValid 12 3 missing3881_3882 records3881_3882 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3881
    maskCheck3881 AlignedValid.nil

def missing3880_3882 : List (BitVec (edgeCount 12)) :=
  missing3880_3881 ++ missing3881_3882
abbrev records3880_3882 : List Blob :=
  records3880_3881 ++ records3881_3882
theorem aligned3880_3882 :
    AlignedValid 12 3 missing3880_3882 records3880_3882 :=
  aligned3880_3881.append aligned3881_3882

def missing3882_3883 : List (BitVec (edgeCount 12)) :=
  [missing3882]
abbrev records3882_3883 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3882]
theorem aligned3882_3883 :
    AlignedValid 12 3 missing3882_3883 records3882_3883 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3882
    maskCheck3882 AlignedValid.nil

def missing3883_3884 : List (BitVec (edgeCount 12)) :=
  [missing3883]
abbrev records3883_3884 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3883]
theorem aligned3883_3884 :
    AlignedValid 12 3 missing3883_3884 records3883_3884 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3883
    maskCheck3883 AlignedValid.nil

def missing3882_3884 : List (BitVec (edgeCount 12)) :=
  missing3882_3883 ++ missing3883_3884
abbrev records3882_3884 : List Blob :=
  records3882_3883 ++ records3883_3884
theorem aligned3882_3884 :
    AlignedValid 12 3 missing3882_3884 records3882_3884 :=
  aligned3882_3883.append aligned3883_3884

def missing3880_3884 : List (BitVec (edgeCount 12)) :=
  missing3880_3882 ++ missing3882_3884
abbrev records3880_3884 : List Blob :=
  records3880_3882 ++ records3882_3884
theorem aligned3880_3884 :
    AlignedValid 12 3 missing3880_3884 records3880_3884 :=
  aligned3880_3882.append aligned3882_3884

def missing3884_3885 : List (BitVec (edgeCount 12)) :=
  [missing3884]
abbrev records3884_3885 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3884]
theorem aligned3884_3885 :
    AlignedValid 12 3 missing3884_3885 records3884_3885 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3884
    maskCheck3884 AlignedValid.nil

def missing3885_3886 : List (BitVec (edgeCount 12)) :=
  [missing3885]
abbrev records3885_3886 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3885]
theorem aligned3885_3886 :
    AlignedValid 12 3 missing3885_3886 records3885_3886 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3885
    maskCheck3885 AlignedValid.nil

def missing3884_3886 : List (BitVec (edgeCount 12)) :=
  missing3884_3885 ++ missing3885_3886
abbrev records3884_3886 : List Blob :=
  records3884_3885 ++ records3885_3886
theorem aligned3884_3886 :
    AlignedValid 12 3 missing3884_3886 records3884_3886 :=
  aligned3884_3885.append aligned3885_3886

def missing3886_3887 : List (BitVec (edgeCount 12)) :=
  [missing3886]
abbrev records3886_3887 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3886]
theorem aligned3886_3887 :
    AlignedValid 12 3 missing3886_3887 records3886_3887 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3886
    maskCheck3886 AlignedValid.nil

def missing3887_3888 : List (BitVec (edgeCount 12)) :=
  [missing3887]
abbrev records3887_3888 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3887]
theorem aligned3887_3888 :
    AlignedValid 12 3 missing3887_3888 records3887_3888 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3887
    maskCheck3887 AlignedValid.nil

def missing3886_3888 : List (BitVec (edgeCount 12)) :=
  missing3886_3887 ++ missing3887_3888
abbrev records3886_3888 : List Blob :=
  records3886_3887 ++ records3887_3888
theorem aligned3886_3888 :
    AlignedValid 12 3 missing3886_3888 records3886_3888 :=
  aligned3886_3887.append aligned3887_3888

def missing3884_3888 : List (BitVec (edgeCount 12)) :=
  missing3884_3886 ++ missing3886_3888
abbrev records3884_3888 : List Blob :=
  records3884_3886 ++ records3886_3888
theorem aligned3884_3888 :
    AlignedValid 12 3 missing3884_3888 records3884_3888 :=
  aligned3884_3886.append aligned3886_3888

def missing3880_3888 : List (BitVec (edgeCount 12)) :=
  missing3880_3884 ++ missing3884_3888
abbrev records3880_3888 : List Blob :=
  records3880_3884 ++ records3884_3888
theorem aligned3880_3888 :
    AlignedValid 12 3 missing3880_3888 records3880_3888 :=
  aligned3880_3884.append aligned3884_3888

def missing3872_3888 : List (BitVec (edgeCount 12)) :=
  missing3872_3880 ++ missing3880_3888
abbrev records3872_3888 : List Blob :=
  records3872_3880 ++ records3880_3888
theorem aligned3872_3888 :
    AlignedValid 12 3 missing3872_3888 records3872_3888 :=
  aligned3872_3880.append aligned3880_3888

def missing3888_3889 : List (BitVec (edgeCount 12)) :=
  [missing3888]
abbrev records3888_3889 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3888]
theorem aligned3888_3889 :
    AlignedValid 12 3 missing3888_3889 records3888_3889 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3888
    maskCheck3888 AlignedValid.nil

def missing3889_3890 : List (BitVec (edgeCount 12)) :=
  [missing3889]
abbrev records3889_3890 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3889]
theorem aligned3889_3890 :
    AlignedValid 12 3 missing3889_3890 records3889_3890 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3889
    maskCheck3889 AlignedValid.nil

def missing3888_3890 : List (BitVec (edgeCount 12)) :=
  missing3888_3889 ++ missing3889_3890
abbrev records3888_3890 : List Blob :=
  records3888_3889 ++ records3889_3890
theorem aligned3888_3890 :
    AlignedValid 12 3 missing3888_3890 records3888_3890 :=
  aligned3888_3889.append aligned3889_3890

def missing3890_3891 : List (BitVec (edgeCount 12)) :=
  [missing3890]
abbrev records3890_3891 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3890]
theorem aligned3890_3891 :
    AlignedValid 12 3 missing3890_3891 records3890_3891 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3890
    maskCheck3890 AlignedValid.nil

def missing3891_3892 : List (BitVec (edgeCount 12)) :=
  [missing3891]
abbrev records3891_3892 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3891]
theorem aligned3891_3892 :
    AlignedValid 12 3 missing3891_3892 records3891_3892 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3891
    maskCheck3891 AlignedValid.nil

def missing3890_3892 : List (BitVec (edgeCount 12)) :=
  missing3890_3891 ++ missing3891_3892
abbrev records3890_3892 : List Blob :=
  records3890_3891 ++ records3891_3892
theorem aligned3890_3892 :
    AlignedValid 12 3 missing3890_3892 records3890_3892 :=
  aligned3890_3891.append aligned3891_3892

def missing3888_3892 : List (BitVec (edgeCount 12)) :=
  missing3888_3890 ++ missing3890_3892
abbrev records3888_3892 : List Blob :=
  records3888_3890 ++ records3890_3892
theorem aligned3888_3892 :
    AlignedValid 12 3 missing3888_3892 records3888_3892 :=
  aligned3888_3890.append aligned3890_3892

def missing3892_3893 : List (BitVec (edgeCount 12)) :=
  [missing3892]
abbrev records3892_3893 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3892]
theorem aligned3892_3893 :
    AlignedValid 12 3 missing3892_3893 records3892_3893 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3892
    maskCheck3892 AlignedValid.nil

def missing3893_3894 : List (BitVec (edgeCount 12)) :=
  [missing3893]
abbrev records3893_3894 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3893]
theorem aligned3893_3894 :
    AlignedValid 12 3 missing3893_3894 records3893_3894 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3893
    maskCheck3893 AlignedValid.nil

def missing3892_3894 : List (BitVec (edgeCount 12)) :=
  missing3892_3893 ++ missing3893_3894
abbrev records3892_3894 : List Blob :=
  records3892_3893 ++ records3893_3894
theorem aligned3892_3894 :
    AlignedValid 12 3 missing3892_3894 records3892_3894 :=
  aligned3892_3893.append aligned3893_3894

def missing3894_3895 : List (BitVec (edgeCount 12)) :=
  [missing3894]
abbrev records3894_3895 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3894]
theorem aligned3894_3895 :
    AlignedValid 12 3 missing3894_3895 records3894_3895 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3894
    maskCheck3894 AlignedValid.nil

def missing3895_3896 : List (BitVec (edgeCount 12)) :=
  [missing3895]
abbrev records3895_3896 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3895]
theorem aligned3895_3896 :
    AlignedValid 12 3 missing3895_3896 records3895_3896 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3895
    maskCheck3895 AlignedValid.nil

def missing3894_3896 : List (BitVec (edgeCount 12)) :=
  missing3894_3895 ++ missing3895_3896
abbrev records3894_3896 : List Blob :=
  records3894_3895 ++ records3895_3896
theorem aligned3894_3896 :
    AlignedValid 12 3 missing3894_3896 records3894_3896 :=
  aligned3894_3895.append aligned3895_3896

def missing3892_3896 : List (BitVec (edgeCount 12)) :=
  missing3892_3894 ++ missing3894_3896
abbrev records3892_3896 : List Blob :=
  records3892_3894 ++ records3894_3896
theorem aligned3892_3896 :
    AlignedValid 12 3 missing3892_3896 records3892_3896 :=
  aligned3892_3894.append aligned3894_3896

def missing3888_3896 : List (BitVec (edgeCount 12)) :=
  missing3888_3892 ++ missing3892_3896
abbrev records3888_3896 : List Blob :=
  records3888_3892 ++ records3892_3896
theorem aligned3888_3896 :
    AlignedValid 12 3 missing3888_3896 records3888_3896 :=
  aligned3888_3892.append aligned3892_3896

def missing3896_3897 : List (BitVec (edgeCount 12)) :=
  [missing3896]
abbrev records3896_3897 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3896]
theorem aligned3896_3897 :
    AlignedValid 12 3 missing3896_3897 records3896_3897 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3896
    maskCheck3896 AlignedValid.nil

def missing3897_3898 : List (BitVec (edgeCount 12)) :=
  [missing3897]
abbrev records3897_3898 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3897]
theorem aligned3897_3898 :
    AlignedValid 12 3 missing3897_3898 records3897_3898 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3897
    maskCheck3897 AlignedValid.nil

def missing3896_3898 : List (BitVec (edgeCount 12)) :=
  missing3896_3897 ++ missing3897_3898
abbrev records3896_3898 : List Blob :=
  records3896_3897 ++ records3897_3898
theorem aligned3896_3898 :
    AlignedValid 12 3 missing3896_3898 records3896_3898 :=
  aligned3896_3897.append aligned3897_3898

def missing3898_3899 : List (BitVec (edgeCount 12)) :=
  [missing3898]
abbrev records3898_3899 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3898]
theorem aligned3898_3899 :
    AlignedValid 12 3 missing3898_3899 records3898_3899 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3898
    maskCheck3898 AlignedValid.nil

def missing3899_3900 : List (BitVec (edgeCount 12)) :=
  [missing3899]
abbrev records3899_3900 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3899]
theorem aligned3899_3900 :
    AlignedValid 12 3 missing3899_3900 records3899_3900 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3899
    maskCheck3899 AlignedValid.nil

def missing3898_3900 : List (BitVec (edgeCount 12)) :=
  missing3898_3899 ++ missing3899_3900
abbrev records3898_3900 : List Blob :=
  records3898_3899 ++ records3899_3900
theorem aligned3898_3900 :
    AlignedValid 12 3 missing3898_3900 records3898_3900 :=
  aligned3898_3899.append aligned3899_3900

def missing3896_3900 : List (BitVec (edgeCount 12)) :=
  missing3896_3898 ++ missing3898_3900
abbrev records3896_3900 : List Blob :=
  records3896_3898 ++ records3898_3900
theorem aligned3896_3900 :
    AlignedValid 12 3 missing3896_3900 records3896_3900 :=
  aligned3896_3898.append aligned3898_3900

def missing3900_3901 : List (BitVec (edgeCount 12)) :=
  [missing3900]
abbrev records3900_3901 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3900]
theorem aligned3900_3901 :
    AlignedValid 12 3 missing3900_3901 records3900_3901 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3900
    maskCheck3900 AlignedValid.nil

def missing3901_3902 : List (BitVec (edgeCount 12)) :=
  [missing3901]
abbrev records3901_3902 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3901]
theorem aligned3901_3902 :
    AlignedValid 12 3 missing3901_3902 records3901_3902 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3901
    maskCheck3901 AlignedValid.nil

def missing3900_3902 : List (BitVec (edgeCount 12)) :=
  missing3900_3901 ++ missing3901_3902
abbrev records3900_3902 : List Blob :=
  records3900_3901 ++ records3901_3902
theorem aligned3900_3902 :
    AlignedValid 12 3 missing3900_3902 records3900_3902 :=
  aligned3900_3901.append aligned3901_3902

def missing3902_3903 : List (BitVec (edgeCount 12)) :=
  [missing3902]
abbrev records3902_3903 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3902]
theorem aligned3902_3903 :
    AlignedValid 12 3 missing3902_3903 records3902_3903 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3902
    maskCheck3902 AlignedValid.nil

def missing3903_3904 : List (BitVec (edgeCount 12)) :=
  [missing3903]
abbrev records3903_3904 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3903]
theorem aligned3903_3904 :
    AlignedValid 12 3 missing3903_3904 records3903_3904 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3903
    maskCheck3903 AlignedValid.nil

def missing3902_3904 : List (BitVec (edgeCount 12)) :=
  missing3902_3903 ++ missing3903_3904
abbrev records3902_3904 : List Blob :=
  records3902_3903 ++ records3903_3904
theorem aligned3902_3904 :
    AlignedValid 12 3 missing3902_3904 records3902_3904 :=
  aligned3902_3903.append aligned3903_3904

def missing3900_3904 : List (BitVec (edgeCount 12)) :=
  missing3900_3902 ++ missing3902_3904
abbrev records3900_3904 : List Blob :=
  records3900_3902 ++ records3902_3904
theorem aligned3900_3904 :
    AlignedValid 12 3 missing3900_3904 records3900_3904 :=
  aligned3900_3902.append aligned3902_3904

def missing3896_3904 : List (BitVec (edgeCount 12)) :=
  missing3896_3900 ++ missing3900_3904
abbrev records3896_3904 : List Blob :=
  records3896_3900 ++ records3900_3904
theorem aligned3896_3904 :
    AlignedValid 12 3 missing3896_3904 records3896_3904 :=
  aligned3896_3900.append aligned3900_3904

def missing3888_3904 : List (BitVec (edgeCount 12)) :=
  missing3888_3896 ++ missing3896_3904
abbrev records3888_3904 : List Blob :=
  records3888_3896 ++ records3896_3904
theorem aligned3888_3904 :
    AlignedValid 12 3 missing3888_3904 records3888_3904 :=
  aligned3888_3896.append aligned3896_3904

def missing3872_3904 : List (BitVec (edgeCount 12)) :=
  missing3872_3888 ++ missing3888_3904
abbrev records3872_3904 : List Blob :=
  records3872_3888 ++ records3888_3904
theorem aligned3872_3904 :
    AlignedValid 12 3 missing3872_3904 records3872_3904 :=
  aligned3872_3888.append aligned3888_3904

def missing3840_3904 : List (BitVec (edgeCount 12)) :=
  missing3840_3872 ++ missing3872_3904
abbrev records3840_3904 : List Blob :=
  records3840_3872 ++ records3872_3904
theorem aligned3840_3904 :
    AlignedValid 12 3 missing3840_3904 records3840_3904 :=
  aligned3840_3872.append aligned3872_3904

def missing3904_3905 : List (BitVec (edgeCount 12)) :=
  [missing3904]
abbrev records3904_3905 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3904]
theorem aligned3904_3905 :
    AlignedValid 12 3 missing3904_3905 records3904_3905 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3904
    maskCheck3904 AlignedValid.nil

def missing3905_3906 : List (BitVec (edgeCount 12)) :=
  [missing3905]
abbrev records3905_3906 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3905]
theorem aligned3905_3906 :
    AlignedValid 12 3 missing3905_3906 records3905_3906 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3905
    maskCheck3905 AlignedValid.nil

def missing3904_3906 : List (BitVec (edgeCount 12)) :=
  missing3904_3905 ++ missing3905_3906
abbrev records3904_3906 : List Blob :=
  records3904_3905 ++ records3905_3906
theorem aligned3904_3906 :
    AlignedValid 12 3 missing3904_3906 records3904_3906 :=
  aligned3904_3905.append aligned3905_3906

def missing3906_3907 : List (BitVec (edgeCount 12)) :=
  [missing3906]
abbrev records3906_3907 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3906]
theorem aligned3906_3907 :
    AlignedValid 12 3 missing3906_3907 records3906_3907 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3906
    maskCheck3906 AlignedValid.nil

def missing3907_3908 : List (BitVec (edgeCount 12)) :=
  [missing3907]
abbrev records3907_3908 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3907]
theorem aligned3907_3908 :
    AlignedValid 12 3 missing3907_3908 records3907_3908 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3907
    maskCheck3907 AlignedValid.nil

def missing3906_3908 : List (BitVec (edgeCount 12)) :=
  missing3906_3907 ++ missing3907_3908
abbrev records3906_3908 : List Blob :=
  records3906_3907 ++ records3907_3908
theorem aligned3906_3908 :
    AlignedValid 12 3 missing3906_3908 records3906_3908 :=
  aligned3906_3907.append aligned3907_3908

def missing3904_3908 : List (BitVec (edgeCount 12)) :=
  missing3904_3906 ++ missing3906_3908
abbrev records3904_3908 : List Blob :=
  records3904_3906 ++ records3906_3908
theorem aligned3904_3908 :
    AlignedValid 12 3 missing3904_3908 records3904_3908 :=
  aligned3904_3906.append aligned3906_3908

def missing3908_3909 : List (BitVec (edgeCount 12)) :=
  [missing3908]
abbrev records3908_3909 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3908]
theorem aligned3908_3909 :
    AlignedValid 12 3 missing3908_3909 records3908_3909 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3908
    maskCheck3908 AlignedValid.nil

def missing3909_3910 : List (BitVec (edgeCount 12)) :=
  [missing3909]
abbrev records3909_3910 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3909]
theorem aligned3909_3910 :
    AlignedValid 12 3 missing3909_3910 records3909_3910 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3909
    maskCheck3909 AlignedValid.nil

def missing3908_3910 : List (BitVec (edgeCount 12)) :=
  missing3908_3909 ++ missing3909_3910
abbrev records3908_3910 : List Blob :=
  records3908_3909 ++ records3909_3910
theorem aligned3908_3910 :
    AlignedValid 12 3 missing3908_3910 records3908_3910 :=
  aligned3908_3909.append aligned3909_3910

def missing3910_3911 : List (BitVec (edgeCount 12)) :=
  [missing3910]
abbrev records3910_3911 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3910]
theorem aligned3910_3911 :
    AlignedValid 12 3 missing3910_3911 records3910_3911 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3910
    maskCheck3910 AlignedValid.nil

def missing3911_3912 : List (BitVec (edgeCount 12)) :=
  [missing3911]
abbrev records3911_3912 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3911]
theorem aligned3911_3912 :
    AlignedValid 12 3 missing3911_3912 records3911_3912 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3911
    maskCheck3911 AlignedValid.nil

def missing3910_3912 : List (BitVec (edgeCount 12)) :=
  missing3910_3911 ++ missing3911_3912
abbrev records3910_3912 : List Blob :=
  records3910_3911 ++ records3911_3912
theorem aligned3910_3912 :
    AlignedValid 12 3 missing3910_3912 records3910_3912 :=
  aligned3910_3911.append aligned3911_3912

def missing3908_3912 : List (BitVec (edgeCount 12)) :=
  missing3908_3910 ++ missing3910_3912
abbrev records3908_3912 : List Blob :=
  records3908_3910 ++ records3910_3912
theorem aligned3908_3912 :
    AlignedValid 12 3 missing3908_3912 records3908_3912 :=
  aligned3908_3910.append aligned3910_3912

def missing3904_3912 : List (BitVec (edgeCount 12)) :=
  missing3904_3908 ++ missing3908_3912
abbrev records3904_3912 : List Blob :=
  records3904_3908 ++ records3908_3912
theorem aligned3904_3912 :
    AlignedValid 12 3 missing3904_3912 records3904_3912 :=
  aligned3904_3908.append aligned3908_3912

def missing3912_3913 : List (BitVec (edgeCount 12)) :=
  [missing3912]
abbrev records3912_3913 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3912]
theorem aligned3912_3913 :
    AlignedValid 12 3 missing3912_3913 records3912_3913 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3912
    maskCheck3912 AlignedValid.nil

def missing3913_3914 : List (BitVec (edgeCount 12)) :=
  [missing3913]
abbrev records3913_3914 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3913]
theorem aligned3913_3914 :
    AlignedValid 12 3 missing3913_3914 records3913_3914 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3913
    maskCheck3913 AlignedValid.nil

def missing3912_3914 : List (BitVec (edgeCount 12)) :=
  missing3912_3913 ++ missing3913_3914
abbrev records3912_3914 : List Blob :=
  records3912_3913 ++ records3913_3914
theorem aligned3912_3914 :
    AlignedValid 12 3 missing3912_3914 records3912_3914 :=
  aligned3912_3913.append aligned3913_3914

def missing3914_3915 : List (BitVec (edgeCount 12)) :=
  [missing3914]
abbrev records3914_3915 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3914]
theorem aligned3914_3915 :
    AlignedValid 12 3 missing3914_3915 records3914_3915 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3914
    maskCheck3914 AlignedValid.nil

def missing3915_3916 : List (BitVec (edgeCount 12)) :=
  [missing3915]
abbrev records3915_3916 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3915]
theorem aligned3915_3916 :
    AlignedValid 12 3 missing3915_3916 records3915_3916 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3915
    maskCheck3915 AlignedValid.nil

def missing3914_3916 : List (BitVec (edgeCount 12)) :=
  missing3914_3915 ++ missing3915_3916
abbrev records3914_3916 : List Blob :=
  records3914_3915 ++ records3915_3916
theorem aligned3914_3916 :
    AlignedValid 12 3 missing3914_3916 records3914_3916 :=
  aligned3914_3915.append aligned3915_3916

def missing3912_3916 : List (BitVec (edgeCount 12)) :=
  missing3912_3914 ++ missing3914_3916
abbrev records3912_3916 : List Blob :=
  records3912_3914 ++ records3914_3916
theorem aligned3912_3916 :
    AlignedValid 12 3 missing3912_3916 records3912_3916 :=
  aligned3912_3914.append aligned3914_3916

def missing3916_3917 : List (BitVec (edgeCount 12)) :=
  [missing3916]
abbrev records3916_3917 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3916]
theorem aligned3916_3917 :
    AlignedValid 12 3 missing3916_3917 records3916_3917 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3916
    maskCheck3916 AlignedValid.nil

def missing3917_3918 : List (BitVec (edgeCount 12)) :=
  [missing3917]
abbrev records3917_3918 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3917]
theorem aligned3917_3918 :
    AlignedValid 12 3 missing3917_3918 records3917_3918 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3917
    maskCheck3917 AlignedValid.nil

def missing3916_3918 : List (BitVec (edgeCount 12)) :=
  missing3916_3917 ++ missing3917_3918
abbrev records3916_3918 : List Blob :=
  records3916_3917 ++ records3917_3918
theorem aligned3916_3918 :
    AlignedValid 12 3 missing3916_3918 records3916_3918 :=
  aligned3916_3917.append aligned3917_3918

def missing3918_3919 : List (BitVec (edgeCount 12)) :=
  [missing3918]
abbrev records3918_3919 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3918]
theorem aligned3918_3919 :
    AlignedValid 12 3 missing3918_3919 records3918_3919 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3918
    maskCheck3918 AlignedValid.nil

def missing3919_3920 : List (BitVec (edgeCount 12)) :=
  [missing3919]
abbrev records3919_3920 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3919]
theorem aligned3919_3920 :
    AlignedValid 12 3 missing3919_3920 records3919_3920 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3919
    maskCheck3919 AlignedValid.nil

def missing3918_3920 : List (BitVec (edgeCount 12)) :=
  missing3918_3919 ++ missing3919_3920
abbrev records3918_3920 : List Blob :=
  records3918_3919 ++ records3919_3920
theorem aligned3918_3920 :
    AlignedValid 12 3 missing3918_3920 records3918_3920 :=
  aligned3918_3919.append aligned3919_3920

def missing3916_3920 : List (BitVec (edgeCount 12)) :=
  missing3916_3918 ++ missing3918_3920
abbrev records3916_3920 : List Blob :=
  records3916_3918 ++ records3918_3920
theorem aligned3916_3920 :
    AlignedValid 12 3 missing3916_3920 records3916_3920 :=
  aligned3916_3918.append aligned3918_3920

def missing3912_3920 : List (BitVec (edgeCount 12)) :=
  missing3912_3916 ++ missing3916_3920
abbrev records3912_3920 : List Blob :=
  records3912_3916 ++ records3916_3920
theorem aligned3912_3920 :
    AlignedValid 12 3 missing3912_3920 records3912_3920 :=
  aligned3912_3916.append aligned3916_3920

def missing3904_3920 : List (BitVec (edgeCount 12)) :=
  missing3904_3912 ++ missing3912_3920
abbrev records3904_3920 : List Blob :=
  records3904_3912 ++ records3912_3920
theorem aligned3904_3920 :
    AlignedValid 12 3 missing3904_3920 records3904_3920 :=
  aligned3904_3912.append aligned3912_3920

def missing3920_3921 : List (BitVec (edgeCount 12)) :=
  [missing3920]
abbrev records3920_3921 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3920]
theorem aligned3920_3921 :
    AlignedValid 12 3 missing3920_3921 records3920_3921 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3920
    maskCheck3920 AlignedValid.nil

def missing3921_3922 : List (BitVec (edgeCount 12)) :=
  [missing3921]
abbrev records3921_3922 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3921]
theorem aligned3921_3922 :
    AlignedValid 12 3 missing3921_3922 records3921_3922 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3921
    maskCheck3921 AlignedValid.nil

def missing3920_3922 : List (BitVec (edgeCount 12)) :=
  missing3920_3921 ++ missing3921_3922
abbrev records3920_3922 : List Blob :=
  records3920_3921 ++ records3921_3922
theorem aligned3920_3922 :
    AlignedValid 12 3 missing3920_3922 records3920_3922 :=
  aligned3920_3921.append aligned3921_3922

def missing3922_3923 : List (BitVec (edgeCount 12)) :=
  [missing3922]
abbrev records3922_3923 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3922]
theorem aligned3922_3923 :
    AlignedValid 12 3 missing3922_3923 records3922_3923 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3922
    maskCheck3922 AlignedValid.nil

def missing3923_3924 : List (BitVec (edgeCount 12)) :=
  [missing3923]
abbrev records3923_3924 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3923]
theorem aligned3923_3924 :
    AlignedValid 12 3 missing3923_3924 records3923_3924 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3923
    maskCheck3923 AlignedValid.nil

def missing3922_3924 : List (BitVec (edgeCount 12)) :=
  missing3922_3923 ++ missing3923_3924
abbrev records3922_3924 : List Blob :=
  records3922_3923 ++ records3923_3924
theorem aligned3922_3924 :
    AlignedValid 12 3 missing3922_3924 records3922_3924 :=
  aligned3922_3923.append aligned3923_3924

def missing3920_3924 : List (BitVec (edgeCount 12)) :=
  missing3920_3922 ++ missing3922_3924
abbrev records3920_3924 : List Blob :=
  records3920_3922 ++ records3922_3924
theorem aligned3920_3924 :
    AlignedValid 12 3 missing3920_3924 records3920_3924 :=
  aligned3920_3922.append aligned3922_3924

def missing3924_3925 : List (BitVec (edgeCount 12)) :=
  [missing3924]
abbrev records3924_3925 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3924]
theorem aligned3924_3925 :
    AlignedValid 12 3 missing3924_3925 records3924_3925 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3924
    maskCheck3924 AlignedValid.nil

def missing3925_3926 : List (BitVec (edgeCount 12)) :=
  [missing3925]
abbrev records3925_3926 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3925]
theorem aligned3925_3926 :
    AlignedValid 12 3 missing3925_3926 records3925_3926 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3925
    maskCheck3925 AlignedValid.nil

def missing3924_3926 : List (BitVec (edgeCount 12)) :=
  missing3924_3925 ++ missing3925_3926
abbrev records3924_3926 : List Blob :=
  records3924_3925 ++ records3925_3926
theorem aligned3924_3926 :
    AlignedValid 12 3 missing3924_3926 records3924_3926 :=
  aligned3924_3925.append aligned3925_3926

def missing3926_3927 : List (BitVec (edgeCount 12)) :=
  [missing3926]
abbrev records3926_3927 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3926]
theorem aligned3926_3927 :
    AlignedValid 12 3 missing3926_3927 records3926_3927 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3926
    maskCheck3926 AlignedValid.nil

def missing3927_3928 : List (BitVec (edgeCount 12)) :=
  [missing3927]
abbrev records3927_3928 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3927]
theorem aligned3927_3928 :
    AlignedValid 12 3 missing3927_3928 records3927_3928 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3927
    maskCheck3927 AlignedValid.nil

def missing3926_3928 : List (BitVec (edgeCount 12)) :=
  missing3926_3927 ++ missing3927_3928
abbrev records3926_3928 : List Blob :=
  records3926_3927 ++ records3927_3928
theorem aligned3926_3928 :
    AlignedValid 12 3 missing3926_3928 records3926_3928 :=
  aligned3926_3927.append aligned3927_3928

def missing3924_3928 : List (BitVec (edgeCount 12)) :=
  missing3924_3926 ++ missing3926_3928
abbrev records3924_3928 : List Blob :=
  records3924_3926 ++ records3926_3928
theorem aligned3924_3928 :
    AlignedValid 12 3 missing3924_3928 records3924_3928 :=
  aligned3924_3926.append aligned3926_3928

def missing3920_3928 : List (BitVec (edgeCount 12)) :=
  missing3920_3924 ++ missing3924_3928
abbrev records3920_3928 : List Blob :=
  records3920_3924 ++ records3924_3928
theorem aligned3920_3928 :
    AlignedValid 12 3 missing3920_3928 records3920_3928 :=
  aligned3920_3924.append aligned3924_3928

def missing3928_3929 : List (BitVec (edgeCount 12)) :=
  [missing3928]
abbrev records3928_3929 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3928]
theorem aligned3928_3929 :
    AlignedValid 12 3 missing3928_3929 records3928_3929 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3928
    maskCheck3928 AlignedValid.nil

def missing3929_3930 : List (BitVec (edgeCount 12)) :=
  [missing3929]
abbrev records3929_3930 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3929]
theorem aligned3929_3930 :
    AlignedValid 12 3 missing3929_3930 records3929_3930 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3929
    maskCheck3929 AlignedValid.nil

def missing3928_3930 : List (BitVec (edgeCount 12)) :=
  missing3928_3929 ++ missing3929_3930
abbrev records3928_3930 : List Blob :=
  records3928_3929 ++ records3929_3930
theorem aligned3928_3930 :
    AlignedValid 12 3 missing3928_3930 records3928_3930 :=
  aligned3928_3929.append aligned3929_3930

def missing3930_3931 : List (BitVec (edgeCount 12)) :=
  [missing3930]
abbrev records3930_3931 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3930]
theorem aligned3930_3931 :
    AlignedValid 12 3 missing3930_3931 records3930_3931 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3930
    maskCheck3930 AlignedValid.nil

def missing3931_3932 : List (BitVec (edgeCount 12)) :=
  [missing3931]
abbrev records3931_3932 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3931]
theorem aligned3931_3932 :
    AlignedValid 12 3 missing3931_3932 records3931_3932 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3931
    maskCheck3931 AlignedValid.nil

def missing3930_3932 : List (BitVec (edgeCount 12)) :=
  missing3930_3931 ++ missing3931_3932
abbrev records3930_3932 : List Blob :=
  records3930_3931 ++ records3931_3932
theorem aligned3930_3932 :
    AlignedValid 12 3 missing3930_3932 records3930_3932 :=
  aligned3930_3931.append aligned3931_3932

def missing3928_3932 : List (BitVec (edgeCount 12)) :=
  missing3928_3930 ++ missing3930_3932
abbrev records3928_3932 : List Blob :=
  records3928_3930 ++ records3930_3932
theorem aligned3928_3932 :
    AlignedValid 12 3 missing3928_3932 records3928_3932 :=
  aligned3928_3930.append aligned3930_3932

def missing3932_3933 : List (BitVec (edgeCount 12)) :=
  [missing3932]
abbrev records3932_3933 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3932]
theorem aligned3932_3933 :
    AlignedValid 12 3 missing3932_3933 records3932_3933 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3932
    maskCheck3932 AlignedValid.nil

def missing3933_3934 : List (BitVec (edgeCount 12)) :=
  [missing3933]
abbrev records3933_3934 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3933]
theorem aligned3933_3934 :
    AlignedValid 12 3 missing3933_3934 records3933_3934 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3933
    maskCheck3933 AlignedValid.nil

def missing3932_3934 : List (BitVec (edgeCount 12)) :=
  missing3932_3933 ++ missing3933_3934
abbrev records3932_3934 : List Blob :=
  records3932_3933 ++ records3933_3934
theorem aligned3932_3934 :
    AlignedValid 12 3 missing3932_3934 records3932_3934 :=
  aligned3932_3933.append aligned3933_3934

def missing3934_3935 : List (BitVec (edgeCount 12)) :=
  [missing3934]
abbrev records3934_3935 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3934]
theorem aligned3934_3935 :
    AlignedValid 12 3 missing3934_3935 records3934_3935 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3934
    maskCheck3934 AlignedValid.nil

def missing3935_3936 : List (BitVec (edgeCount 12)) :=
  [missing3935]
abbrev records3935_3936 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3935]
theorem aligned3935_3936 :
    AlignedValid 12 3 missing3935_3936 records3935_3936 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3935
    maskCheck3935 AlignedValid.nil

def missing3934_3936 : List (BitVec (edgeCount 12)) :=
  missing3934_3935 ++ missing3935_3936
abbrev records3934_3936 : List Blob :=
  records3934_3935 ++ records3935_3936
theorem aligned3934_3936 :
    AlignedValid 12 3 missing3934_3936 records3934_3936 :=
  aligned3934_3935.append aligned3935_3936

def missing3932_3936 : List (BitVec (edgeCount 12)) :=
  missing3932_3934 ++ missing3934_3936
abbrev records3932_3936 : List Blob :=
  records3932_3934 ++ records3934_3936
theorem aligned3932_3936 :
    AlignedValid 12 3 missing3932_3936 records3932_3936 :=
  aligned3932_3934.append aligned3934_3936

def missing3928_3936 : List (BitVec (edgeCount 12)) :=
  missing3928_3932 ++ missing3932_3936
abbrev records3928_3936 : List Blob :=
  records3928_3932 ++ records3932_3936
theorem aligned3928_3936 :
    AlignedValid 12 3 missing3928_3936 records3928_3936 :=
  aligned3928_3932.append aligned3932_3936

def missing3920_3936 : List (BitVec (edgeCount 12)) :=
  missing3920_3928 ++ missing3928_3936
abbrev records3920_3936 : List Blob :=
  records3920_3928 ++ records3928_3936
theorem aligned3920_3936 :
    AlignedValid 12 3 missing3920_3936 records3920_3936 :=
  aligned3920_3928.append aligned3928_3936

def missing3904_3936 : List (BitVec (edgeCount 12)) :=
  missing3904_3920 ++ missing3920_3936
abbrev records3904_3936 : List Blob :=
  records3904_3920 ++ records3920_3936
theorem aligned3904_3936 :
    AlignedValid 12 3 missing3904_3936 records3904_3936 :=
  aligned3904_3920.append aligned3920_3936

def missing3936_3937 : List (BitVec (edgeCount 12)) :=
  [missing3936]
abbrev records3936_3937 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3936]
theorem aligned3936_3937 :
    AlignedValid 12 3 missing3936_3937 records3936_3937 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3936
    maskCheck3936 AlignedValid.nil

def missing3937_3938 : List (BitVec (edgeCount 12)) :=
  [missing3937]
abbrev records3937_3938 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3937]
theorem aligned3937_3938 :
    AlignedValid 12 3 missing3937_3938 records3937_3938 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3937
    maskCheck3937 AlignedValid.nil

def missing3936_3938 : List (BitVec (edgeCount 12)) :=
  missing3936_3937 ++ missing3937_3938
abbrev records3936_3938 : List Blob :=
  records3936_3937 ++ records3937_3938
theorem aligned3936_3938 :
    AlignedValid 12 3 missing3936_3938 records3936_3938 :=
  aligned3936_3937.append aligned3937_3938

def missing3938_3939 : List (BitVec (edgeCount 12)) :=
  [missing3938]
abbrev records3938_3939 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3938]
theorem aligned3938_3939 :
    AlignedValid 12 3 missing3938_3939 records3938_3939 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3938
    maskCheck3938 AlignedValid.nil

def missing3939_3940 : List (BitVec (edgeCount 12)) :=
  [missing3939]
abbrev records3939_3940 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3939]
theorem aligned3939_3940 :
    AlignedValid 12 3 missing3939_3940 records3939_3940 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3939
    maskCheck3939 AlignedValid.nil

def missing3938_3940 : List (BitVec (edgeCount 12)) :=
  missing3938_3939 ++ missing3939_3940
abbrev records3938_3940 : List Blob :=
  records3938_3939 ++ records3939_3940
theorem aligned3938_3940 :
    AlignedValid 12 3 missing3938_3940 records3938_3940 :=
  aligned3938_3939.append aligned3939_3940

def missing3936_3940 : List (BitVec (edgeCount 12)) :=
  missing3936_3938 ++ missing3938_3940
abbrev records3936_3940 : List Blob :=
  records3936_3938 ++ records3938_3940
theorem aligned3936_3940 :
    AlignedValid 12 3 missing3936_3940 records3936_3940 :=
  aligned3936_3938.append aligned3938_3940

def missing3940_3941 : List (BitVec (edgeCount 12)) :=
  [missing3940]
abbrev records3940_3941 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3940]
theorem aligned3940_3941 :
    AlignedValid 12 3 missing3940_3941 records3940_3941 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3940
    maskCheck3940 AlignedValid.nil

def missing3941_3942 : List (BitVec (edgeCount 12)) :=
  [missing3941]
abbrev records3941_3942 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3941]
theorem aligned3941_3942 :
    AlignedValid 12 3 missing3941_3942 records3941_3942 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3941
    maskCheck3941 AlignedValid.nil

def missing3940_3942 : List (BitVec (edgeCount 12)) :=
  missing3940_3941 ++ missing3941_3942
abbrev records3940_3942 : List Blob :=
  records3940_3941 ++ records3941_3942
theorem aligned3940_3942 :
    AlignedValid 12 3 missing3940_3942 records3940_3942 :=
  aligned3940_3941.append aligned3941_3942

def missing3942_3943 : List (BitVec (edgeCount 12)) :=
  [missing3942]
abbrev records3942_3943 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3942]
theorem aligned3942_3943 :
    AlignedValid 12 3 missing3942_3943 records3942_3943 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3942
    maskCheck3942 AlignedValid.nil

def missing3943_3944 : List (BitVec (edgeCount 12)) :=
  [missing3943]
abbrev records3943_3944 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3943]
theorem aligned3943_3944 :
    AlignedValid 12 3 missing3943_3944 records3943_3944 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3943
    maskCheck3943 AlignedValid.nil

def missing3942_3944 : List (BitVec (edgeCount 12)) :=
  missing3942_3943 ++ missing3943_3944
abbrev records3942_3944 : List Blob :=
  records3942_3943 ++ records3943_3944
theorem aligned3942_3944 :
    AlignedValid 12 3 missing3942_3944 records3942_3944 :=
  aligned3942_3943.append aligned3943_3944

def missing3940_3944 : List (BitVec (edgeCount 12)) :=
  missing3940_3942 ++ missing3942_3944
abbrev records3940_3944 : List Blob :=
  records3940_3942 ++ records3942_3944
theorem aligned3940_3944 :
    AlignedValid 12 3 missing3940_3944 records3940_3944 :=
  aligned3940_3942.append aligned3942_3944

def missing3936_3944 : List (BitVec (edgeCount 12)) :=
  missing3936_3940 ++ missing3940_3944
abbrev records3936_3944 : List Blob :=
  records3936_3940 ++ records3940_3944
theorem aligned3936_3944 :
    AlignedValid 12 3 missing3936_3944 records3936_3944 :=
  aligned3936_3940.append aligned3940_3944

def missing3944_3945 : List (BitVec (edgeCount 12)) :=
  [missing3944]
abbrev records3944_3945 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3944]
theorem aligned3944_3945 :
    AlignedValid 12 3 missing3944_3945 records3944_3945 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3944
    maskCheck3944 AlignedValid.nil

def missing3945_3946 : List (BitVec (edgeCount 12)) :=
  [missing3945]
abbrev records3945_3946 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3945]
theorem aligned3945_3946 :
    AlignedValid 12 3 missing3945_3946 records3945_3946 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3945
    maskCheck3945 AlignedValid.nil

def missing3944_3946 : List (BitVec (edgeCount 12)) :=
  missing3944_3945 ++ missing3945_3946
abbrev records3944_3946 : List Blob :=
  records3944_3945 ++ records3945_3946
theorem aligned3944_3946 :
    AlignedValid 12 3 missing3944_3946 records3944_3946 :=
  aligned3944_3945.append aligned3945_3946

def missing3946_3947 : List (BitVec (edgeCount 12)) :=
  [missing3946]
abbrev records3946_3947 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3946]
theorem aligned3946_3947 :
    AlignedValid 12 3 missing3946_3947 records3946_3947 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3946
    maskCheck3946 AlignedValid.nil

def missing3947_3948 : List (BitVec (edgeCount 12)) :=
  [missing3947]
abbrev records3947_3948 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3947]
theorem aligned3947_3948 :
    AlignedValid 12 3 missing3947_3948 records3947_3948 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3947
    maskCheck3947 AlignedValid.nil

def missing3946_3948 : List (BitVec (edgeCount 12)) :=
  missing3946_3947 ++ missing3947_3948
abbrev records3946_3948 : List Blob :=
  records3946_3947 ++ records3947_3948
theorem aligned3946_3948 :
    AlignedValid 12 3 missing3946_3948 records3946_3948 :=
  aligned3946_3947.append aligned3947_3948

def missing3944_3948 : List (BitVec (edgeCount 12)) :=
  missing3944_3946 ++ missing3946_3948
abbrev records3944_3948 : List Blob :=
  records3944_3946 ++ records3946_3948
theorem aligned3944_3948 :
    AlignedValid 12 3 missing3944_3948 records3944_3948 :=
  aligned3944_3946.append aligned3946_3948

def missing3948_3949 : List (BitVec (edgeCount 12)) :=
  [missing3948]
abbrev records3948_3949 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3948]
theorem aligned3948_3949 :
    AlignedValid 12 3 missing3948_3949 records3948_3949 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3948
    maskCheck3948 AlignedValid.nil

def missing3949_3950 : List (BitVec (edgeCount 12)) :=
  [missing3949]
abbrev records3949_3950 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3949]
theorem aligned3949_3950 :
    AlignedValid 12 3 missing3949_3950 records3949_3950 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3949
    maskCheck3949 AlignedValid.nil

def missing3948_3950 : List (BitVec (edgeCount 12)) :=
  missing3948_3949 ++ missing3949_3950
abbrev records3948_3950 : List Blob :=
  records3948_3949 ++ records3949_3950
theorem aligned3948_3950 :
    AlignedValid 12 3 missing3948_3950 records3948_3950 :=
  aligned3948_3949.append aligned3949_3950

def missing3950_3951 : List (BitVec (edgeCount 12)) :=
  [missing3950]
abbrev records3950_3951 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3950]
theorem aligned3950_3951 :
    AlignedValid 12 3 missing3950_3951 records3950_3951 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3950
    maskCheck3950 AlignedValid.nil

def missing3951_3952 : List (BitVec (edgeCount 12)) :=
  [missing3951]
abbrev records3951_3952 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3951]
theorem aligned3951_3952 :
    AlignedValid 12 3 missing3951_3952 records3951_3952 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3951
    maskCheck3951 AlignedValid.nil

def missing3950_3952 : List (BitVec (edgeCount 12)) :=
  missing3950_3951 ++ missing3951_3952
abbrev records3950_3952 : List Blob :=
  records3950_3951 ++ records3951_3952
theorem aligned3950_3952 :
    AlignedValid 12 3 missing3950_3952 records3950_3952 :=
  aligned3950_3951.append aligned3951_3952

def missing3948_3952 : List (BitVec (edgeCount 12)) :=
  missing3948_3950 ++ missing3950_3952
abbrev records3948_3952 : List Blob :=
  records3948_3950 ++ records3950_3952
theorem aligned3948_3952 :
    AlignedValid 12 3 missing3948_3952 records3948_3952 :=
  aligned3948_3950.append aligned3950_3952

def missing3944_3952 : List (BitVec (edgeCount 12)) :=
  missing3944_3948 ++ missing3948_3952
abbrev records3944_3952 : List Blob :=
  records3944_3948 ++ records3948_3952
theorem aligned3944_3952 :
    AlignedValid 12 3 missing3944_3952 records3944_3952 :=
  aligned3944_3948.append aligned3948_3952

def missing3936_3952 : List (BitVec (edgeCount 12)) :=
  missing3936_3944 ++ missing3944_3952
abbrev records3936_3952 : List Blob :=
  records3936_3944 ++ records3944_3952
theorem aligned3936_3952 :
    AlignedValid 12 3 missing3936_3952 records3936_3952 :=
  aligned3936_3944.append aligned3944_3952

def missing3952_3953 : List (BitVec (edgeCount 12)) :=
  [missing3952]
abbrev records3952_3953 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3952]
theorem aligned3952_3953 :
    AlignedValid 12 3 missing3952_3953 records3952_3953 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3952
    maskCheck3952 AlignedValid.nil

def missing3953_3954 : List (BitVec (edgeCount 12)) :=
  [missing3953]
abbrev records3953_3954 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3953]
theorem aligned3953_3954 :
    AlignedValid 12 3 missing3953_3954 records3953_3954 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3953
    maskCheck3953 AlignedValid.nil

def missing3952_3954 : List (BitVec (edgeCount 12)) :=
  missing3952_3953 ++ missing3953_3954
abbrev records3952_3954 : List Blob :=
  records3952_3953 ++ records3953_3954
theorem aligned3952_3954 :
    AlignedValid 12 3 missing3952_3954 records3952_3954 :=
  aligned3952_3953.append aligned3953_3954

def missing3954_3955 : List (BitVec (edgeCount 12)) :=
  [missing3954]
abbrev records3954_3955 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3954]
theorem aligned3954_3955 :
    AlignedValid 12 3 missing3954_3955 records3954_3955 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3954
    maskCheck3954 AlignedValid.nil

def missing3955_3956 : List (BitVec (edgeCount 12)) :=
  [missing3955]
abbrev records3955_3956 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3955]
theorem aligned3955_3956 :
    AlignedValid 12 3 missing3955_3956 records3955_3956 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3955
    maskCheck3955 AlignedValid.nil

def missing3954_3956 : List (BitVec (edgeCount 12)) :=
  missing3954_3955 ++ missing3955_3956
abbrev records3954_3956 : List Blob :=
  records3954_3955 ++ records3955_3956
theorem aligned3954_3956 :
    AlignedValid 12 3 missing3954_3956 records3954_3956 :=
  aligned3954_3955.append aligned3955_3956

def missing3952_3956 : List (BitVec (edgeCount 12)) :=
  missing3952_3954 ++ missing3954_3956
abbrev records3952_3956 : List Blob :=
  records3952_3954 ++ records3954_3956
theorem aligned3952_3956 :
    AlignedValid 12 3 missing3952_3956 records3952_3956 :=
  aligned3952_3954.append aligned3954_3956

def missing3956_3957 : List (BitVec (edgeCount 12)) :=
  [missing3956]
abbrev records3956_3957 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3956]
theorem aligned3956_3957 :
    AlignedValid 12 3 missing3956_3957 records3956_3957 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3956
    maskCheck3956 AlignedValid.nil

def missing3957_3958 : List (BitVec (edgeCount 12)) :=
  [missing3957]
abbrev records3957_3958 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3957]
theorem aligned3957_3958 :
    AlignedValid 12 3 missing3957_3958 records3957_3958 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3957
    maskCheck3957 AlignedValid.nil

def missing3956_3958 : List (BitVec (edgeCount 12)) :=
  missing3956_3957 ++ missing3957_3958
abbrev records3956_3958 : List Blob :=
  records3956_3957 ++ records3957_3958
theorem aligned3956_3958 :
    AlignedValid 12 3 missing3956_3958 records3956_3958 :=
  aligned3956_3957.append aligned3957_3958

def missing3958_3959 : List (BitVec (edgeCount 12)) :=
  [missing3958]
abbrev records3958_3959 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3958]
theorem aligned3958_3959 :
    AlignedValid 12 3 missing3958_3959 records3958_3959 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3958
    maskCheck3958 AlignedValid.nil

def missing3959_3960 : List (BitVec (edgeCount 12)) :=
  [missing3959]
abbrev records3959_3960 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3959]
theorem aligned3959_3960 :
    AlignedValid 12 3 missing3959_3960 records3959_3960 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3959
    maskCheck3959 AlignedValid.nil

def missing3958_3960 : List (BitVec (edgeCount 12)) :=
  missing3958_3959 ++ missing3959_3960
abbrev records3958_3960 : List Blob :=
  records3958_3959 ++ records3959_3960
theorem aligned3958_3960 :
    AlignedValid 12 3 missing3958_3960 records3958_3960 :=
  aligned3958_3959.append aligned3959_3960

def missing3956_3960 : List (BitVec (edgeCount 12)) :=
  missing3956_3958 ++ missing3958_3960
abbrev records3956_3960 : List Blob :=
  records3956_3958 ++ records3958_3960
theorem aligned3956_3960 :
    AlignedValid 12 3 missing3956_3960 records3956_3960 :=
  aligned3956_3958.append aligned3958_3960

def missing3952_3960 : List (BitVec (edgeCount 12)) :=
  missing3952_3956 ++ missing3956_3960
abbrev records3952_3960 : List Blob :=
  records3952_3956 ++ records3956_3960
theorem aligned3952_3960 :
    AlignedValid 12 3 missing3952_3960 records3952_3960 :=
  aligned3952_3956.append aligned3956_3960

def missing3960_3961 : List (BitVec (edgeCount 12)) :=
  [missing3960]
abbrev records3960_3961 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3960]
theorem aligned3960_3961 :
    AlignedValid 12 3 missing3960_3961 records3960_3961 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3960
    maskCheck3960 AlignedValid.nil

def missing3961_3962 : List (BitVec (edgeCount 12)) :=
  [missing3961]
abbrev records3961_3962 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3961]
theorem aligned3961_3962 :
    AlignedValid 12 3 missing3961_3962 records3961_3962 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3961
    maskCheck3961 AlignedValid.nil

def missing3960_3962 : List (BitVec (edgeCount 12)) :=
  missing3960_3961 ++ missing3961_3962
abbrev records3960_3962 : List Blob :=
  records3960_3961 ++ records3961_3962
theorem aligned3960_3962 :
    AlignedValid 12 3 missing3960_3962 records3960_3962 :=
  aligned3960_3961.append aligned3961_3962

def missing3962_3963 : List (BitVec (edgeCount 12)) :=
  [missing3962]
abbrev records3962_3963 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3962]
theorem aligned3962_3963 :
    AlignedValid 12 3 missing3962_3963 records3962_3963 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3962
    maskCheck3962 AlignedValid.nil

def missing3963_3964 : List (BitVec (edgeCount 12)) :=
  [missing3963]
abbrev records3963_3964 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3963]
theorem aligned3963_3964 :
    AlignedValid 12 3 missing3963_3964 records3963_3964 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3963
    maskCheck3963 AlignedValid.nil

def missing3962_3964 : List (BitVec (edgeCount 12)) :=
  missing3962_3963 ++ missing3963_3964
abbrev records3962_3964 : List Blob :=
  records3962_3963 ++ records3963_3964
theorem aligned3962_3964 :
    AlignedValid 12 3 missing3962_3964 records3962_3964 :=
  aligned3962_3963.append aligned3963_3964

def missing3960_3964 : List (BitVec (edgeCount 12)) :=
  missing3960_3962 ++ missing3962_3964
abbrev records3960_3964 : List Blob :=
  records3960_3962 ++ records3962_3964
theorem aligned3960_3964 :
    AlignedValid 12 3 missing3960_3964 records3960_3964 :=
  aligned3960_3962.append aligned3962_3964

def missing3964_3965 : List (BitVec (edgeCount 12)) :=
  [missing3964]
abbrev records3964_3965 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3964]
theorem aligned3964_3965 :
    AlignedValid 12 3 missing3964_3965 records3964_3965 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3964
    maskCheck3964 AlignedValid.nil

def missing3965_3966 : List (BitVec (edgeCount 12)) :=
  [missing3965]
abbrev records3965_3966 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3965]
theorem aligned3965_3966 :
    AlignedValid 12 3 missing3965_3966 records3965_3966 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3965
    maskCheck3965 AlignedValid.nil

def missing3964_3966 : List (BitVec (edgeCount 12)) :=
  missing3964_3965 ++ missing3965_3966
abbrev records3964_3966 : List Blob :=
  records3964_3965 ++ records3965_3966
theorem aligned3964_3966 :
    AlignedValid 12 3 missing3964_3966 records3964_3966 :=
  aligned3964_3965.append aligned3965_3966

def missing3966_3967 : List (BitVec (edgeCount 12)) :=
  [missing3966]
abbrev records3966_3967 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3966]
theorem aligned3966_3967 :
    AlignedValid 12 3 missing3966_3967 records3966_3967 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3966
    maskCheck3966 AlignedValid.nil

def missing3967_3968 : List (BitVec (edgeCount 12)) :=
  [missing3967]
abbrev records3967_3968 : List Blob :=
  [StrongPackedBucketN12A3Shard030.record3967]
theorem aligned3967_3968 :
    AlignedValid 12 3 missing3967_3968 records3967_3968 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard030.check3967
    maskCheck3967 AlignedValid.nil

def missing3966_3968 : List (BitVec (edgeCount 12)) :=
  missing3966_3967 ++ missing3967_3968
abbrev records3966_3968 : List Blob :=
  records3966_3967 ++ records3967_3968
theorem aligned3966_3968 :
    AlignedValid 12 3 missing3966_3968 records3966_3968 :=
  aligned3966_3967.append aligned3967_3968

def missing3964_3968 : List (BitVec (edgeCount 12)) :=
  missing3964_3966 ++ missing3966_3968
abbrev records3964_3968 : List Blob :=
  records3964_3966 ++ records3966_3968
theorem aligned3964_3968 :
    AlignedValid 12 3 missing3964_3968 records3964_3968 :=
  aligned3964_3966.append aligned3966_3968

def missing3960_3968 : List (BitVec (edgeCount 12)) :=
  missing3960_3964 ++ missing3964_3968
abbrev records3960_3968 : List Blob :=
  records3960_3964 ++ records3964_3968
theorem aligned3960_3968 :
    AlignedValid 12 3 missing3960_3968 records3960_3968 :=
  aligned3960_3964.append aligned3964_3968

def missing3952_3968 : List (BitVec (edgeCount 12)) :=
  missing3952_3960 ++ missing3960_3968
abbrev records3952_3968 : List Blob :=
  records3952_3960 ++ records3960_3968
theorem aligned3952_3968 :
    AlignedValid 12 3 missing3952_3968 records3952_3968 :=
  aligned3952_3960.append aligned3960_3968

def missing3936_3968 : List (BitVec (edgeCount 12)) :=
  missing3936_3952 ++ missing3952_3968
abbrev records3936_3968 : List Blob :=
  records3936_3952 ++ records3952_3968
theorem aligned3936_3968 :
    AlignedValid 12 3 missing3936_3968 records3936_3968 :=
  aligned3936_3952.append aligned3952_3968

def missing3904_3968 : List (BitVec (edgeCount 12)) :=
  missing3904_3936 ++ missing3936_3968
abbrev records3904_3968 : List Blob :=
  records3904_3936 ++ records3936_3968
theorem aligned3904_3968 :
    AlignedValid 12 3 missing3904_3968 records3904_3968 :=
  aligned3904_3936.append aligned3936_3968

def missing3840_3968 : List (BitVec (edgeCount 12)) :=
  missing3840_3904 ++ missing3904_3968
abbrev records3840_3968 : List Blob :=
  records3840_3904 ++ records3904_3968
theorem aligned3840_3968 :
    AlignedValid 12 3 missing3840_3968 records3840_3968 :=
  aligned3840_3904.append aligned3904_3968

abbrev missing : List (BitVec (edgeCount 12)) := missing3840_3968
abbrev records : List Blob := records3840_3968
theorem aligned : AlignedValid 12 3 missing records := aligned3840_3968

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard030
