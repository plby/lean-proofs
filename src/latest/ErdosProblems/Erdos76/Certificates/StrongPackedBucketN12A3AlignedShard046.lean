/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A3Shard046

/-! Decode-only alignment checks for n=12, a=3, records 5888--6015. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard046

open PackedBucketCertificate

def missing5888 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5517789428247953408
theorem maskCheck5888 :
    checkMaskFor missing5888 StrongPackedBucketN12A3Shard046.record5888 = true := by
  decide

def missing5889 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5878077398437593088
theorem maskCheck5889 :
    checkMaskFor missing5889 StrongPackedBucketN12A3Shard046.record5889 = true := by
  decide

def missing5890 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6094250180551376896
theorem maskCheck5890 :
    checkMaskFor missing5890 StrongPackedBucketN12A3Shard046.record5890 = true := by
  decide

def missing5891 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8111862813613359104
theorem maskCheck5891 :
    checkMaskFor missing5891 StrongPackedBucketN12A3Shard046.record5891 = true := by
  decide

def missing5892 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9480957100333989888
theorem maskCheck5892 :
    checkMaskFor missing5892 StrongPackedBucketN12A3Shard046.record5892 = true := by
  decide

def missing5893 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9625072288409845760
theorem maskCheck5893 :
    checkMaskFor missing5893 StrongPackedBucketN12A3Shard046.record5893 = true := by
  decide

def missing5894 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9733158679466737664
theorem maskCheck5894 :
    checkMaskFor missing5894 StrongPackedBucketN12A3Shard046.record5894 = true := by
  decide

def missing5895 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10165504243694305280
theorem maskCheck5895 :
    checkMaskFor missing5895 StrongPackedBucketN12A3Shard046.record5895 = true := by
  decide

def missing5896 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10489763416864980992
theorem maskCheck5896 :
    checkMaskFor missing5896 StrongPackedBucketN12A3Shard046.record5896 = true := by
  decide

def missing5897 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10597849807921872896
theorem maskCheck5897 :
    checkMaskFor missing5897 StrongPackedBucketN12A3Shard046.record5897 = true := by
  decide

def missing5898 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10741964995997728768
theorem maskCheck5898 :
    checkMaskFor missing5898 StrongPackedBucketN12A3Shard046.record5898 = true := by
  decide

def missing5899 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12759577629059710976
theorem maskCheck5899 :
    checkMaskFor missing5899 StrongPackedBucketN12A3Shard046.record5899 = true := by
  decide

def missing5900 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13948527930685521920
theorem maskCheck5900 :
    checkMaskFor missing5900 StrongPackedBucketN12A3Shard046.record5900 = true := by
  decide

def missing5901 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27891672377024577536
theorem maskCheck5901 :
    checkMaskFor missing5901 StrongPackedBucketN12A3Shard046.record5901 = true := by
  decide

def missing5902 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13956761073754308608
theorem maskCheck5902 :
    checkMaskFor missing5902 StrongPackedBucketN12A3Shard046.record5902 = true := by
  decide

def missing5903 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23252190704647012352
theorem maskCheck5903 :
    checkMaskFor missing5903 StrongPackedBucketN12A3Shard046.record5903 = true := by
  decide

def missing5904 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117244895445123072
theorem maskCheck5904 :
    checkMaskFor missing5904 StrongPackedBucketN12A3Shard046.record5904 = true := by
  decide

def missing5905 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1981936023900258304
theorem maskCheck5905 :
    checkMaskFor missing5905 StrongPackedBucketN12A3Shard046.record5905 = true := by
  decide

def missing5906 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2198108806014042112
theorem maskCheck5906 :
    checkMaskFor missing5906 StrongPackedBucketN12A3Shard046.record5906 = true := by
  decide

def missing5907 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4143663845038096384
theorem maskCheck5907 :
    checkMaskFor missing5907 StrongPackedBucketN12A3Shard046.record5907 = true := by
  decide

def missing5908 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4215721439076024320
theorem maskCheck5908 :
    checkMaskFor missing5908 StrongPackedBucketN12A3Shard046.record5908 = true := by
  decide

def missing5909 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4251750236094988288
theorem maskCheck5909 :
    checkMaskFor missing5909 StrongPackedBucketN12A3Shard046.record5909 = true := by
  decide

def missing5910 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4467923018208772096
theorem maskCheck5910 :
    checkMaskFor missing5910 StrongPackedBucketN12A3Shard046.record5910 = true := by
  decide

def missing5911 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5152470161569087488
theorem maskCheck5911 :
    checkMaskFor missing5911 StrongPackedBucketN12A3Shard046.record5911 = true := by
  decide

def missing5912 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5440700537720799232
theorem maskCheck5912 :
    checkMaskFor missing5912 StrongPackedBucketN12A3Shard046.record5912 = true := by
  decide

def missing5913 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5584815725796655104
theorem maskCheck5913 :
    checkMaskFor missing5913 StrongPackedBucketN12A3Shard046.record5913 = true := by
  decide

def missing5914 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5656873319834583040
theorem maskCheck5914 :
    checkMaskFor missing5914 StrongPackedBucketN12A3Shard046.record5914 = true := by
  decide

def missing5915 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5692902116853547008
theorem maskCheck5915 :
    checkMaskFor missing5915 StrongPackedBucketN12A3Shard046.record5915 = true := by
  decide

def missing5916 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6449506854251790336
theorem maskCheck5916 :
    checkMaskFor missing5916 StrongPackedBucketN12A3Shard046.record5916 = true := by
  decide

def missing5917 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6521564448289718272
theorem maskCheck5917 :
    checkMaskFor missing5917 StrongPackedBucketN12A3Shard046.record5917 = true := by
  decide

def missing5918 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6557593245308682240
theorem maskCheck5918 :
    checkMaskFor missing5918 StrongPackedBucketN12A3Shard046.record5918 = true := by
  decide

def missing5919 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6665679636365574144
theorem maskCheck5919 :
    checkMaskFor missing5919 StrongPackedBucketN12A3Shard046.record5919 = true := by
  decide

def missing5920 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6773766027422466048
theorem maskCheck5920 :
    checkMaskFor missing5920 StrongPackedBucketN12A3Shard046.record5920 = true := by
  decide

def missing5921 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8683292269427556352
theorem maskCheck5921 :
    checkMaskFor missing5921 StrongPackedBucketN12A3Shard046.record5921 = true := by
  decide

def missing5922 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8791378660484448256
theorem maskCheck5922 :
    checkMaskFor missing5922 StrongPackedBucketN12A3Shard046.record5922 = true := by
  decide

def missing5923 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14087611822272151552
theorem maskCheck5923 :
    checkMaskFor missing5923 StrongPackedBucketN12A3Shard046.record5923 = true := by
  decide

def missing5924 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14303784604385935360
theorem maskCheck5924 :
    checkMaskFor missing5924 StrongPackedBucketN12A3Shard046.record5924 = true := by
  decide

def missing5925 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14519957386499719168
theorem maskCheck5925 :
    checkMaskFor missing5925 StrongPackedBucketN12A3Shard046.record5925 = true := by
  decide

def missing5926 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14628043777556611072
theorem maskCheck5926 :
    checkMaskFor missing5926 StrongPackedBucketN12A3Shard046.record5926 = true := by
  decide

def missing5927 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14844216559670394880
theorem maskCheck5927 :
    checkMaskFor missing5927 StrongPackedBucketN12A3Shard046.record5927 = true := by
  decide

def missing5928 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18987528216851251200
theorem maskCheck5928 :
    checkMaskFor missing5928 StrongPackedBucketN12A3Shard046.record5928 = true := by
  decide

def missing5929 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19275758593002962944
theorem maskCheck5929 :
    checkMaskFor missing5929 StrongPackedBucketN12A3Shard046.record5929 = true := by
  decide

def missing5930 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19419873781078818816
theorem maskCheck5930 :
    checkMaskFor missing5930 StrongPackedBucketN12A3Shard046.record5930 = true := by
  decide

def missing5931 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19491931375116746752
theorem maskCheck5931 :
    checkMaskFor missing5931 StrongPackedBucketN12A3Shard046.record5931 = true := by
  decide

def missing5932 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20284564909533954048
theorem maskCheck5932 :
    checkMaskFor missing5932 StrongPackedBucketN12A3Shard046.record5932 = true := by
  decide

def missing5933 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20356622503571881984
theorem maskCheck5933 :
    checkMaskFor missing5933 StrongPackedBucketN12A3Shard046.record5933 = true := by
  decide

def missing5934 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20500737691647737856
theorem maskCheck5934 :
    checkMaskFor missing5934 StrongPackedBucketN12A3Shard046.record5934 = true := by
  decide

def missing5935 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22518350324709720064
theorem maskCheck5935 :
    checkMaskFor missing5935 StrongPackedBucketN12A3Shard046.record5935 = true := by
  decide

def missing5936 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23310983859126927360
theorem maskCheck5936 :
    checkMaskFor missing5936 StrongPackedBucketN12A3Shard046.record5936 = true := by
  decide

def missing5937 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23527156641240711168
theorem maskCheck5937 :
    checkMaskFor missing5937 StrongPackedBucketN12A3Shard046.record5937 = true := by
  decide

def missing5938 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23815387017392422912
theorem maskCheck5938 :
    checkMaskFor missing5938 StrongPackedBucketN12A3Shard046.record5938 = true := by
  decide

def missing5939 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27922669877554315264
theorem maskCheck5939 :
    checkMaskFor missing5939 StrongPackedBucketN12A3Shard046.record5939 = true := by
  decide

def missing5940 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28066785065630171136
theorem maskCheck5940 :
    checkMaskFor missing5940 StrongPackedBucketN12A3Shard046.record5940 = true := by
  decide

def missing5941 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28138842659668099072
theorem maskCheck5941 :
    checkMaskFor missing5941 StrongPackedBucketN12A3Shard046.record5941 = true := by
  decide

def missing5942 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28355015441781882880
theorem maskCheck5942 :
    checkMaskFor missing5942 StrongPackedBucketN12A3Shard046.record5942 = true := by
  decide

def missing5943 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28571188223895666688
theorem maskCheck5943 :
    checkMaskFor missing5943 StrongPackedBucketN12A3Shard046.record5943 = true := by
  decide

def missing5944 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55592785988118642688
theorem maskCheck5944 :
    checkMaskFor missing5944 StrongPackedBucketN12A3Shard046.record5944 = true := by
  decide

def missing5945 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56025131552346210304
theorem maskCheck5945 :
    checkMaskFor missing5945 StrongPackedBucketN12A3Shard046.record5945 = true := by
  decide

def missing5946 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117315264189300736
theorem maskCheck5946 :
    checkMaskFor missing5946 StrongPackedBucketN12A3Shard046.record5946 = true := by
  decide

def missing5947 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1982006392644435968
theorem maskCheck5947 :
    checkMaskFor missing5947 StrongPackedBucketN12A3Shard046.record5947 = true := by
  decide

def missing5948 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2126121580720291840
theorem maskCheck5948 :
    checkMaskFor missing5948 StrongPackedBucketN12A3Shard046.record5948 = true := by
  decide

def missing5949 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2198179174758219776
theorem maskCheck5949 :
    checkMaskFor missing5949 StrongPackedBucketN12A3Shard046.record5949 = true := by
  decide

def missing5950 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2234207971777183744
theorem maskCheck5950 :
    checkMaskFor missing5950 StrongPackedBucketN12A3Shard046.record5950 = true := by
  decide

def missing5951 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4143734213782274048
theorem maskCheck5951 :
    checkMaskFor missing5951 StrongPackedBucketN12A3Shard046.record5951 = true := by
  decide

def missing5952 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4215791807820201984
theorem maskCheck5952 :
    checkMaskFor missing5952 StrongPackedBucketN12A3Shard046.record5952 = true := by
  decide

def missing5953 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4251820604839165952
theorem maskCheck5953 :
    checkMaskFor missing5953 StrongPackedBucketN12A3Shard046.record5953 = true := by
  decide

def missing5954 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4359906995896057856
theorem maskCheck5954 :
    checkMaskFor missing5954 StrongPackedBucketN12A3Shard046.record5954 = true := by
  decide

def missing5955 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4395935792915021824
theorem maskCheck5955 :
    checkMaskFor missing5955 StrongPackedBucketN12A3Shard046.record5955 = true := by
  decide

def missing5956 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4467993386952949760
theorem maskCheck5956 :
    checkMaskFor missing5956 StrongPackedBucketN12A3Shard046.record5956 = true := by
  decide

def missing5957 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5152540530313265152
theorem maskCheck5957 :
    checkMaskFor missing5957 StrongPackedBucketN12A3Shard046.record5957 = true := by
  decide

def missing5958 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5440770906464976896
theorem maskCheck5958 :
    checkMaskFor missing5958 StrongPackedBucketN12A3Shard046.record5958 = true := by
  decide

def missing5959 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5584886094540832768
theorem maskCheck5959 :
    checkMaskFor missing5959 StrongPackedBucketN12A3Shard046.record5959 = true := by
  decide

def missing5960 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5656943688578760704
theorem maskCheck5960 :
    checkMaskFor missing5960 StrongPackedBucketN12A3Shard046.record5960 = true := by
  decide

def missing5961 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5692972485597724672
theorem maskCheck5961 :
    checkMaskFor missing5961 StrongPackedBucketN12A3Shard046.record5961 = true := by
  decide

def missing5962 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6449577222995968000
theorem maskCheck5962 :
    checkMaskFor missing5962 StrongPackedBucketN12A3Shard046.record5962 = true := by
  decide

def missing5963 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6521634817033895936
theorem maskCheck5963 :
    checkMaskFor missing5963 StrongPackedBucketN12A3Shard046.record5963 = true := by
  decide

def missing5964 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6557663614052859904
theorem maskCheck5964 :
    checkMaskFor missing5964 StrongPackedBucketN12A3Shard046.record5964 = true := by
  decide

def missing5965 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6665750005109751808
theorem maskCheck5965 :
    checkMaskFor missing5965 StrongPackedBucketN12A3Shard046.record5965 = true := by
  decide

def missing5966 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6701778802128715776
theorem maskCheck5966 :
    checkMaskFor missing5966 StrongPackedBucketN12A3Shard046.record5966 = true := by
  decide

def missing5967 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6773836396166643712
theorem maskCheck5967 :
    checkMaskFor missing5967 StrongPackedBucketN12A3Shard046.record5967 = true := by
  decide

def missing5968 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8683362638171734016
theorem maskCheck5968 :
    checkMaskFor missing5968 StrongPackedBucketN12A3Shard046.record5968 = true := by
  decide

def missing5969 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8791449029228625920
theorem maskCheck5969 :
    checkMaskFor missing5969 StrongPackedBucketN12A3Shard046.record5969 = true := by
  decide

def missing5970 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8935564217304481792
theorem maskCheck5970 :
    checkMaskFor missing5970 StrongPackedBucketN12A3Shard046.record5970 = true := by
  decide

def missing5971 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9764226548740653056
theorem maskCheck5971 :
    checkMaskFor missing5971 StrongPackedBucketN12A3Shard046.record5971 = true := by
  decide

def missing5972 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10052456924892364800
theorem maskCheck5972 :
    checkMaskFor missing5972 StrongPackedBucketN12A3Shard046.record5972 = true := by
  decide

def missing5973 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10196572112968220672
theorem maskCheck5973 :
    checkMaskFor missing5973 StrongPackedBucketN12A3Shard046.record5973 = true := by
  decide

def missing5974 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10304658504025112576
theorem maskCheck5974 :
    checkMaskFor missing5974 StrongPackedBucketN12A3Shard046.record5974 = true := by
  decide

def missing5975 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11061263241423355904
theorem maskCheck5975 :
    checkMaskFor missing5975 StrongPackedBucketN12A3Shard046.record5975 = true := by
  decide

def missing5976 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11169349632480247808
theorem maskCheck5976 :
    checkMaskFor missing5976 StrongPackedBucketN12A3Shard046.record5976 = true := by
  decide

def missing5977 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11313464820556103680
theorem maskCheck5977 :
    checkMaskFor missing5977 StrongPackedBucketN12A3Shard046.record5977 = true := by
  decide

def missing5978 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13331077453618085888
theorem maskCheck5978 :
    checkMaskFor missing5978 StrongPackedBucketN12A3Shard046.record5978 = true := by
  decide

def missing5979 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14087682191016329216
theorem maskCheck5979 :
    checkMaskFor missing5979 StrongPackedBucketN12A3Shard046.record5979 = true := by
  decide

def missing5980 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14231797379092185088
theorem maskCheck5980 :
    checkMaskFor missing5980 StrongPackedBucketN12A3Shard046.record5980 = true := by
  decide

def missing5981 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14339883770149076992
theorem maskCheck5981 :
    checkMaskFor missing5981 StrongPackedBucketN12A3Shard046.record5981 = true := by
  decide

def missing5982 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14520027755243896832
theorem maskCheck5982 :
    checkMaskFor missing5982 StrongPackedBucketN12A3Shard046.record5982 = true := by
  decide

def missing5983 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14628114146300788736
theorem maskCheck5983 :
    checkMaskFor missing5983 StrongPackedBucketN12A3Shard046.record5983 = true := by
  decide

def missing5984 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14772229334376644608
theorem maskCheck5984 :
    checkMaskFor missing5984 StrongPackedBucketN12A3Shard046.record5984 = true := by
  decide

def missing5985 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18987598585595428864
theorem maskCheck5985 :
    checkMaskFor missing5985 StrongPackedBucketN12A3Shard046.record5985 = true := by
  decide

def missing5986 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19275828961747140608
theorem maskCheck5986 :
    checkMaskFor missing5986 StrongPackedBucketN12A3Shard046.record5986 = true := by
  decide

def missing5987 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19419944149822996480
theorem maskCheck5987 :
    checkMaskFor missing5987 StrongPackedBucketN12A3Shard046.record5987 = true := by
  decide

def missing5988 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19492001743860924416
theorem maskCheck5988 :
    checkMaskFor missing5988 StrongPackedBucketN12A3Shard046.record5988 = true := by
  decide

def missing5989 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19528030540879888384
theorem maskCheck5989 :
    checkMaskFor missing5989 StrongPackedBucketN12A3Shard046.record5989 = true := by
  decide

def missing5990 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20284635278278131712
theorem maskCheck5990 :
    checkMaskFor missing5990 StrongPackedBucketN12A3Shard046.record5990 = true := by
  decide

def missing5991 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20356692872316059648
theorem maskCheck5991 :
    checkMaskFor missing5991 StrongPackedBucketN12A3Shard046.record5991 = true := by
  decide

def missing5992 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20392721669335023616
theorem maskCheck5992 :
    checkMaskFor missing5992 StrongPackedBucketN12A3Shard046.record5992 = true := by
  decide

def missing5993 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20500808060391915520
theorem maskCheck5993 :
    checkMaskFor missing5993 StrongPackedBucketN12A3Shard046.record5993 = true := by
  decide

def missing5994 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20608894451448807424
theorem maskCheck5994 :
    checkMaskFor missing5994 StrongPackedBucketN12A3Shard046.record5994 = true := by
  decide

def missing5995 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22518420693453897728
theorem maskCheck5995 :
    checkMaskFor missing5995 StrongPackedBucketN12A3Shard046.record5995 = true := by
  decide

def missing5996 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22626507084510789632
theorem maskCheck5996 :
    checkMaskFor missing5996 StrongPackedBucketN12A3Shard046.record5996 = true := by
  decide

def missing5997 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23311054227871105024
theorem maskCheck5997 :
    checkMaskFor missing5997 StrongPackedBucketN12A3Shard046.record5997 = true := by
  decide

def missing5998 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23455169415946960896
theorem maskCheck5998 :
    checkMaskFor missing5998 StrongPackedBucketN12A3Shard046.record5998 = true := by
  decide

def missing5999 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23527227009984888832
theorem maskCheck5999 :
    checkMaskFor missing5999 StrongPackedBucketN12A3Shard046.record5999 = true := by
  decide

def missing6000 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23563255807003852800
theorem maskCheck6000 :
    checkMaskFor missing6000 StrongPackedBucketN12A3Shard046.record6000 = true := by
  decide

def missing6001 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23743399792098672640
theorem maskCheck6001 :
    checkMaskFor missing6001 StrongPackedBucketN12A3Shard046.record6001 = true := by
  decide

def missing6002 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23815457386136600576
theorem maskCheck6002 :
    checkMaskFor missing6002 StrongPackedBucketN12A3Shard046.record6002 = true := by
  decide

def missing6003 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23959572574212456448
theorem maskCheck6003 :
    checkMaskFor missing6003 StrongPackedBucketN12A3Shard046.record6003 = true := by
  decide

def missing6004 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24067658965269348352
theorem maskCheck6004 :
    checkMaskFor missing6004 StrongPackedBucketN12A3Shard046.record6004 = true := by
  decide

def missing6005 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24824263702667591680
theorem maskCheck6005 :
    checkMaskFor missing6005 StrongPackedBucketN12A3Shard046.record6005 = true := by
  decide

def missing6006 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27922740246298492928
theorem maskCheck6006 :
    checkMaskFor missing6006 StrongPackedBucketN12A3Shard046.record6006 = true := by
  decide

def missing6007 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28066855434374348800
theorem maskCheck6007 :
    checkMaskFor missing6007 StrongPackedBucketN12A3Shard046.record6007 = true := by
  decide

def missing6008 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28174941825431240704
theorem maskCheck6008 :
    checkMaskFor missing6008 StrongPackedBucketN12A3Shard046.record6008 = true := by
  decide

def missing6009 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28355085810526060544
theorem maskCheck6009 :
    checkMaskFor missing6009 StrongPackedBucketN12A3Shard046.record6009 = true := by
  decide

def missing6010 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28463172201582952448
theorem maskCheck6010 :
    checkMaskFor missing6010 StrongPackedBucketN12A3Shard046.record6010 = true := by
  decide

def missing6011 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32390311076650024960
theorem maskCheck6011 :
    checkMaskFor missing6011 StrongPackedBucketN12A3Shard046.record6011 = true := by
  decide

def missing6012 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37434342659304980480
theorem maskCheck6012 :
    checkMaskFor missing6012 StrongPackedBucketN12A3Shard046.record6012 = true := by
  decide

def missing6013 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37722573035456692224
theorem maskCheck6013 :
    checkMaskFor missing6013 StrongPackedBucketN12A3Shard046.record6013 = true := by
  decide

def missing6014 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37866688223532548096
theorem maskCheck6014 :
    checkMaskFor missing6014 StrongPackedBucketN12A3Shard046.record6014 = true := by
  decide

def missing6015 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37938745817570476032
theorem maskCheck6015 :
    checkMaskFor missing6015 StrongPackedBucketN12A3Shard046.record6015 = true := by
  decide

def missing5888_5889 : List (BitVec (edgeCount 12)) :=
  [missing5888]
abbrev records5888_5889 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5888]
theorem aligned5888_5889 :
    AlignedValid 12 3 missing5888_5889 records5888_5889 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5888
    maskCheck5888 AlignedValid.nil

def missing5889_5890 : List (BitVec (edgeCount 12)) :=
  [missing5889]
abbrev records5889_5890 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5889]
theorem aligned5889_5890 :
    AlignedValid 12 3 missing5889_5890 records5889_5890 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5889
    maskCheck5889 AlignedValid.nil

def missing5888_5890 : List (BitVec (edgeCount 12)) :=
  missing5888_5889 ++ missing5889_5890
abbrev records5888_5890 : List Blob :=
  records5888_5889 ++ records5889_5890
theorem aligned5888_5890 :
    AlignedValid 12 3 missing5888_5890 records5888_5890 :=
  aligned5888_5889.append aligned5889_5890

def missing5890_5891 : List (BitVec (edgeCount 12)) :=
  [missing5890]
abbrev records5890_5891 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5890]
theorem aligned5890_5891 :
    AlignedValid 12 3 missing5890_5891 records5890_5891 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5890
    maskCheck5890 AlignedValid.nil

def missing5891_5892 : List (BitVec (edgeCount 12)) :=
  [missing5891]
abbrev records5891_5892 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5891]
theorem aligned5891_5892 :
    AlignedValid 12 3 missing5891_5892 records5891_5892 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5891
    maskCheck5891 AlignedValid.nil

def missing5890_5892 : List (BitVec (edgeCount 12)) :=
  missing5890_5891 ++ missing5891_5892
abbrev records5890_5892 : List Blob :=
  records5890_5891 ++ records5891_5892
theorem aligned5890_5892 :
    AlignedValid 12 3 missing5890_5892 records5890_5892 :=
  aligned5890_5891.append aligned5891_5892

def missing5888_5892 : List (BitVec (edgeCount 12)) :=
  missing5888_5890 ++ missing5890_5892
abbrev records5888_5892 : List Blob :=
  records5888_5890 ++ records5890_5892
theorem aligned5888_5892 :
    AlignedValid 12 3 missing5888_5892 records5888_5892 :=
  aligned5888_5890.append aligned5890_5892

def missing5892_5893 : List (BitVec (edgeCount 12)) :=
  [missing5892]
abbrev records5892_5893 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5892]
theorem aligned5892_5893 :
    AlignedValid 12 3 missing5892_5893 records5892_5893 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5892
    maskCheck5892 AlignedValid.nil

def missing5893_5894 : List (BitVec (edgeCount 12)) :=
  [missing5893]
abbrev records5893_5894 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5893]
theorem aligned5893_5894 :
    AlignedValid 12 3 missing5893_5894 records5893_5894 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5893
    maskCheck5893 AlignedValid.nil

def missing5892_5894 : List (BitVec (edgeCount 12)) :=
  missing5892_5893 ++ missing5893_5894
abbrev records5892_5894 : List Blob :=
  records5892_5893 ++ records5893_5894
theorem aligned5892_5894 :
    AlignedValid 12 3 missing5892_5894 records5892_5894 :=
  aligned5892_5893.append aligned5893_5894

def missing5894_5895 : List (BitVec (edgeCount 12)) :=
  [missing5894]
abbrev records5894_5895 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5894]
theorem aligned5894_5895 :
    AlignedValid 12 3 missing5894_5895 records5894_5895 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5894
    maskCheck5894 AlignedValid.nil

def missing5895_5896 : List (BitVec (edgeCount 12)) :=
  [missing5895]
abbrev records5895_5896 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5895]
theorem aligned5895_5896 :
    AlignedValid 12 3 missing5895_5896 records5895_5896 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5895
    maskCheck5895 AlignedValid.nil

def missing5894_5896 : List (BitVec (edgeCount 12)) :=
  missing5894_5895 ++ missing5895_5896
abbrev records5894_5896 : List Blob :=
  records5894_5895 ++ records5895_5896
theorem aligned5894_5896 :
    AlignedValid 12 3 missing5894_5896 records5894_5896 :=
  aligned5894_5895.append aligned5895_5896

def missing5892_5896 : List (BitVec (edgeCount 12)) :=
  missing5892_5894 ++ missing5894_5896
abbrev records5892_5896 : List Blob :=
  records5892_5894 ++ records5894_5896
theorem aligned5892_5896 :
    AlignedValid 12 3 missing5892_5896 records5892_5896 :=
  aligned5892_5894.append aligned5894_5896

def missing5888_5896 : List (BitVec (edgeCount 12)) :=
  missing5888_5892 ++ missing5892_5896
abbrev records5888_5896 : List Blob :=
  records5888_5892 ++ records5892_5896
theorem aligned5888_5896 :
    AlignedValid 12 3 missing5888_5896 records5888_5896 :=
  aligned5888_5892.append aligned5892_5896

def missing5896_5897 : List (BitVec (edgeCount 12)) :=
  [missing5896]
abbrev records5896_5897 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5896]
theorem aligned5896_5897 :
    AlignedValid 12 3 missing5896_5897 records5896_5897 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5896
    maskCheck5896 AlignedValid.nil

def missing5897_5898 : List (BitVec (edgeCount 12)) :=
  [missing5897]
abbrev records5897_5898 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5897]
theorem aligned5897_5898 :
    AlignedValid 12 3 missing5897_5898 records5897_5898 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5897
    maskCheck5897 AlignedValid.nil

def missing5896_5898 : List (BitVec (edgeCount 12)) :=
  missing5896_5897 ++ missing5897_5898
abbrev records5896_5898 : List Blob :=
  records5896_5897 ++ records5897_5898
theorem aligned5896_5898 :
    AlignedValid 12 3 missing5896_5898 records5896_5898 :=
  aligned5896_5897.append aligned5897_5898

def missing5898_5899 : List (BitVec (edgeCount 12)) :=
  [missing5898]
abbrev records5898_5899 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5898]
theorem aligned5898_5899 :
    AlignedValid 12 3 missing5898_5899 records5898_5899 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5898
    maskCheck5898 AlignedValid.nil

def missing5899_5900 : List (BitVec (edgeCount 12)) :=
  [missing5899]
abbrev records5899_5900 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5899]
theorem aligned5899_5900 :
    AlignedValid 12 3 missing5899_5900 records5899_5900 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5899
    maskCheck5899 AlignedValid.nil

def missing5898_5900 : List (BitVec (edgeCount 12)) :=
  missing5898_5899 ++ missing5899_5900
abbrev records5898_5900 : List Blob :=
  records5898_5899 ++ records5899_5900
theorem aligned5898_5900 :
    AlignedValid 12 3 missing5898_5900 records5898_5900 :=
  aligned5898_5899.append aligned5899_5900

def missing5896_5900 : List (BitVec (edgeCount 12)) :=
  missing5896_5898 ++ missing5898_5900
abbrev records5896_5900 : List Blob :=
  records5896_5898 ++ records5898_5900
theorem aligned5896_5900 :
    AlignedValid 12 3 missing5896_5900 records5896_5900 :=
  aligned5896_5898.append aligned5898_5900

def missing5900_5901 : List (BitVec (edgeCount 12)) :=
  [missing5900]
abbrev records5900_5901 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5900]
theorem aligned5900_5901 :
    AlignedValid 12 3 missing5900_5901 records5900_5901 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5900
    maskCheck5900 AlignedValid.nil

def missing5901_5902 : List (BitVec (edgeCount 12)) :=
  [missing5901]
abbrev records5901_5902 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5901]
theorem aligned5901_5902 :
    AlignedValid 12 3 missing5901_5902 records5901_5902 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5901
    maskCheck5901 AlignedValid.nil

def missing5900_5902 : List (BitVec (edgeCount 12)) :=
  missing5900_5901 ++ missing5901_5902
abbrev records5900_5902 : List Blob :=
  records5900_5901 ++ records5901_5902
theorem aligned5900_5902 :
    AlignedValid 12 3 missing5900_5902 records5900_5902 :=
  aligned5900_5901.append aligned5901_5902

def missing5902_5903 : List (BitVec (edgeCount 12)) :=
  [missing5902]
abbrev records5902_5903 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5902]
theorem aligned5902_5903 :
    AlignedValid 12 3 missing5902_5903 records5902_5903 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5902
    maskCheck5902 AlignedValid.nil

def missing5903_5904 : List (BitVec (edgeCount 12)) :=
  [missing5903]
abbrev records5903_5904 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5903]
theorem aligned5903_5904 :
    AlignedValid 12 3 missing5903_5904 records5903_5904 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5903
    maskCheck5903 AlignedValid.nil

def missing5902_5904 : List (BitVec (edgeCount 12)) :=
  missing5902_5903 ++ missing5903_5904
abbrev records5902_5904 : List Blob :=
  records5902_5903 ++ records5903_5904
theorem aligned5902_5904 :
    AlignedValid 12 3 missing5902_5904 records5902_5904 :=
  aligned5902_5903.append aligned5903_5904

def missing5900_5904 : List (BitVec (edgeCount 12)) :=
  missing5900_5902 ++ missing5902_5904
abbrev records5900_5904 : List Blob :=
  records5900_5902 ++ records5902_5904
theorem aligned5900_5904 :
    AlignedValid 12 3 missing5900_5904 records5900_5904 :=
  aligned5900_5902.append aligned5902_5904

def missing5896_5904 : List (BitVec (edgeCount 12)) :=
  missing5896_5900 ++ missing5900_5904
abbrev records5896_5904 : List Blob :=
  records5896_5900 ++ records5900_5904
theorem aligned5896_5904 :
    AlignedValid 12 3 missing5896_5904 records5896_5904 :=
  aligned5896_5900.append aligned5900_5904

def missing5888_5904 : List (BitVec (edgeCount 12)) :=
  missing5888_5896 ++ missing5896_5904
abbrev records5888_5904 : List Blob :=
  records5888_5896 ++ records5896_5904
theorem aligned5888_5904 :
    AlignedValid 12 3 missing5888_5904 records5888_5904 :=
  aligned5888_5896.append aligned5896_5904

def missing5904_5905 : List (BitVec (edgeCount 12)) :=
  [missing5904]
abbrev records5904_5905 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5904]
theorem aligned5904_5905 :
    AlignedValid 12 3 missing5904_5905 records5904_5905 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5904
    maskCheck5904 AlignedValid.nil

def missing5905_5906 : List (BitVec (edgeCount 12)) :=
  [missing5905]
abbrev records5905_5906 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5905]
theorem aligned5905_5906 :
    AlignedValid 12 3 missing5905_5906 records5905_5906 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5905
    maskCheck5905 AlignedValid.nil

def missing5904_5906 : List (BitVec (edgeCount 12)) :=
  missing5904_5905 ++ missing5905_5906
abbrev records5904_5906 : List Blob :=
  records5904_5905 ++ records5905_5906
theorem aligned5904_5906 :
    AlignedValid 12 3 missing5904_5906 records5904_5906 :=
  aligned5904_5905.append aligned5905_5906

def missing5906_5907 : List (BitVec (edgeCount 12)) :=
  [missing5906]
abbrev records5906_5907 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5906]
theorem aligned5906_5907 :
    AlignedValid 12 3 missing5906_5907 records5906_5907 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5906
    maskCheck5906 AlignedValid.nil

def missing5907_5908 : List (BitVec (edgeCount 12)) :=
  [missing5907]
abbrev records5907_5908 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5907]
theorem aligned5907_5908 :
    AlignedValid 12 3 missing5907_5908 records5907_5908 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5907
    maskCheck5907 AlignedValid.nil

def missing5906_5908 : List (BitVec (edgeCount 12)) :=
  missing5906_5907 ++ missing5907_5908
abbrev records5906_5908 : List Blob :=
  records5906_5907 ++ records5907_5908
theorem aligned5906_5908 :
    AlignedValid 12 3 missing5906_5908 records5906_5908 :=
  aligned5906_5907.append aligned5907_5908

def missing5904_5908 : List (BitVec (edgeCount 12)) :=
  missing5904_5906 ++ missing5906_5908
abbrev records5904_5908 : List Blob :=
  records5904_5906 ++ records5906_5908
theorem aligned5904_5908 :
    AlignedValid 12 3 missing5904_5908 records5904_5908 :=
  aligned5904_5906.append aligned5906_5908

def missing5908_5909 : List (BitVec (edgeCount 12)) :=
  [missing5908]
abbrev records5908_5909 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5908]
theorem aligned5908_5909 :
    AlignedValid 12 3 missing5908_5909 records5908_5909 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5908
    maskCheck5908 AlignedValid.nil

def missing5909_5910 : List (BitVec (edgeCount 12)) :=
  [missing5909]
abbrev records5909_5910 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5909]
theorem aligned5909_5910 :
    AlignedValid 12 3 missing5909_5910 records5909_5910 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5909
    maskCheck5909 AlignedValid.nil

def missing5908_5910 : List (BitVec (edgeCount 12)) :=
  missing5908_5909 ++ missing5909_5910
abbrev records5908_5910 : List Blob :=
  records5908_5909 ++ records5909_5910
theorem aligned5908_5910 :
    AlignedValid 12 3 missing5908_5910 records5908_5910 :=
  aligned5908_5909.append aligned5909_5910

def missing5910_5911 : List (BitVec (edgeCount 12)) :=
  [missing5910]
abbrev records5910_5911 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5910]
theorem aligned5910_5911 :
    AlignedValid 12 3 missing5910_5911 records5910_5911 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5910
    maskCheck5910 AlignedValid.nil

def missing5911_5912 : List (BitVec (edgeCount 12)) :=
  [missing5911]
abbrev records5911_5912 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5911]
theorem aligned5911_5912 :
    AlignedValid 12 3 missing5911_5912 records5911_5912 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5911
    maskCheck5911 AlignedValid.nil

def missing5910_5912 : List (BitVec (edgeCount 12)) :=
  missing5910_5911 ++ missing5911_5912
abbrev records5910_5912 : List Blob :=
  records5910_5911 ++ records5911_5912
theorem aligned5910_5912 :
    AlignedValid 12 3 missing5910_5912 records5910_5912 :=
  aligned5910_5911.append aligned5911_5912

def missing5908_5912 : List (BitVec (edgeCount 12)) :=
  missing5908_5910 ++ missing5910_5912
abbrev records5908_5912 : List Blob :=
  records5908_5910 ++ records5910_5912
theorem aligned5908_5912 :
    AlignedValid 12 3 missing5908_5912 records5908_5912 :=
  aligned5908_5910.append aligned5910_5912

def missing5904_5912 : List (BitVec (edgeCount 12)) :=
  missing5904_5908 ++ missing5908_5912
abbrev records5904_5912 : List Blob :=
  records5904_5908 ++ records5908_5912
theorem aligned5904_5912 :
    AlignedValid 12 3 missing5904_5912 records5904_5912 :=
  aligned5904_5908.append aligned5908_5912

def missing5912_5913 : List (BitVec (edgeCount 12)) :=
  [missing5912]
abbrev records5912_5913 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5912]
theorem aligned5912_5913 :
    AlignedValid 12 3 missing5912_5913 records5912_5913 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5912
    maskCheck5912 AlignedValid.nil

def missing5913_5914 : List (BitVec (edgeCount 12)) :=
  [missing5913]
abbrev records5913_5914 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5913]
theorem aligned5913_5914 :
    AlignedValid 12 3 missing5913_5914 records5913_5914 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5913
    maskCheck5913 AlignedValid.nil

def missing5912_5914 : List (BitVec (edgeCount 12)) :=
  missing5912_5913 ++ missing5913_5914
abbrev records5912_5914 : List Blob :=
  records5912_5913 ++ records5913_5914
theorem aligned5912_5914 :
    AlignedValid 12 3 missing5912_5914 records5912_5914 :=
  aligned5912_5913.append aligned5913_5914

def missing5914_5915 : List (BitVec (edgeCount 12)) :=
  [missing5914]
abbrev records5914_5915 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5914]
theorem aligned5914_5915 :
    AlignedValid 12 3 missing5914_5915 records5914_5915 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5914
    maskCheck5914 AlignedValid.nil

def missing5915_5916 : List (BitVec (edgeCount 12)) :=
  [missing5915]
abbrev records5915_5916 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5915]
theorem aligned5915_5916 :
    AlignedValid 12 3 missing5915_5916 records5915_5916 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5915
    maskCheck5915 AlignedValid.nil

def missing5914_5916 : List (BitVec (edgeCount 12)) :=
  missing5914_5915 ++ missing5915_5916
abbrev records5914_5916 : List Blob :=
  records5914_5915 ++ records5915_5916
theorem aligned5914_5916 :
    AlignedValid 12 3 missing5914_5916 records5914_5916 :=
  aligned5914_5915.append aligned5915_5916

def missing5912_5916 : List (BitVec (edgeCount 12)) :=
  missing5912_5914 ++ missing5914_5916
abbrev records5912_5916 : List Blob :=
  records5912_5914 ++ records5914_5916
theorem aligned5912_5916 :
    AlignedValid 12 3 missing5912_5916 records5912_5916 :=
  aligned5912_5914.append aligned5914_5916

def missing5916_5917 : List (BitVec (edgeCount 12)) :=
  [missing5916]
abbrev records5916_5917 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5916]
theorem aligned5916_5917 :
    AlignedValid 12 3 missing5916_5917 records5916_5917 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5916
    maskCheck5916 AlignedValid.nil

def missing5917_5918 : List (BitVec (edgeCount 12)) :=
  [missing5917]
abbrev records5917_5918 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5917]
theorem aligned5917_5918 :
    AlignedValid 12 3 missing5917_5918 records5917_5918 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5917
    maskCheck5917 AlignedValid.nil

def missing5916_5918 : List (BitVec (edgeCount 12)) :=
  missing5916_5917 ++ missing5917_5918
abbrev records5916_5918 : List Blob :=
  records5916_5917 ++ records5917_5918
theorem aligned5916_5918 :
    AlignedValid 12 3 missing5916_5918 records5916_5918 :=
  aligned5916_5917.append aligned5917_5918

def missing5918_5919 : List (BitVec (edgeCount 12)) :=
  [missing5918]
abbrev records5918_5919 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5918]
theorem aligned5918_5919 :
    AlignedValid 12 3 missing5918_5919 records5918_5919 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5918
    maskCheck5918 AlignedValid.nil

def missing5919_5920 : List (BitVec (edgeCount 12)) :=
  [missing5919]
abbrev records5919_5920 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5919]
theorem aligned5919_5920 :
    AlignedValid 12 3 missing5919_5920 records5919_5920 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5919
    maskCheck5919 AlignedValid.nil

def missing5918_5920 : List (BitVec (edgeCount 12)) :=
  missing5918_5919 ++ missing5919_5920
abbrev records5918_5920 : List Blob :=
  records5918_5919 ++ records5919_5920
theorem aligned5918_5920 :
    AlignedValid 12 3 missing5918_5920 records5918_5920 :=
  aligned5918_5919.append aligned5919_5920

def missing5916_5920 : List (BitVec (edgeCount 12)) :=
  missing5916_5918 ++ missing5918_5920
abbrev records5916_5920 : List Blob :=
  records5916_5918 ++ records5918_5920
theorem aligned5916_5920 :
    AlignedValid 12 3 missing5916_5920 records5916_5920 :=
  aligned5916_5918.append aligned5918_5920

def missing5912_5920 : List (BitVec (edgeCount 12)) :=
  missing5912_5916 ++ missing5916_5920
abbrev records5912_5920 : List Blob :=
  records5912_5916 ++ records5916_5920
theorem aligned5912_5920 :
    AlignedValid 12 3 missing5912_5920 records5912_5920 :=
  aligned5912_5916.append aligned5916_5920

def missing5904_5920 : List (BitVec (edgeCount 12)) :=
  missing5904_5912 ++ missing5912_5920
abbrev records5904_5920 : List Blob :=
  records5904_5912 ++ records5912_5920
theorem aligned5904_5920 :
    AlignedValid 12 3 missing5904_5920 records5904_5920 :=
  aligned5904_5912.append aligned5912_5920

def missing5888_5920 : List (BitVec (edgeCount 12)) :=
  missing5888_5904 ++ missing5904_5920
abbrev records5888_5920 : List Blob :=
  records5888_5904 ++ records5904_5920
theorem aligned5888_5920 :
    AlignedValid 12 3 missing5888_5920 records5888_5920 :=
  aligned5888_5904.append aligned5904_5920

def missing5920_5921 : List (BitVec (edgeCount 12)) :=
  [missing5920]
abbrev records5920_5921 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5920]
theorem aligned5920_5921 :
    AlignedValid 12 3 missing5920_5921 records5920_5921 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5920
    maskCheck5920 AlignedValid.nil

def missing5921_5922 : List (BitVec (edgeCount 12)) :=
  [missing5921]
abbrev records5921_5922 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5921]
theorem aligned5921_5922 :
    AlignedValid 12 3 missing5921_5922 records5921_5922 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5921
    maskCheck5921 AlignedValid.nil

def missing5920_5922 : List (BitVec (edgeCount 12)) :=
  missing5920_5921 ++ missing5921_5922
abbrev records5920_5922 : List Blob :=
  records5920_5921 ++ records5921_5922
theorem aligned5920_5922 :
    AlignedValid 12 3 missing5920_5922 records5920_5922 :=
  aligned5920_5921.append aligned5921_5922

def missing5922_5923 : List (BitVec (edgeCount 12)) :=
  [missing5922]
abbrev records5922_5923 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5922]
theorem aligned5922_5923 :
    AlignedValid 12 3 missing5922_5923 records5922_5923 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5922
    maskCheck5922 AlignedValid.nil

def missing5923_5924 : List (BitVec (edgeCount 12)) :=
  [missing5923]
abbrev records5923_5924 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5923]
theorem aligned5923_5924 :
    AlignedValid 12 3 missing5923_5924 records5923_5924 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5923
    maskCheck5923 AlignedValid.nil

def missing5922_5924 : List (BitVec (edgeCount 12)) :=
  missing5922_5923 ++ missing5923_5924
abbrev records5922_5924 : List Blob :=
  records5922_5923 ++ records5923_5924
theorem aligned5922_5924 :
    AlignedValid 12 3 missing5922_5924 records5922_5924 :=
  aligned5922_5923.append aligned5923_5924

def missing5920_5924 : List (BitVec (edgeCount 12)) :=
  missing5920_5922 ++ missing5922_5924
abbrev records5920_5924 : List Blob :=
  records5920_5922 ++ records5922_5924
theorem aligned5920_5924 :
    AlignedValid 12 3 missing5920_5924 records5920_5924 :=
  aligned5920_5922.append aligned5922_5924

def missing5924_5925 : List (BitVec (edgeCount 12)) :=
  [missing5924]
abbrev records5924_5925 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5924]
theorem aligned5924_5925 :
    AlignedValid 12 3 missing5924_5925 records5924_5925 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5924
    maskCheck5924 AlignedValid.nil

def missing5925_5926 : List (BitVec (edgeCount 12)) :=
  [missing5925]
abbrev records5925_5926 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5925]
theorem aligned5925_5926 :
    AlignedValid 12 3 missing5925_5926 records5925_5926 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5925
    maskCheck5925 AlignedValid.nil

def missing5924_5926 : List (BitVec (edgeCount 12)) :=
  missing5924_5925 ++ missing5925_5926
abbrev records5924_5926 : List Blob :=
  records5924_5925 ++ records5925_5926
theorem aligned5924_5926 :
    AlignedValid 12 3 missing5924_5926 records5924_5926 :=
  aligned5924_5925.append aligned5925_5926

def missing5926_5927 : List (BitVec (edgeCount 12)) :=
  [missing5926]
abbrev records5926_5927 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5926]
theorem aligned5926_5927 :
    AlignedValid 12 3 missing5926_5927 records5926_5927 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5926
    maskCheck5926 AlignedValid.nil

def missing5927_5928 : List (BitVec (edgeCount 12)) :=
  [missing5927]
abbrev records5927_5928 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5927]
theorem aligned5927_5928 :
    AlignedValid 12 3 missing5927_5928 records5927_5928 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5927
    maskCheck5927 AlignedValid.nil

def missing5926_5928 : List (BitVec (edgeCount 12)) :=
  missing5926_5927 ++ missing5927_5928
abbrev records5926_5928 : List Blob :=
  records5926_5927 ++ records5927_5928
theorem aligned5926_5928 :
    AlignedValid 12 3 missing5926_5928 records5926_5928 :=
  aligned5926_5927.append aligned5927_5928

def missing5924_5928 : List (BitVec (edgeCount 12)) :=
  missing5924_5926 ++ missing5926_5928
abbrev records5924_5928 : List Blob :=
  records5924_5926 ++ records5926_5928
theorem aligned5924_5928 :
    AlignedValid 12 3 missing5924_5928 records5924_5928 :=
  aligned5924_5926.append aligned5926_5928

def missing5920_5928 : List (BitVec (edgeCount 12)) :=
  missing5920_5924 ++ missing5924_5928
abbrev records5920_5928 : List Blob :=
  records5920_5924 ++ records5924_5928
theorem aligned5920_5928 :
    AlignedValid 12 3 missing5920_5928 records5920_5928 :=
  aligned5920_5924.append aligned5924_5928

def missing5928_5929 : List (BitVec (edgeCount 12)) :=
  [missing5928]
abbrev records5928_5929 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5928]
theorem aligned5928_5929 :
    AlignedValid 12 3 missing5928_5929 records5928_5929 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5928
    maskCheck5928 AlignedValid.nil

def missing5929_5930 : List (BitVec (edgeCount 12)) :=
  [missing5929]
abbrev records5929_5930 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5929]
theorem aligned5929_5930 :
    AlignedValid 12 3 missing5929_5930 records5929_5930 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5929
    maskCheck5929 AlignedValid.nil

def missing5928_5930 : List (BitVec (edgeCount 12)) :=
  missing5928_5929 ++ missing5929_5930
abbrev records5928_5930 : List Blob :=
  records5928_5929 ++ records5929_5930
theorem aligned5928_5930 :
    AlignedValid 12 3 missing5928_5930 records5928_5930 :=
  aligned5928_5929.append aligned5929_5930

def missing5930_5931 : List (BitVec (edgeCount 12)) :=
  [missing5930]
abbrev records5930_5931 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5930]
theorem aligned5930_5931 :
    AlignedValid 12 3 missing5930_5931 records5930_5931 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5930
    maskCheck5930 AlignedValid.nil

def missing5931_5932 : List (BitVec (edgeCount 12)) :=
  [missing5931]
abbrev records5931_5932 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5931]
theorem aligned5931_5932 :
    AlignedValid 12 3 missing5931_5932 records5931_5932 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5931
    maskCheck5931 AlignedValid.nil

def missing5930_5932 : List (BitVec (edgeCount 12)) :=
  missing5930_5931 ++ missing5931_5932
abbrev records5930_5932 : List Blob :=
  records5930_5931 ++ records5931_5932
theorem aligned5930_5932 :
    AlignedValid 12 3 missing5930_5932 records5930_5932 :=
  aligned5930_5931.append aligned5931_5932

def missing5928_5932 : List (BitVec (edgeCount 12)) :=
  missing5928_5930 ++ missing5930_5932
abbrev records5928_5932 : List Blob :=
  records5928_5930 ++ records5930_5932
theorem aligned5928_5932 :
    AlignedValid 12 3 missing5928_5932 records5928_5932 :=
  aligned5928_5930.append aligned5930_5932

def missing5932_5933 : List (BitVec (edgeCount 12)) :=
  [missing5932]
abbrev records5932_5933 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5932]
theorem aligned5932_5933 :
    AlignedValid 12 3 missing5932_5933 records5932_5933 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5932
    maskCheck5932 AlignedValid.nil

def missing5933_5934 : List (BitVec (edgeCount 12)) :=
  [missing5933]
abbrev records5933_5934 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5933]
theorem aligned5933_5934 :
    AlignedValid 12 3 missing5933_5934 records5933_5934 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5933
    maskCheck5933 AlignedValid.nil

def missing5932_5934 : List (BitVec (edgeCount 12)) :=
  missing5932_5933 ++ missing5933_5934
abbrev records5932_5934 : List Blob :=
  records5932_5933 ++ records5933_5934
theorem aligned5932_5934 :
    AlignedValid 12 3 missing5932_5934 records5932_5934 :=
  aligned5932_5933.append aligned5933_5934

def missing5934_5935 : List (BitVec (edgeCount 12)) :=
  [missing5934]
abbrev records5934_5935 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5934]
theorem aligned5934_5935 :
    AlignedValid 12 3 missing5934_5935 records5934_5935 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5934
    maskCheck5934 AlignedValid.nil

def missing5935_5936 : List (BitVec (edgeCount 12)) :=
  [missing5935]
abbrev records5935_5936 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5935]
theorem aligned5935_5936 :
    AlignedValid 12 3 missing5935_5936 records5935_5936 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5935
    maskCheck5935 AlignedValid.nil

def missing5934_5936 : List (BitVec (edgeCount 12)) :=
  missing5934_5935 ++ missing5935_5936
abbrev records5934_5936 : List Blob :=
  records5934_5935 ++ records5935_5936
theorem aligned5934_5936 :
    AlignedValid 12 3 missing5934_5936 records5934_5936 :=
  aligned5934_5935.append aligned5935_5936

def missing5932_5936 : List (BitVec (edgeCount 12)) :=
  missing5932_5934 ++ missing5934_5936
abbrev records5932_5936 : List Blob :=
  records5932_5934 ++ records5934_5936
theorem aligned5932_5936 :
    AlignedValid 12 3 missing5932_5936 records5932_5936 :=
  aligned5932_5934.append aligned5934_5936

def missing5928_5936 : List (BitVec (edgeCount 12)) :=
  missing5928_5932 ++ missing5932_5936
abbrev records5928_5936 : List Blob :=
  records5928_5932 ++ records5932_5936
theorem aligned5928_5936 :
    AlignedValid 12 3 missing5928_5936 records5928_5936 :=
  aligned5928_5932.append aligned5932_5936

def missing5920_5936 : List (BitVec (edgeCount 12)) :=
  missing5920_5928 ++ missing5928_5936
abbrev records5920_5936 : List Blob :=
  records5920_5928 ++ records5928_5936
theorem aligned5920_5936 :
    AlignedValid 12 3 missing5920_5936 records5920_5936 :=
  aligned5920_5928.append aligned5928_5936

def missing5936_5937 : List (BitVec (edgeCount 12)) :=
  [missing5936]
abbrev records5936_5937 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5936]
theorem aligned5936_5937 :
    AlignedValid 12 3 missing5936_5937 records5936_5937 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5936
    maskCheck5936 AlignedValid.nil

def missing5937_5938 : List (BitVec (edgeCount 12)) :=
  [missing5937]
abbrev records5937_5938 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5937]
theorem aligned5937_5938 :
    AlignedValid 12 3 missing5937_5938 records5937_5938 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5937
    maskCheck5937 AlignedValid.nil

def missing5936_5938 : List (BitVec (edgeCount 12)) :=
  missing5936_5937 ++ missing5937_5938
abbrev records5936_5938 : List Blob :=
  records5936_5937 ++ records5937_5938
theorem aligned5936_5938 :
    AlignedValid 12 3 missing5936_5938 records5936_5938 :=
  aligned5936_5937.append aligned5937_5938

def missing5938_5939 : List (BitVec (edgeCount 12)) :=
  [missing5938]
abbrev records5938_5939 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5938]
theorem aligned5938_5939 :
    AlignedValid 12 3 missing5938_5939 records5938_5939 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5938
    maskCheck5938 AlignedValid.nil

def missing5939_5940 : List (BitVec (edgeCount 12)) :=
  [missing5939]
abbrev records5939_5940 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5939]
theorem aligned5939_5940 :
    AlignedValid 12 3 missing5939_5940 records5939_5940 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5939
    maskCheck5939 AlignedValid.nil

def missing5938_5940 : List (BitVec (edgeCount 12)) :=
  missing5938_5939 ++ missing5939_5940
abbrev records5938_5940 : List Blob :=
  records5938_5939 ++ records5939_5940
theorem aligned5938_5940 :
    AlignedValid 12 3 missing5938_5940 records5938_5940 :=
  aligned5938_5939.append aligned5939_5940

def missing5936_5940 : List (BitVec (edgeCount 12)) :=
  missing5936_5938 ++ missing5938_5940
abbrev records5936_5940 : List Blob :=
  records5936_5938 ++ records5938_5940
theorem aligned5936_5940 :
    AlignedValid 12 3 missing5936_5940 records5936_5940 :=
  aligned5936_5938.append aligned5938_5940

def missing5940_5941 : List (BitVec (edgeCount 12)) :=
  [missing5940]
abbrev records5940_5941 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5940]
theorem aligned5940_5941 :
    AlignedValid 12 3 missing5940_5941 records5940_5941 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5940
    maskCheck5940 AlignedValid.nil

def missing5941_5942 : List (BitVec (edgeCount 12)) :=
  [missing5941]
abbrev records5941_5942 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5941]
theorem aligned5941_5942 :
    AlignedValid 12 3 missing5941_5942 records5941_5942 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5941
    maskCheck5941 AlignedValid.nil

def missing5940_5942 : List (BitVec (edgeCount 12)) :=
  missing5940_5941 ++ missing5941_5942
abbrev records5940_5942 : List Blob :=
  records5940_5941 ++ records5941_5942
theorem aligned5940_5942 :
    AlignedValid 12 3 missing5940_5942 records5940_5942 :=
  aligned5940_5941.append aligned5941_5942

def missing5942_5943 : List (BitVec (edgeCount 12)) :=
  [missing5942]
abbrev records5942_5943 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5942]
theorem aligned5942_5943 :
    AlignedValid 12 3 missing5942_5943 records5942_5943 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5942
    maskCheck5942 AlignedValid.nil

def missing5943_5944 : List (BitVec (edgeCount 12)) :=
  [missing5943]
abbrev records5943_5944 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5943]
theorem aligned5943_5944 :
    AlignedValid 12 3 missing5943_5944 records5943_5944 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5943
    maskCheck5943 AlignedValid.nil

def missing5942_5944 : List (BitVec (edgeCount 12)) :=
  missing5942_5943 ++ missing5943_5944
abbrev records5942_5944 : List Blob :=
  records5942_5943 ++ records5943_5944
theorem aligned5942_5944 :
    AlignedValid 12 3 missing5942_5944 records5942_5944 :=
  aligned5942_5943.append aligned5943_5944

def missing5940_5944 : List (BitVec (edgeCount 12)) :=
  missing5940_5942 ++ missing5942_5944
abbrev records5940_5944 : List Blob :=
  records5940_5942 ++ records5942_5944
theorem aligned5940_5944 :
    AlignedValid 12 3 missing5940_5944 records5940_5944 :=
  aligned5940_5942.append aligned5942_5944

def missing5936_5944 : List (BitVec (edgeCount 12)) :=
  missing5936_5940 ++ missing5940_5944
abbrev records5936_5944 : List Blob :=
  records5936_5940 ++ records5940_5944
theorem aligned5936_5944 :
    AlignedValid 12 3 missing5936_5944 records5936_5944 :=
  aligned5936_5940.append aligned5940_5944

def missing5944_5945 : List (BitVec (edgeCount 12)) :=
  [missing5944]
abbrev records5944_5945 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5944]
theorem aligned5944_5945 :
    AlignedValid 12 3 missing5944_5945 records5944_5945 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5944
    maskCheck5944 AlignedValid.nil

def missing5945_5946 : List (BitVec (edgeCount 12)) :=
  [missing5945]
abbrev records5945_5946 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5945]
theorem aligned5945_5946 :
    AlignedValid 12 3 missing5945_5946 records5945_5946 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5945
    maskCheck5945 AlignedValid.nil

def missing5944_5946 : List (BitVec (edgeCount 12)) :=
  missing5944_5945 ++ missing5945_5946
abbrev records5944_5946 : List Blob :=
  records5944_5945 ++ records5945_5946
theorem aligned5944_5946 :
    AlignedValid 12 3 missing5944_5946 records5944_5946 :=
  aligned5944_5945.append aligned5945_5946

def missing5946_5947 : List (BitVec (edgeCount 12)) :=
  [missing5946]
abbrev records5946_5947 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5946]
theorem aligned5946_5947 :
    AlignedValid 12 3 missing5946_5947 records5946_5947 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5946
    maskCheck5946 AlignedValid.nil

def missing5947_5948 : List (BitVec (edgeCount 12)) :=
  [missing5947]
abbrev records5947_5948 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5947]
theorem aligned5947_5948 :
    AlignedValid 12 3 missing5947_5948 records5947_5948 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5947
    maskCheck5947 AlignedValid.nil

def missing5946_5948 : List (BitVec (edgeCount 12)) :=
  missing5946_5947 ++ missing5947_5948
abbrev records5946_5948 : List Blob :=
  records5946_5947 ++ records5947_5948
theorem aligned5946_5948 :
    AlignedValid 12 3 missing5946_5948 records5946_5948 :=
  aligned5946_5947.append aligned5947_5948

def missing5944_5948 : List (BitVec (edgeCount 12)) :=
  missing5944_5946 ++ missing5946_5948
abbrev records5944_5948 : List Blob :=
  records5944_5946 ++ records5946_5948
theorem aligned5944_5948 :
    AlignedValid 12 3 missing5944_5948 records5944_5948 :=
  aligned5944_5946.append aligned5946_5948

def missing5948_5949 : List (BitVec (edgeCount 12)) :=
  [missing5948]
abbrev records5948_5949 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5948]
theorem aligned5948_5949 :
    AlignedValid 12 3 missing5948_5949 records5948_5949 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5948
    maskCheck5948 AlignedValid.nil

def missing5949_5950 : List (BitVec (edgeCount 12)) :=
  [missing5949]
abbrev records5949_5950 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5949]
theorem aligned5949_5950 :
    AlignedValid 12 3 missing5949_5950 records5949_5950 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5949
    maskCheck5949 AlignedValid.nil

def missing5948_5950 : List (BitVec (edgeCount 12)) :=
  missing5948_5949 ++ missing5949_5950
abbrev records5948_5950 : List Blob :=
  records5948_5949 ++ records5949_5950
theorem aligned5948_5950 :
    AlignedValid 12 3 missing5948_5950 records5948_5950 :=
  aligned5948_5949.append aligned5949_5950

def missing5950_5951 : List (BitVec (edgeCount 12)) :=
  [missing5950]
abbrev records5950_5951 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5950]
theorem aligned5950_5951 :
    AlignedValid 12 3 missing5950_5951 records5950_5951 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5950
    maskCheck5950 AlignedValid.nil

def missing5951_5952 : List (BitVec (edgeCount 12)) :=
  [missing5951]
abbrev records5951_5952 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5951]
theorem aligned5951_5952 :
    AlignedValid 12 3 missing5951_5952 records5951_5952 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5951
    maskCheck5951 AlignedValid.nil

def missing5950_5952 : List (BitVec (edgeCount 12)) :=
  missing5950_5951 ++ missing5951_5952
abbrev records5950_5952 : List Blob :=
  records5950_5951 ++ records5951_5952
theorem aligned5950_5952 :
    AlignedValid 12 3 missing5950_5952 records5950_5952 :=
  aligned5950_5951.append aligned5951_5952

def missing5948_5952 : List (BitVec (edgeCount 12)) :=
  missing5948_5950 ++ missing5950_5952
abbrev records5948_5952 : List Blob :=
  records5948_5950 ++ records5950_5952
theorem aligned5948_5952 :
    AlignedValid 12 3 missing5948_5952 records5948_5952 :=
  aligned5948_5950.append aligned5950_5952

def missing5944_5952 : List (BitVec (edgeCount 12)) :=
  missing5944_5948 ++ missing5948_5952
abbrev records5944_5952 : List Blob :=
  records5944_5948 ++ records5948_5952
theorem aligned5944_5952 :
    AlignedValid 12 3 missing5944_5952 records5944_5952 :=
  aligned5944_5948.append aligned5948_5952

def missing5936_5952 : List (BitVec (edgeCount 12)) :=
  missing5936_5944 ++ missing5944_5952
abbrev records5936_5952 : List Blob :=
  records5936_5944 ++ records5944_5952
theorem aligned5936_5952 :
    AlignedValid 12 3 missing5936_5952 records5936_5952 :=
  aligned5936_5944.append aligned5944_5952

def missing5920_5952 : List (BitVec (edgeCount 12)) :=
  missing5920_5936 ++ missing5936_5952
abbrev records5920_5952 : List Blob :=
  records5920_5936 ++ records5936_5952
theorem aligned5920_5952 :
    AlignedValid 12 3 missing5920_5952 records5920_5952 :=
  aligned5920_5936.append aligned5936_5952

def missing5888_5952 : List (BitVec (edgeCount 12)) :=
  missing5888_5920 ++ missing5920_5952
abbrev records5888_5952 : List Blob :=
  records5888_5920 ++ records5920_5952
theorem aligned5888_5952 :
    AlignedValid 12 3 missing5888_5952 records5888_5952 :=
  aligned5888_5920.append aligned5920_5952

def missing5952_5953 : List (BitVec (edgeCount 12)) :=
  [missing5952]
abbrev records5952_5953 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5952]
theorem aligned5952_5953 :
    AlignedValid 12 3 missing5952_5953 records5952_5953 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5952
    maskCheck5952 AlignedValid.nil

def missing5953_5954 : List (BitVec (edgeCount 12)) :=
  [missing5953]
abbrev records5953_5954 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5953]
theorem aligned5953_5954 :
    AlignedValid 12 3 missing5953_5954 records5953_5954 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5953
    maskCheck5953 AlignedValid.nil

def missing5952_5954 : List (BitVec (edgeCount 12)) :=
  missing5952_5953 ++ missing5953_5954
abbrev records5952_5954 : List Blob :=
  records5952_5953 ++ records5953_5954
theorem aligned5952_5954 :
    AlignedValid 12 3 missing5952_5954 records5952_5954 :=
  aligned5952_5953.append aligned5953_5954

def missing5954_5955 : List (BitVec (edgeCount 12)) :=
  [missing5954]
abbrev records5954_5955 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5954]
theorem aligned5954_5955 :
    AlignedValid 12 3 missing5954_5955 records5954_5955 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5954
    maskCheck5954 AlignedValid.nil

def missing5955_5956 : List (BitVec (edgeCount 12)) :=
  [missing5955]
abbrev records5955_5956 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5955]
theorem aligned5955_5956 :
    AlignedValid 12 3 missing5955_5956 records5955_5956 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5955
    maskCheck5955 AlignedValid.nil

def missing5954_5956 : List (BitVec (edgeCount 12)) :=
  missing5954_5955 ++ missing5955_5956
abbrev records5954_5956 : List Blob :=
  records5954_5955 ++ records5955_5956
theorem aligned5954_5956 :
    AlignedValid 12 3 missing5954_5956 records5954_5956 :=
  aligned5954_5955.append aligned5955_5956

def missing5952_5956 : List (BitVec (edgeCount 12)) :=
  missing5952_5954 ++ missing5954_5956
abbrev records5952_5956 : List Blob :=
  records5952_5954 ++ records5954_5956
theorem aligned5952_5956 :
    AlignedValid 12 3 missing5952_5956 records5952_5956 :=
  aligned5952_5954.append aligned5954_5956

def missing5956_5957 : List (BitVec (edgeCount 12)) :=
  [missing5956]
abbrev records5956_5957 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5956]
theorem aligned5956_5957 :
    AlignedValid 12 3 missing5956_5957 records5956_5957 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5956
    maskCheck5956 AlignedValid.nil

def missing5957_5958 : List (BitVec (edgeCount 12)) :=
  [missing5957]
abbrev records5957_5958 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5957]
theorem aligned5957_5958 :
    AlignedValid 12 3 missing5957_5958 records5957_5958 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5957
    maskCheck5957 AlignedValid.nil

def missing5956_5958 : List (BitVec (edgeCount 12)) :=
  missing5956_5957 ++ missing5957_5958
abbrev records5956_5958 : List Blob :=
  records5956_5957 ++ records5957_5958
theorem aligned5956_5958 :
    AlignedValid 12 3 missing5956_5958 records5956_5958 :=
  aligned5956_5957.append aligned5957_5958

def missing5958_5959 : List (BitVec (edgeCount 12)) :=
  [missing5958]
abbrev records5958_5959 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5958]
theorem aligned5958_5959 :
    AlignedValid 12 3 missing5958_5959 records5958_5959 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5958
    maskCheck5958 AlignedValid.nil

def missing5959_5960 : List (BitVec (edgeCount 12)) :=
  [missing5959]
abbrev records5959_5960 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5959]
theorem aligned5959_5960 :
    AlignedValid 12 3 missing5959_5960 records5959_5960 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5959
    maskCheck5959 AlignedValid.nil

def missing5958_5960 : List (BitVec (edgeCount 12)) :=
  missing5958_5959 ++ missing5959_5960
abbrev records5958_5960 : List Blob :=
  records5958_5959 ++ records5959_5960
theorem aligned5958_5960 :
    AlignedValid 12 3 missing5958_5960 records5958_5960 :=
  aligned5958_5959.append aligned5959_5960

def missing5956_5960 : List (BitVec (edgeCount 12)) :=
  missing5956_5958 ++ missing5958_5960
abbrev records5956_5960 : List Blob :=
  records5956_5958 ++ records5958_5960
theorem aligned5956_5960 :
    AlignedValid 12 3 missing5956_5960 records5956_5960 :=
  aligned5956_5958.append aligned5958_5960

def missing5952_5960 : List (BitVec (edgeCount 12)) :=
  missing5952_5956 ++ missing5956_5960
abbrev records5952_5960 : List Blob :=
  records5952_5956 ++ records5956_5960
theorem aligned5952_5960 :
    AlignedValid 12 3 missing5952_5960 records5952_5960 :=
  aligned5952_5956.append aligned5956_5960

def missing5960_5961 : List (BitVec (edgeCount 12)) :=
  [missing5960]
abbrev records5960_5961 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5960]
theorem aligned5960_5961 :
    AlignedValid 12 3 missing5960_5961 records5960_5961 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5960
    maskCheck5960 AlignedValid.nil

def missing5961_5962 : List (BitVec (edgeCount 12)) :=
  [missing5961]
abbrev records5961_5962 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5961]
theorem aligned5961_5962 :
    AlignedValid 12 3 missing5961_5962 records5961_5962 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5961
    maskCheck5961 AlignedValid.nil

def missing5960_5962 : List (BitVec (edgeCount 12)) :=
  missing5960_5961 ++ missing5961_5962
abbrev records5960_5962 : List Blob :=
  records5960_5961 ++ records5961_5962
theorem aligned5960_5962 :
    AlignedValid 12 3 missing5960_5962 records5960_5962 :=
  aligned5960_5961.append aligned5961_5962

def missing5962_5963 : List (BitVec (edgeCount 12)) :=
  [missing5962]
abbrev records5962_5963 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5962]
theorem aligned5962_5963 :
    AlignedValid 12 3 missing5962_5963 records5962_5963 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5962
    maskCheck5962 AlignedValid.nil

def missing5963_5964 : List (BitVec (edgeCount 12)) :=
  [missing5963]
abbrev records5963_5964 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5963]
theorem aligned5963_5964 :
    AlignedValid 12 3 missing5963_5964 records5963_5964 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5963
    maskCheck5963 AlignedValid.nil

def missing5962_5964 : List (BitVec (edgeCount 12)) :=
  missing5962_5963 ++ missing5963_5964
abbrev records5962_5964 : List Blob :=
  records5962_5963 ++ records5963_5964
theorem aligned5962_5964 :
    AlignedValid 12 3 missing5962_5964 records5962_5964 :=
  aligned5962_5963.append aligned5963_5964

def missing5960_5964 : List (BitVec (edgeCount 12)) :=
  missing5960_5962 ++ missing5962_5964
abbrev records5960_5964 : List Blob :=
  records5960_5962 ++ records5962_5964
theorem aligned5960_5964 :
    AlignedValid 12 3 missing5960_5964 records5960_5964 :=
  aligned5960_5962.append aligned5962_5964

def missing5964_5965 : List (BitVec (edgeCount 12)) :=
  [missing5964]
abbrev records5964_5965 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5964]
theorem aligned5964_5965 :
    AlignedValid 12 3 missing5964_5965 records5964_5965 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5964
    maskCheck5964 AlignedValid.nil

def missing5965_5966 : List (BitVec (edgeCount 12)) :=
  [missing5965]
abbrev records5965_5966 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5965]
theorem aligned5965_5966 :
    AlignedValid 12 3 missing5965_5966 records5965_5966 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5965
    maskCheck5965 AlignedValid.nil

def missing5964_5966 : List (BitVec (edgeCount 12)) :=
  missing5964_5965 ++ missing5965_5966
abbrev records5964_5966 : List Blob :=
  records5964_5965 ++ records5965_5966
theorem aligned5964_5966 :
    AlignedValid 12 3 missing5964_5966 records5964_5966 :=
  aligned5964_5965.append aligned5965_5966

def missing5966_5967 : List (BitVec (edgeCount 12)) :=
  [missing5966]
abbrev records5966_5967 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5966]
theorem aligned5966_5967 :
    AlignedValid 12 3 missing5966_5967 records5966_5967 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5966
    maskCheck5966 AlignedValid.nil

def missing5967_5968 : List (BitVec (edgeCount 12)) :=
  [missing5967]
abbrev records5967_5968 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5967]
theorem aligned5967_5968 :
    AlignedValid 12 3 missing5967_5968 records5967_5968 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5967
    maskCheck5967 AlignedValid.nil

def missing5966_5968 : List (BitVec (edgeCount 12)) :=
  missing5966_5967 ++ missing5967_5968
abbrev records5966_5968 : List Blob :=
  records5966_5967 ++ records5967_5968
theorem aligned5966_5968 :
    AlignedValid 12 3 missing5966_5968 records5966_5968 :=
  aligned5966_5967.append aligned5967_5968

def missing5964_5968 : List (BitVec (edgeCount 12)) :=
  missing5964_5966 ++ missing5966_5968
abbrev records5964_5968 : List Blob :=
  records5964_5966 ++ records5966_5968
theorem aligned5964_5968 :
    AlignedValid 12 3 missing5964_5968 records5964_5968 :=
  aligned5964_5966.append aligned5966_5968

def missing5960_5968 : List (BitVec (edgeCount 12)) :=
  missing5960_5964 ++ missing5964_5968
abbrev records5960_5968 : List Blob :=
  records5960_5964 ++ records5964_5968
theorem aligned5960_5968 :
    AlignedValid 12 3 missing5960_5968 records5960_5968 :=
  aligned5960_5964.append aligned5964_5968

def missing5952_5968 : List (BitVec (edgeCount 12)) :=
  missing5952_5960 ++ missing5960_5968
abbrev records5952_5968 : List Blob :=
  records5952_5960 ++ records5960_5968
theorem aligned5952_5968 :
    AlignedValid 12 3 missing5952_5968 records5952_5968 :=
  aligned5952_5960.append aligned5960_5968

def missing5968_5969 : List (BitVec (edgeCount 12)) :=
  [missing5968]
abbrev records5968_5969 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5968]
theorem aligned5968_5969 :
    AlignedValid 12 3 missing5968_5969 records5968_5969 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5968
    maskCheck5968 AlignedValid.nil

def missing5969_5970 : List (BitVec (edgeCount 12)) :=
  [missing5969]
abbrev records5969_5970 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5969]
theorem aligned5969_5970 :
    AlignedValid 12 3 missing5969_5970 records5969_5970 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5969
    maskCheck5969 AlignedValid.nil

def missing5968_5970 : List (BitVec (edgeCount 12)) :=
  missing5968_5969 ++ missing5969_5970
abbrev records5968_5970 : List Blob :=
  records5968_5969 ++ records5969_5970
theorem aligned5968_5970 :
    AlignedValid 12 3 missing5968_5970 records5968_5970 :=
  aligned5968_5969.append aligned5969_5970

def missing5970_5971 : List (BitVec (edgeCount 12)) :=
  [missing5970]
abbrev records5970_5971 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5970]
theorem aligned5970_5971 :
    AlignedValid 12 3 missing5970_5971 records5970_5971 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5970
    maskCheck5970 AlignedValid.nil

def missing5971_5972 : List (BitVec (edgeCount 12)) :=
  [missing5971]
abbrev records5971_5972 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5971]
theorem aligned5971_5972 :
    AlignedValid 12 3 missing5971_5972 records5971_5972 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5971
    maskCheck5971 AlignedValid.nil

def missing5970_5972 : List (BitVec (edgeCount 12)) :=
  missing5970_5971 ++ missing5971_5972
abbrev records5970_5972 : List Blob :=
  records5970_5971 ++ records5971_5972
theorem aligned5970_5972 :
    AlignedValid 12 3 missing5970_5972 records5970_5972 :=
  aligned5970_5971.append aligned5971_5972

def missing5968_5972 : List (BitVec (edgeCount 12)) :=
  missing5968_5970 ++ missing5970_5972
abbrev records5968_5972 : List Blob :=
  records5968_5970 ++ records5970_5972
theorem aligned5968_5972 :
    AlignedValid 12 3 missing5968_5972 records5968_5972 :=
  aligned5968_5970.append aligned5970_5972

def missing5972_5973 : List (BitVec (edgeCount 12)) :=
  [missing5972]
abbrev records5972_5973 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5972]
theorem aligned5972_5973 :
    AlignedValid 12 3 missing5972_5973 records5972_5973 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5972
    maskCheck5972 AlignedValid.nil

def missing5973_5974 : List (BitVec (edgeCount 12)) :=
  [missing5973]
abbrev records5973_5974 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5973]
theorem aligned5973_5974 :
    AlignedValid 12 3 missing5973_5974 records5973_5974 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5973
    maskCheck5973 AlignedValid.nil

def missing5972_5974 : List (BitVec (edgeCount 12)) :=
  missing5972_5973 ++ missing5973_5974
abbrev records5972_5974 : List Blob :=
  records5972_5973 ++ records5973_5974
theorem aligned5972_5974 :
    AlignedValid 12 3 missing5972_5974 records5972_5974 :=
  aligned5972_5973.append aligned5973_5974

def missing5974_5975 : List (BitVec (edgeCount 12)) :=
  [missing5974]
abbrev records5974_5975 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5974]
theorem aligned5974_5975 :
    AlignedValid 12 3 missing5974_5975 records5974_5975 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5974
    maskCheck5974 AlignedValid.nil

def missing5975_5976 : List (BitVec (edgeCount 12)) :=
  [missing5975]
abbrev records5975_5976 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5975]
theorem aligned5975_5976 :
    AlignedValid 12 3 missing5975_5976 records5975_5976 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5975
    maskCheck5975 AlignedValid.nil

def missing5974_5976 : List (BitVec (edgeCount 12)) :=
  missing5974_5975 ++ missing5975_5976
abbrev records5974_5976 : List Blob :=
  records5974_5975 ++ records5975_5976
theorem aligned5974_5976 :
    AlignedValid 12 3 missing5974_5976 records5974_5976 :=
  aligned5974_5975.append aligned5975_5976

def missing5972_5976 : List (BitVec (edgeCount 12)) :=
  missing5972_5974 ++ missing5974_5976
abbrev records5972_5976 : List Blob :=
  records5972_5974 ++ records5974_5976
theorem aligned5972_5976 :
    AlignedValid 12 3 missing5972_5976 records5972_5976 :=
  aligned5972_5974.append aligned5974_5976

def missing5968_5976 : List (BitVec (edgeCount 12)) :=
  missing5968_5972 ++ missing5972_5976
abbrev records5968_5976 : List Blob :=
  records5968_5972 ++ records5972_5976
theorem aligned5968_5976 :
    AlignedValid 12 3 missing5968_5976 records5968_5976 :=
  aligned5968_5972.append aligned5972_5976

def missing5976_5977 : List (BitVec (edgeCount 12)) :=
  [missing5976]
abbrev records5976_5977 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5976]
theorem aligned5976_5977 :
    AlignedValid 12 3 missing5976_5977 records5976_5977 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5976
    maskCheck5976 AlignedValid.nil

def missing5977_5978 : List (BitVec (edgeCount 12)) :=
  [missing5977]
abbrev records5977_5978 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5977]
theorem aligned5977_5978 :
    AlignedValid 12 3 missing5977_5978 records5977_5978 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5977
    maskCheck5977 AlignedValid.nil

def missing5976_5978 : List (BitVec (edgeCount 12)) :=
  missing5976_5977 ++ missing5977_5978
abbrev records5976_5978 : List Blob :=
  records5976_5977 ++ records5977_5978
theorem aligned5976_5978 :
    AlignedValid 12 3 missing5976_5978 records5976_5978 :=
  aligned5976_5977.append aligned5977_5978

def missing5978_5979 : List (BitVec (edgeCount 12)) :=
  [missing5978]
abbrev records5978_5979 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5978]
theorem aligned5978_5979 :
    AlignedValid 12 3 missing5978_5979 records5978_5979 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5978
    maskCheck5978 AlignedValid.nil

def missing5979_5980 : List (BitVec (edgeCount 12)) :=
  [missing5979]
abbrev records5979_5980 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5979]
theorem aligned5979_5980 :
    AlignedValid 12 3 missing5979_5980 records5979_5980 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5979
    maskCheck5979 AlignedValid.nil

def missing5978_5980 : List (BitVec (edgeCount 12)) :=
  missing5978_5979 ++ missing5979_5980
abbrev records5978_5980 : List Blob :=
  records5978_5979 ++ records5979_5980
theorem aligned5978_5980 :
    AlignedValid 12 3 missing5978_5980 records5978_5980 :=
  aligned5978_5979.append aligned5979_5980

def missing5976_5980 : List (BitVec (edgeCount 12)) :=
  missing5976_5978 ++ missing5978_5980
abbrev records5976_5980 : List Blob :=
  records5976_5978 ++ records5978_5980
theorem aligned5976_5980 :
    AlignedValid 12 3 missing5976_5980 records5976_5980 :=
  aligned5976_5978.append aligned5978_5980

def missing5980_5981 : List (BitVec (edgeCount 12)) :=
  [missing5980]
abbrev records5980_5981 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5980]
theorem aligned5980_5981 :
    AlignedValid 12 3 missing5980_5981 records5980_5981 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5980
    maskCheck5980 AlignedValid.nil

def missing5981_5982 : List (BitVec (edgeCount 12)) :=
  [missing5981]
abbrev records5981_5982 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5981]
theorem aligned5981_5982 :
    AlignedValid 12 3 missing5981_5982 records5981_5982 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5981
    maskCheck5981 AlignedValid.nil

def missing5980_5982 : List (BitVec (edgeCount 12)) :=
  missing5980_5981 ++ missing5981_5982
abbrev records5980_5982 : List Blob :=
  records5980_5981 ++ records5981_5982
theorem aligned5980_5982 :
    AlignedValid 12 3 missing5980_5982 records5980_5982 :=
  aligned5980_5981.append aligned5981_5982

def missing5982_5983 : List (BitVec (edgeCount 12)) :=
  [missing5982]
abbrev records5982_5983 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5982]
theorem aligned5982_5983 :
    AlignedValid 12 3 missing5982_5983 records5982_5983 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5982
    maskCheck5982 AlignedValid.nil

def missing5983_5984 : List (BitVec (edgeCount 12)) :=
  [missing5983]
abbrev records5983_5984 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5983]
theorem aligned5983_5984 :
    AlignedValid 12 3 missing5983_5984 records5983_5984 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5983
    maskCheck5983 AlignedValid.nil

def missing5982_5984 : List (BitVec (edgeCount 12)) :=
  missing5982_5983 ++ missing5983_5984
abbrev records5982_5984 : List Blob :=
  records5982_5983 ++ records5983_5984
theorem aligned5982_5984 :
    AlignedValid 12 3 missing5982_5984 records5982_5984 :=
  aligned5982_5983.append aligned5983_5984

def missing5980_5984 : List (BitVec (edgeCount 12)) :=
  missing5980_5982 ++ missing5982_5984
abbrev records5980_5984 : List Blob :=
  records5980_5982 ++ records5982_5984
theorem aligned5980_5984 :
    AlignedValid 12 3 missing5980_5984 records5980_5984 :=
  aligned5980_5982.append aligned5982_5984

def missing5976_5984 : List (BitVec (edgeCount 12)) :=
  missing5976_5980 ++ missing5980_5984
abbrev records5976_5984 : List Blob :=
  records5976_5980 ++ records5980_5984
theorem aligned5976_5984 :
    AlignedValid 12 3 missing5976_5984 records5976_5984 :=
  aligned5976_5980.append aligned5980_5984

def missing5968_5984 : List (BitVec (edgeCount 12)) :=
  missing5968_5976 ++ missing5976_5984
abbrev records5968_5984 : List Blob :=
  records5968_5976 ++ records5976_5984
theorem aligned5968_5984 :
    AlignedValid 12 3 missing5968_5984 records5968_5984 :=
  aligned5968_5976.append aligned5976_5984

def missing5952_5984 : List (BitVec (edgeCount 12)) :=
  missing5952_5968 ++ missing5968_5984
abbrev records5952_5984 : List Blob :=
  records5952_5968 ++ records5968_5984
theorem aligned5952_5984 :
    AlignedValid 12 3 missing5952_5984 records5952_5984 :=
  aligned5952_5968.append aligned5968_5984

def missing5984_5985 : List (BitVec (edgeCount 12)) :=
  [missing5984]
abbrev records5984_5985 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5984]
theorem aligned5984_5985 :
    AlignedValid 12 3 missing5984_5985 records5984_5985 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5984
    maskCheck5984 AlignedValid.nil

def missing5985_5986 : List (BitVec (edgeCount 12)) :=
  [missing5985]
abbrev records5985_5986 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5985]
theorem aligned5985_5986 :
    AlignedValid 12 3 missing5985_5986 records5985_5986 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5985
    maskCheck5985 AlignedValid.nil

def missing5984_5986 : List (BitVec (edgeCount 12)) :=
  missing5984_5985 ++ missing5985_5986
abbrev records5984_5986 : List Blob :=
  records5984_5985 ++ records5985_5986
theorem aligned5984_5986 :
    AlignedValid 12 3 missing5984_5986 records5984_5986 :=
  aligned5984_5985.append aligned5985_5986

def missing5986_5987 : List (BitVec (edgeCount 12)) :=
  [missing5986]
abbrev records5986_5987 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5986]
theorem aligned5986_5987 :
    AlignedValid 12 3 missing5986_5987 records5986_5987 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5986
    maskCheck5986 AlignedValid.nil

def missing5987_5988 : List (BitVec (edgeCount 12)) :=
  [missing5987]
abbrev records5987_5988 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5987]
theorem aligned5987_5988 :
    AlignedValid 12 3 missing5987_5988 records5987_5988 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5987
    maskCheck5987 AlignedValid.nil

def missing5986_5988 : List (BitVec (edgeCount 12)) :=
  missing5986_5987 ++ missing5987_5988
abbrev records5986_5988 : List Blob :=
  records5986_5987 ++ records5987_5988
theorem aligned5986_5988 :
    AlignedValid 12 3 missing5986_5988 records5986_5988 :=
  aligned5986_5987.append aligned5987_5988

def missing5984_5988 : List (BitVec (edgeCount 12)) :=
  missing5984_5986 ++ missing5986_5988
abbrev records5984_5988 : List Blob :=
  records5984_5986 ++ records5986_5988
theorem aligned5984_5988 :
    AlignedValid 12 3 missing5984_5988 records5984_5988 :=
  aligned5984_5986.append aligned5986_5988

def missing5988_5989 : List (BitVec (edgeCount 12)) :=
  [missing5988]
abbrev records5988_5989 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5988]
theorem aligned5988_5989 :
    AlignedValid 12 3 missing5988_5989 records5988_5989 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5988
    maskCheck5988 AlignedValid.nil

def missing5989_5990 : List (BitVec (edgeCount 12)) :=
  [missing5989]
abbrev records5989_5990 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5989]
theorem aligned5989_5990 :
    AlignedValid 12 3 missing5989_5990 records5989_5990 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5989
    maskCheck5989 AlignedValid.nil

def missing5988_5990 : List (BitVec (edgeCount 12)) :=
  missing5988_5989 ++ missing5989_5990
abbrev records5988_5990 : List Blob :=
  records5988_5989 ++ records5989_5990
theorem aligned5988_5990 :
    AlignedValid 12 3 missing5988_5990 records5988_5990 :=
  aligned5988_5989.append aligned5989_5990

def missing5990_5991 : List (BitVec (edgeCount 12)) :=
  [missing5990]
abbrev records5990_5991 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5990]
theorem aligned5990_5991 :
    AlignedValid 12 3 missing5990_5991 records5990_5991 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5990
    maskCheck5990 AlignedValid.nil

def missing5991_5992 : List (BitVec (edgeCount 12)) :=
  [missing5991]
abbrev records5991_5992 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5991]
theorem aligned5991_5992 :
    AlignedValid 12 3 missing5991_5992 records5991_5992 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5991
    maskCheck5991 AlignedValid.nil

def missing5990_5992 : List (BitVec (edgeCount 12)) :=
  missing5990_5991 ++ missing5991_5992
abbrev records5990_5992 : List Blob :=
  records5990_5991 ++ records5991_5992
theorem aligned5990_5992 :
    AlignedValid 12 3 missing5990_5992 records5990_5992 :=
  aligned5990_5991.append aligned5991_5992

def missing5988_5992 : List (BitVec (edgeCount 12)) :=
  missing5988_5990 ++ missing5990_5992
abbrev records5988_5992 : List Blob :=
  records5988_5990 ++ records5990_5992
theorem aligned5988_5992 :
    AlignedValid 12 3 missing5988_5992 records5988_5992 :=
  aligned5988_5990.append aligned5990_5992

def missing5984_5992 : List (BitVec (edgeCount 12)) :=
  missing5984_5988 ++ missing5988_5992
abbrev records5984_5992 : List Blob :=
  records5984_5988 ++ records5988_5992
theorem aligned5984_5992 :
    AlignedValid 12 3 missing5984_5992 records5984_5992 :=
  aligned5984_5988.append aligned5988_5992

def missing5992_5993 : List (BitVec (edgeCount 12)) :=
  [missing5992]
abbrev records5992_5993 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5992]
theorem aligned5992_5993 :
    AlignedValid 12 3 missing5992_5993 records5992_5993 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5992
    maskCheck5992 AlignedValid.nil

def missing5993_5994 : List (BitVec (edgeCount 12)) :=
  [missing5993]
abbrev records5993_5994 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5993]
theorem aligned5993_5994 :
    AlignedValid 12 3 missing5993_5994 records5993_5994 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5993
    maskCheck5993 AlignedValid.nil

def missing5992_5994 : List (BitVec (edgeCount 12)) :=
  missing5992_5993 ++ missing5993_5994
abbrev records5992_5994 : List Blob :=
  records5992_5993 ++ records5993_5994
theorem aligned5992_5994 :
    AlignedValid 12 3 missing5992_5994 records5992_5994 :=
  aligned5992_5993.append aligned5993_5994

def missing5994_5995 : List (BitVec (edgeCount 12)) :=
  [missing5994]
abbrev records5994_5995 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5994]
theorem aligned5994_5995 :
    AlignedValid 12 3 missing5994_5995 records5994_5995 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5994
    maskCheck5994 AlignedValid.nil

def missing5995_5996 : List (BitVec (edgeCount 12)) :=
  [missing5995]
abbrev records5995_5996 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5995]
theorem aligned5995_5996 :
    AlignedValid 12 3 missing5995_5996 records5995_5996 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5995
    maskCheck5995 AlignedValid.nil

def missing5994_5996 : List (BitVec (edgeCount 12)) :=
  missing5994_5995 ++ missing5995_5996
abbrev records5994_5996 : List Blob :=
  records5994_5995 ++ records5995_5996
theorem aligned5994_5996 :
    AlignedValid 12 3 missing5994_5996 records5994_5996 :=
  aligned5994_5995.append aligned5995_5996

def missing5992_5996 : List (BitVec (edgeCount 12)) :=
  missing5992_5994 ++ missing5994_5996
abbrev records5992_5996 : List Blob :=
  records5992_5994 ++ records5994_5996
theorem aligned5992_5996 :
    AlignedValid 12 3 missing5992_5996 records5992_5996 :=
  aligned5992_5994.append aligned5994_5996

def missing5996_5997 : List (BitVec (edgeCount 12)) :=
  [missing5996]
abbrev records5996_5997 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5996]
theorem aligned5996_5997 :
    AlignedValid 12 3 missing5996_5997 records5996_5997 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5996
    maskCheck5996 AlignedValid.nil

def missing5997_5998 : List (BitVec (edgeCount 12)) :=
  [missing5997]
abbrev records5997_5998 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5997]
theorem aligned5997_5998 :
    AlignedValid 12 3 missing5997_5998 records5997_5998 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5997
    maskCheck5997 AlignedValid.nil

def missing5996_5998 : List (BitVec (edgeCount 12)) :=
  missing5996_5997 ++ missing5997_5998
abbrev records5996_5998 : List Blob :=
  records5996_5997 ++ records5997_5998
theorem aligned5996_5998 :
    AlignedValid 12 3 missing5996_5998 records5996_5998 :=
  aligned5996_5997.append aligned5997_5998

def missing5998_5999 : List (BitVec (edgeCount 12)) :=
  [missing5998]
abbrev records5998_5999 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5998]
theorem aligned5998_5999 :
    AlignedValid 12 3 missing5998_5999 records5998_5999 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5998
    maskCheck5998 AlignedValid.nil

def missing5999_6000 : List (BitVec (edgeCount 12)) :=
  [missing5999]
abbrev records5999_6000 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record5999]
theorem aligned5999_6000 :
    AlignedValid 12 3 missing5999_6000 records5999_6000 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check5999
    maskCheck5999 AlignedValid.nil

def missing5998_6000 : List (BitVec (edgeCount 12)) :=
  missing5998_5999 ++ missing5999_6000
abbrev records5998_6000 : List Blob :=
  records5998_5999 ++ records5999_6000
theorem aligned5998_6000 :
    AlignedValid 12 3 missing5998_6000 records5998_6000 :=
  aligned5998_5999.append aligned5999_6000

def missing5996_6000 : List (BitVec (edgeCount 12)) :=
  missing5996_5998 ++ missing5998_6000
abbrev records5996_6000 : List Blob :=
  records5996_5998 ++ records5998_6000
theorem aligned5996_6000 :
    AlignedValid 12 3 missing5996_6000 records5996_6000 :=
  aligned5996_5998.append aligned5998_6000

def missing5992_6000 : List (BitVec (edgeCount 12)) :=
  missing5992_5996 ++ missing5996_6000
abbrev records5992_6000 : List Blob :=
  records5992_5996 ++ records5996_6000
theorem aligned5992_6000 :
    AlignedValid 12 3 missing5992_6000 records5992_6000 :=
  aligned5992_5996.append aligned5996_6000

def missing5984_6000 : List (BitVec (edgeCount 12)) :=
  missing5984_5992 ++ missing5992_6000
abbrev records5984_6000 : List Blob :=
  records5984_5992 ++ records5992_6000
theorem aligned5984_6000 :
    AlignedValid 12 3 missing5984_6000 records5984_6000 :=
  aligned5984_5992.append aligned5992_6000

def missing6000_6001 : List (BitVec (edgeCount 12)) :=
  [missing6000]
abbrev records6000_6001 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6000]
theorem aligned6000_6001 :
    AlignedValid 12 3 missing6000_6001 records6000_6001 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6000
    maskCheck6000 AlignedValid.nil

def missing6001_6002 : List (BitVec (edgeCount 12)) :=
  [missing6001]
abbrev records6001_6002 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6001]
theorem aligned6001_6002 :
    AlignedValid 12 3 missing6001_6002 records6001_6002 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6001
    maskCheck6001 AlignedValid.nil

def missing6000_6002 : List (BitVec (edgeCount 12)) :=
  missing6000_6001 ++ missing6001_6002
abbrev records6000_6002 : List Blob :=
  records6000_6001 ++ records6001_6002
theorem aligned6000_6002 :
    AlignedValid 12 3 missing6000_6002 records6000_6002 :=
  aligned6000_6001.append aligned6001_6002

def missing6002_6003 : List (BitVec (edgeCount 12)) :=
  [missing6002]
abbrev records6002_6003 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6002]
theorem aligned6002_6003 :
    AlignedValid 12 3 missing6002_6003 records6002_6003 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6002
    maskCheck6002 AlignedValid.nil

def missing6003_6004 : List (BitVec (edgeCount 12)) :=
  [missing6003]
abbrev records6003_6004 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6003]
theorem aligned6003_6004 :
    AlignedValid 12 3 missing6003_6004 records6003_6004 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6003
    maskCheck6003 AlignedValid.nil

def missing6002_6004 : List (BitVec (edgeCount 12)) :=
  missing6002_6003 ++ missing6003_6004
abbrev records6002_6004 : List Blob :=
  records6002_6003 ++ records6003_6004
theorem aligned6002_6004 :
    AlignedValid 12 3 missing6002_6004 records6002_6004 :=
  aligned6002_6003.append aligned6003_6004

def missing6000_6004 : List (BitVec (edgeCount 12)) :=
  missing6000_6002 ++ missing6002_6004
abbrev records6000_6004 : List Blob :=
  records6000_6002 ++ records6002_6004
theorem aligned6000_6004 :
    AlignedValid 12 3 missing6000_6004 records6000_6004 :=
  aligned6000_6002.append aligned6002_6004

def missing6004_6005 : List (BitVec (edgeCount 12)) :=
  [missing6004]
abbrev records6004_6005 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6004]
theorem aligned6004_6005 :
    AlignedValid 12 3 missing6004_6005 records6004_6005 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6004
    maskCheck6004 AlignedValid.nil

def missing6005_6006 : List (BitVec (edgeCount 12)) :=
  [missing6005]
abbrev records6005_6006 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6005]
theorem aligned6005_6006 :
    AlignedValid 12 3 missing6005_6006 records6005_6006 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6005
    maskCheck6005 AlignedValid.nil

def missing6004_6006 : List (BitVec (edgeCount 12)) :=
  missing6004_6005 ++ missing6005_6006
abbrev records6004_6006 : List Blob :=
  records6004_6005 ++ records6005_6006
theorem aligned6004_6006 :
    AlignedValid 12 3 missing6004_6006 records6004_6006 :=
  aligned6004_6005.append aligned6005_6006

def missing6006_6007 : List (BitVec (edgeCount 12)) :=
  [missing6006]
abbrev records6006_6007 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6006]
theorem aligned6006_6007 :
    AlignedValid 12 3 missing6006_6007 records6006_6007 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6006
    maskCheck6006 AlignedValid.nil

def missing6007_6008 : List (BitVec (edgeCount 12)) :=
  [missing6007]
abbrev records6007_6008 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6007]
theorem aligned6007_6008 :
    AlignedValid 12 3 missing6007_6008 records6007_6008 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6007
    maskCheck6007 AlignedValid.nil

def missing6006_6008 : List (BitVec (edgeCount 12)) :=
  missing6006_6007 ++ missing6007_6008
abbrev records6006_6008 : List Blob :=
  records6006_6007 ++ records6007_6008
theorem aligned6006_6008 :
    AlignedValid 12 3 missing6006_6008 records6006_6008 :=
  aligned6006_6007.append aligned6007_6008

def missing6004_6008 : List (BitVec (edgeCount 12)) :=
  missing6004_6006 ++ missing6006_6008
abbrev records6004_6008 : List Blob :=
  records6004_6006 ++ records6006_6008
theorem aligned6004_6008 :
    AlignedValid 12 3 missing6004_6008 records6004_6008 :=
  aligned6004_6006.append aligned6006_6008

def missing6000_6008 : List (BitVec (edgeCount 12)) :=
  missing6000_6004 ++ missing6004_6008
abbrev records6000_6008 : List Blob :=
  records6000_6004 ++ records6004_6008
theorem aligned6000_6008 :
    AlignedValid 12 3 missing6000_6008 records6000_6008 :=
  aligned6000_6004.append aligned6004_6008

def missing6008_6009 : List (BitVec (edgeCount 12)) :=
  [missing6008]
abbrev records6008_6009 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6008]
theorem aligned6008_6009 :
    AlignedValid 12 3 missing6008_6009 records6008_6009 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6008
    maskCheck6008 AlignedValid.nil

def missing6009_6010 : List (BitVec (edgeCount 12)) :=
  [missing6009]
abbrev records6009_6010 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6009]
theorem aligned6009_6010 :
    AlignedValid 12 3 missing6009_6010 records6009_6010 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6009
    maskCheck6009 AlignedValid.nil

def missing6008_6010 : List (BitVec (edgeCount 12)) :=
  missing6008_6009 ++ missing6009_6010
abbrev records6008_6010 : List Blob :=
  records6008_6009 ++ records6009_6010
theorem aligned6008_6010 :
    AlignedValid 12 3 missing6008_6010 records6008_6010 :=
  aligned6008_6009.append aligned6009_6010

def missing6010_6011 : List (BitVec (edgeCount 12)) :=
  [missing6010]
abbrev records6010_6011 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6010]
theorem aligned6010_6011 :
    AlignedValid 12 3 missing6010_6011 records6010_6011 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6010
    maskCheck6010 AlignedValid.nil

def missing6011_6012 : List (BitVec (edgeCount 12)) :=
  [missing6011]
abbrev records6011_6012 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6011]
theorem aligned6011_6012 :
    AlignedValid 12 3 missing6011_6012 records6011_6012 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6011
    maskCheck6011 AlignedValid.nil

def missing6010_6012 : List (BitVec (edgeCount 12)) :=
  missing6010_6011 ++ missing6011_6012
abbrev records6010_6012 : List Blob :=
  records6010_6011 ++ records6011_6012
theorem aligned6010_6012 :
    AlignedValid 12 3 missing6010_6012 records6010_6012 :=
  aligned6010_6011.append aligned6011_6012

def missing6008_6012 : List (BitVec (edgeCount 12)) :=
  missing6008_6010 ++ missing6010_6012
abbrev records6008_6012 : List Blob :=
  records6008_6010 ++ records6010_6012
theorem aligned6008_6012 :
    AlignedValid 12 3 missing6008_6012 records6008_6012 :=
  aligned6008_6010.append aligned6010_6012

def missing6012_6013 : List (BitVec (edgeCount 12)) :=
  [missing6012]
abbrev records6012_6013 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6012]
theorem aligned6012_6013 :
    AlignedValid 12 3 missing6012_6013 records6012_6013 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6012
    maskCheck6012 AlignedValid.nil

def missing6013_6014 : List (BitVec (edgeCount 12)) :=
  [missing6013]
abbrev records6013_6014 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6013]
theorem aligned6013_6014 :
    AlignedValid 12 3 missing6013_6014 records6013_6014 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6013
    maskCheck6013 AlignedValid.nil

def missing6012_6014 : List (BitVec (edgeCount 12)) :=
  missing6012_6013 ++ missing6013_6014
abbrev records6012_6014 : List Blob :=
  records6012_6013 ++ records6013_6014
theorem aligned6012_6014 :
    AlignedValid 12 3 missing6012_6014 records6012_6014 :=
  aligned6012_6013.append aligned6013_6014

def missing6014_6015 : List (BitVec (edgeCount 12)) :=
  [missing6014]
abbrev records6014_6015 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6014]
theorem aligned6014_6015 :
    AlignedValid 12 3 missing6014_6015 records6014_6015 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6014
    maskCheck6014 AlignedValid.nil

def missing6015_6016 : List (BitVec (edgeCount 12)) :=
  [missing6015]
abbrev records6015_6016 : List Blob :=
  [StrongPackedBucketN12A3Shard046.record6015]
theorem aligned6015_6016 :
    AlignedValid 12 3 missing6015_6016 records6015_6016 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard046.check6015
    maskCheck6015 AlignedValid.nil

def missing6014_6016 : List (BitVec (edgeCount 12)) :=
  missing6014_6015 ++ missing6015_6016
abbrev records6014_6016 : List Blob :=
  records6014_6015 ++ records6015_6016
theorem aligned6014_6016 :
    AlignedValid 12 3 missing6014_6016 records6014_6016 :=
  aligned6014_6015.append aligned6015_6016

def missing6012_6016 : List (BitVec (edgeCount 12)) :=
  missing6012_6014 ++ missing6014_6016
abbrev records6012_6016 : List Blob :=
  records6012_6014 ++ records6014_6016
theorem aligned6012_6016 :
    AlignedValid 12 3 missing6012_6016 records6012_6016 :=
  aligned6012_6014.append aligned6014_6016

def missing6008_6016 : List (BitVec (edgeCount 12)) :=
  missing6008_6012 ++ missing6012_6016
abbrev records6008_6016 : List Blob :=
  records6008_6012 ++ records6012_6016
theorem aligned6008_6016 :
    AlignedValid 12 3 missing6008_6016 records6008_6016 :=
  aligned6008_6012.append aligned6012_6016

def missing6000_6016 : List (BitVec (edgeCount 12)) :=
  missing6000_6008 ++ missing6008_6016
abbrev records6000_6016 : List Blob :=
  records6000_6008 ++ records6008_6016
theorem aligned6000_6016 :
    AlignedValid 12 3 missing6000_6016 records6000_6016 :=
  aligned6000_6008.append aligned6008_6016

def missing5984_6016 : List (BitVec (edgeCount 12)) :=
  missing5984_6000 ++ missing6000_6016
abbrev records5984_6016 : List Blob :=
  records5984_6000 ++ records6000_6016
theorem aligned5984_6016 :
    AlignedValid 12 3 missing5984_6016 records5984_6016 :=
  aligned5984_6000.append aligned6000_6016

def missing5952_6016 : List (BitVec (edgeCount 12)) :=
  missing5952_5984 ++ missing5984_6016
abbrev records5952_6016 : List Blob :=
  records5952_5984 ++ records5984_6016
theorem aligned5952_6016 :
    AlignedValid 12 3 missing5952_6016 records5952_6016 :=
  aligned5952_5984.append aligned5984_6016

def missing5888_6016 : List (BitVec (edgeCount 12)) :=
  missing5888_5952 ++ missing5952_6016
abbrev records5888_6016 : List Blob :=
  records5888_5952 ++ records5952_6016
theorem aligned5888_6016 :
    AlignedValid 12 3 missing5888_6016 records5888_6016 :=
  aligned5888_5952.append aligned5952_6016

abbrev missing : List (BitVec (edgeCount 12)) := missing5888_6016
abbrev records : List Blob := records5888_6016
theorem aligned : AlignedValid 12 3 missing records := aligned5888_6016

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard046
