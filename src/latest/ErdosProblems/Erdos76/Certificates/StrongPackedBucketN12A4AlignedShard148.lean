/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard148

/-! Decode-only alignment checks for n=12, a=4, records 18944--19071. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard148

open PackedBucketCertificate

def missing18944 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 545042001920262144
theorem maskCheck18944 :
    checkMaskFor missing18944 StrongPackedBucketN12A4Shard148.record18944 = true := by
  decide

def missing18945 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1049445160185757696
theorem maskCheck18945 :
    checkMaskFor missing18945 StrongPackedBucketN12A4Shard148.record18945 = true := by
  decide

def missing18946 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1085473957204721664
theorem maskCheck18946 :
    checkMaskFor missing18946 StrongPackedBucketN12A4Shard148.record18946 = true := by
  decide

def missing18947 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1950165085659856896
theorem maskCheck18947 :
    checkMaskFor missing18947 StrongPackedBucketN12A4Shard148.record18947 = true := by
  decide

def missing18948 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2166337867773640704
theorem maskCheck18948 :
    checkMaskFor missing18948 StrongPackedBucketN12A4Shard148.record18948 = true := by
  decide

def missing18949 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4111892906797694976
theorem maskCheck18949 :
    checkMaskFor missing18949 StrongPackedBucketN12A4Shard148.record18949 = true := by
  decide

def missing18950 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4183950500835622912
theorem maskCheck18950 :
    checkMaskFor missing18950 StrongPackedBucketN12A4Shard148.record18950 = true := by
  decide

def missing18951 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4868497644195938304
theorem maskCheck18951 :
    checkMaskFor missing18951 StrongPackedBucketN12A4Shard148.record18951 = true := by
  decide

def missing18952 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5084670426309722112
theorem maskCheck18952 :
    checkMaskFor missing18952 StrongPackedBucketN12A4Shard148.record18952 = true := by
  decide

def missing18953 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5120699223328686080
theorem maskCheck18953 :
    checkMaskFor missing18953 StrongPackedBucketN12A4Shard148.record18953 = true := by
  decide

def missing18954 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5300843208423505920
theorem maskCheck18954 :
    checkMaskFor missing18954 StrongPackedBucketN12A4Shard148.record18954 = true := by
  decide

def missing18955 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5372900802461433856
theorem maskCheck18955 :
    checkMaskFor missing18955 StrongPackedBucketN12A4Shard148.record18955 = true := by
  decide

def missing18956 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5408929599480397824
theorem maskCheck18956 :
    checkMaskFor missing18956 StrongPackedBucketN12A4Shard148.record18956 = true := by
  decide

def missing18957 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5625102381594181632
theorem maskCheck18957 :
    checkMaskFor missing18957 StrongPackedBucketN12A4Shard148.record18957 = true := by
  decide

def missing18958 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6417735916011388928
theorem maskCheck18958 :
    checkMaskFor missing18958 StrongPackedBucketN12A4Shard148.record18958 = true := by
  decide

def missing18959 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6489793510049316864
theorem maskCheck18959 :
    checkMaskFor missing18959 StrongPackedBucketN12A4Shard148.record18959 = true := by
  decide

def missing18960 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8651521331187154944
theorem maskCheck18960 :
    checkMaskFor missing18960 StrongPackedBucketN12A4Shard148.record18960 = true := by
  decide

def missing18961 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9480183662623326208
theorem maskCheck18961 :
    checkMaskFor missing18961 StrongPackedBucketN12A4Shard148.record18961 = true := by
  decide

def missing18962 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9696356444737110016
theorem maskCheck18962 :
    checkMaskFor missing18962 StrongPackedBucketN12A4Shard148.record18962 = true := by
  decide

def missing18963 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9732385241756073984
theorem maskCheck18963 :
    checkMaskFor missing18963 StrongPackedBucketN12A4Shard148.record18963 = true := by
  decide

def missing18964 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9912529226850893824
theorem maskCheck18964 :
    checkMaskFor missing18964 StrongPackedBucketN12A4Shard148.record18964 = true := by
  decide

def missing18965 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9984586820888821760
theorem maskCheck18965 :
    checkMaskFor missing18965 StrongPackedBucketN12A4Shard148.record18965 = true := by
  decide

def missing18966 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10020615617907785728
theorem maskCheck18966 :
    checkMaskFor missing18966 StrongPackedBucketN12A4Shard148.record18966 = true := by
  decide

def missing18967 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10236788400021569536
theorem maskCheck18967 :
    checkMaskFor missing18967 StrongPackedBucketN12A4Shard148.record18967 = true := by
  decide

def missing18968 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11029421934438776832
theorem maskCheck18968 :
    checkMaskFor missing18968 StrongPackedBucketN12A4Shard148.record18968 = true := by
  decide

def missing18969 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11101479528476704768
theorem maskCheck18969 :
    checkMaskFor missing18969 StrongPackedBucketN12A4Shard148.record18969 = true := by
  decide

def missing18970 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13263207349614542848
theorem maskCheck18970 :
    checkMaskFor missing18970 StrongPackedBucketN12A4Shard148.record18970 = true := by
  decide

def missing18971 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13947754492974858240
theorem maskCheck18971 :
    checkMaskFor missing18971 StrongPackedBucketN12A4Shard148.record18971 = true := by
  decide

def missing18972 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14019812087012786176
theorem maskCheck18972 :
    checkMaskFor missing18972 StrongPackedBucketN12A4Shard148.record18972 = true := by
  decide

def missing18973 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14055840884031750144
theorem maskCheck18973 :
    checkMaskFor missing18973 StrongPackedBucketN12A4Shard148.record18973 = true := by
  decide

def missing18974 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14272013666145533952
theorem maskCheck18974 :
    checkMaskFor missing18974 StrongPackedBucketN12A4Shard148.record18974 = true := by
  decide

def missing18975 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14452157651240353792
theorem maskCheck18975 :
    checkMaskFor missing18975 StrongPackedBucketN12A4Shard148.record18975 = true := by
  decide

def missing18976 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14488186448259317760
theorem maskCheck18976 :
    checkMaskFor missing18976 StrongPackedBucketN12A4Shard148.record18976 = true := by
  decide

def missing18977 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14560244042297245696
theorem maskCheck18977 :
    checkMaskFor missing18977 StrongPackedBucketN12A4Shard148.record18977 = true := by
  decide

def missing18978 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15569050358828236800
theorem maskCheck18978 :
    checkMaskFor missing18978 StrongPackedBucketN12A4Shard148.record18978 = true := by
  decide

def missing18979 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23495385703000309760
theorem maskCheck18979 :
    checkMaskFor missing18979 StrongPackedBucketN12A4Shard148.record18979 = true := by
  decide

def missing18980 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23783616079152021504
theorem maskCheck18980 :
    checkMaskFor missing18980 StrongPackedBucketN12A4Shard148.record18980 = true := by
  decide

def missing18981 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24792422395683012608
theorem maskCheck18981 :
    checkMaskFor missing18981 StrongPackedBucketN12A4Shard148.record18981 = true := by
  decide

def missing18982 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27782812548257021952
theorem maskCheck18982 :
    checkMaskFor missing18982 StrongPackedBucketN12A4Shard148.record18982 = true := by
  decide

def missing18983 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32322440972646481920
theorem maskCheck18983 :
    checkMaskFor missing18983 StrongPackedBucketN12A4Shard148.record18983 = true := by
  decide

def missing18984 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37150299773187653632
theorem maskCheck18984 :
    checkMaskFor missing18984 StrongPackedBucketN12A4Shard148.record18984 = true := by
  decide

def missing18985 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37366472555301437440
theorem maskCheck18985 :
    checkMaskFor missing18985 StrongPackedBucketN12A4Shard148.record18985 = true := by
  decide

def missing18986 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37402501352320401408
theorem maskCheck18986 :
    checkMaskFor missing18986 StrongPackedBucketN12A4Shard148.record18986 = true := by
  decide

def missing18987 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37582645337415221248
theorem maskCheck18987 :
    checkMaskFor missing18987 StrongPackedBucketN12A4Shard148.record18987 = true := by
  decide

def missing18988 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37690731728472113152
theorem maskCheck18988 :
    checkMaskFor missing18988 StrongPackedBucketN12A4Shard148.record18988 = true := by
  decide

def missing18989 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41617870603539185664
theorem maskCheck18989 :
    checkMaskFor missing18989 StrongPackedBucketN12A4Shard148.record18989 = true := by
  decide

def missing18990 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41725956994596077568
theorem maskCheck18990 :
    checkMaskFor missing18990 StrongPackedBucketN12A4Shard148.record18990 = true := by
  decide

def missing18991 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41942129776709861376
theorem maskCheck18991 :
    checkMaskFor missing18991 StrongPackedBucketN12A4Shard148.record18991 = true := by
  decide

def missing18992 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42158302558823645184
theorem maskCheck18992 :
    checkMaskFor missing18992 StrongPackedBucketN12A4Shard148.record18992 = true := by
  decide

def missing18993 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46229556621966573568
theorem maskCheck18993 :
    checkMaskFor missing18993 StrongPackedBucketN12A4Shard148.record18993 = true := by
  decide

def missing18994 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46301614216004501504
theorem maskCheck18994 :
    checkMaskFor missing18994 StrongPackedBucketN12A4Shard148.record18994 = true := by
  decide

def missing18995 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46337643013023465472
theorem maskCheck18995 :
    checkMaskFor missing18995 StrongPackedBucketN12A4Shard148.record18995 = true := by
  decide

def missing18996 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46553815795137249280
theorem maskCheck18996 :
    checkMaskFor missing18996 StrongPackedBucketN12A4Shard148.record18996 = true := by
  decide

def missing18997 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46733959780232069120
theorem maskCheck18997 :
    checkMaskFor missing18997 StrongPackedBucketN12A4Shard148.record18997 = true := by
  decide

def missing18998 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46769988577251033088
theorem maskCheck18998 :
    checkMaskFor missing18998 StrongPackedBucketN12A4Shard148.record18998 = true := by
  decide

def missing18999 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46842046171288961024
theorem maskCheck18999 :
    checkMaskFor missing18999 StrongPackedBucketN12A4Shard148.record18999 = true := by
  decide

def missing19000 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50769185046356033536
theorem maskCheck19000 :
    checkMaskFor missing19000 StrongPackedBucketN12A4Shard148.record19000 = true := by
  decide

def missing19001 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50805213843374997504
theorem maskCheck19001 :
    checkMaskFor missing19001 StrongPackedBucketN12A4Shard148.record19001 = true := by
  decide

def missing19002 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50877271437412925440
theorem maskCheck19002 :
    checkMaskFor missing19002 StrongPackedBucketN12A4Shard148.record19002 = true := by
  decide

def missing19003 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51309617001640493056
theorem maskCheck19003 :
    checkMaskFor missing19003 StrongPackedBucketN12A4Shard148.record19003 = true := by
  decide

def missing19004 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55452928658821349376
theorem maskCheck19004 :
    checkMaskFor missing19004 StrongPackedBucketN12A4Shard148.record19004 = true := by
  decide

def missing19005 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55561015049878241280
theorem maskCheck19005 :
    checkMaskFor missing19005 StrongPackedBucketN12A4Shard148.record19005 = true := by
  decide

def missing19006 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55777187831992025088
theorem maskCheck19006 :
    checkMaskFor missing19006 StrongPackedBucketN12A4Shard148.record19006 = true := by
  decide

def missing19007 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55957331817086844928
theorem maskCheck19007 :
    checkMaskFor missing19007 StrongPackedBucketN12A4Shard148.record19007 = true := by
  decide

def missing19008 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55993360614105808896
theorem maskCheck19008 :
    checkMaskFor missing19008 StrongPackedBucketN12A4Shard148.record19008 = true := by
  decide

def missing19009 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56065418208143736832
theorem maskCheck19009 :
    checkMaskFor missing19009 StrongPackedBucketN12A4Shard148.record19009 = true := by
  decide

def missing19010 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57074224524674727936
theorem maskCheck19010 :
    checkMaskFor missing19010 StrongPackedBucketN12A4Shard148.record19010 = true := by
  decide

def missing19011 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59992557083210809344
theorem maskCheck19011 :
    checkMaskFor missing19011 StrongPackedBucketN12A4Shard148.record19011 = true := by
  decide

def missing19012 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60028585880229773312
theorem maskCheck19012 :
    checkMaskFor missing19012 StrongPackedBucketN12A4Shard148.record19012 = true := by
  decide

def missing19013 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60100643474267701248
theorem maskCheck19013 :
    checkMaskFor missing19013 StrongPackedBucketN12A4Shard148.record19013 = true := by
  decide

def missing19014 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60532989038495268864
theorem maskCheck19014 :
    checkMaskFor missing19014 StrongPackedBucketN12A4Shard148.record19014 = true := by
  decide

def missing19015 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64604243101638197248
theorem maskCheck19015 :
    checkMaskFor missing19015 StrongPackedBucketN12A4Shard148.record19015 = true := by
  decide

def missing19016 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64640271898657161216
theorem maskCheck19016 :
    checkMaskFor missing19016 StrongPackedBucketN12A4Shard148.record19016 = true := by
  decide

def missing19017 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64712329492695089152
theorem maskCheck19017 :
    checkMaskFor missing19017 StrongPackedBucketN12A4Shard148.record19017 = true := by
  decide

def missing19018 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65144675056922656768
theorem maskCheck19018 :
    checkMaskFor missing19018 StrongPackedBucketN12A4Shard148.record19018 = true := by
  decide

def missing19019 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 69179900323046621184
theorem maskCheck19019 :
    checkMaskFor missing19019 StrongPackedBucketN12A4Shard148.record19019 = true := by
  decide

def missing19020 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 545147555036528640
theorem maskCheck19020 :
    checkMaskFor missing19020 StrongPackedBucketN12A4Shard148.record19020 = true := by
  decide

def missing19021 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 833377931188240384
theorem maskCheck19021 :
    checkMaskFor missing19021 StrongPackedBucketN12A4Shard148.record19021 = true := by
  decide

def missing19022 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 977493119264096256
theorem maskCheck19022 :
    checkMaskFor missing19022 StrongPackedBucketN12A4Shard148.record19022 = true := by
  decide

def missing19023 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1049550713302024192
theorem maskCheck19023 :
    checkMaskFor missing19023 StrongPackedBucketN12A4Shard148.record19023 = true := by
  decide

def missing19024 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1085579510320988160
theorem maskCheck19024 :
    checkMaskFor missing19024 StrongPackedBucketN12A4Shard148.record19024 = true := by
  decide

def missing19025 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1842184247719231488
theorem maskCheck19025 :
    checkMaskFor missing19025 StrongPackedBucketN12A4Shard148.record19025 = true := by
  decide

def missing19026 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1914241841757159424
theorem maskCheck19026 :
    checkMaskFor missing19026 StrongPackedBucketN12A4Shard148.record19026 = true := by
  decide

def missing19027 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1950270638776123392
theorem maskCheck19027 :
    checkMaskFor missing19027 StrongPackedBucketN12A4Shard148.record19027 = true := by
  decide

def missing19028 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2058357029833015296
theorem maskCheck19028 :
    checkMaskFor missing19028 StrongPackedBucketN12A4Shard148.record19028 = true := by
  decide

def missing19029 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2094385826851979264
theorem maskCheck19029 :
    checkMaskFor missing19029 StrongPackedBucketN12A4Shard148.record19029 = true := by
  decide

def missing19030 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2166443420889907200
theorem maskCheck19030 :
    checkMaskFor missing19030 StrongPackedBucketN12A4Shard148.record19030 = true := by
  decide

def missing19031 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4075969662894997504
theorem maskCheck19031 :
    checkMaskFor missing19031 StrongPackedBucketN12A4Shard148.record19031 = true := by
  decide

def missing19032 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4111998459913961472
theorem maskCheck19032 :
    checkMaskFor missing19032 StrongPackedBucketN12A4Shard148.record19032 = true := by
  decide

def missing19033 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4184056053951889408
theorem maskCheck19033 :
    checkMaskFor missing19033 StrongPackedBucketN12A4Shard148.record19033 = true := by
  decide

def missing19034 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4328171242027745280
theorem maskCheck19034 :
    checkMaskFor missing19034 StrongPackedBucketN12A4Shard148.record19034 = true := by
  decide

def missing19035 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4868603197312204800
theorem maskCheck19035 :
    checkMaskFor missing19035 StrongPackedBucketN12A4Shard148.record19035 = true := by
  decide

def missing19036 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5012718385388060672
theorem maskCheck19036 :
    checkMaskFor missing19036 StrongPackedBucketN12A4Shard148.record19036 = true := by
  decide

def missing19037 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5084775979425988608
theorem maskCheck19037 :
    checkMaskFor missing19037 StrongPackedBucketN12A4Shard148.record19037 = true := by
  decide

def missing19038 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5120804776444952576
theorem maskCheck19038 :
    checkMaskFor missing19038 StrongPackedBucketN12A4Shard148.record19038 = true := by
  decide

def missing19039 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5300948761539772416
theorem maskCheck19039 :
    checkMaskFor missing19039 StrongPackedBucketN12A4Shard148.record19039 = true := by
  decide

def missing19040 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5373006355577700352
theorem maskCheck19040 :
    checkMaskFor missing19040 StrongPackedBucketN12A4Shard148.record19040 = true := by
  decide

def missing19041 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5409035152596664320
theorem maskCheck19041 :
    checkMaskFor missing19041 StrongPackedBucketN12A4Shard148.record19041 = true := by
  decide

def missing19042 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5517121543653556224
theorem maskCheck19042 :
    checkMaskFor missing19042 StrongPackedBucketN12A4Shard148.record19042 = true := by
  decide

def missing19043 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5553150340672520192
theorem maskCheck19043 :
    checkMaskFor missing19043 StrongPackedBucketN12A4Shard148.record19043 = true := by
  decide

def missing19044 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5625207934710448128
theorem maskCheck19044 :
    checkMaskFor missing19044 StrongPackedBucketN12A4Shard148.record19044 = true := by
  decide

def missing19045 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6381812672108691456
theorem maskCheck19045 :
    checkMaskFor missing19045 StrongPackedBucketN12A4Shard148.record19045 = true := by
  decide

def missing19046 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6417841469127655424
theorem maskCheck19046 :
    checkMaskFor missing19046 StrongPackedBucketN12A4Shard148.record19046 = true := by
  decide

def missing19047 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6489899063165583360
theorem maskCheck19047 :
    checkMaskFor missing19047 StrongPackedBucketN12A4Shard148.record19047 = true := by
  decide

def missing19048 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6634014251241439232
theorem maskCheck19048 :
    checkMaskFor missing19048 StrongPackedBucketN12A4Shard148.record19048 = true := by
  decide

def missing19049 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8651626884303421440
theorem maskCheck19049 :
    checkMaskFor missing19049 StrongPackedBucketN12A4Shard148.record19049 = true := by
  decide

def missing19050 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9480289215739592704
theorem maskCheck19050 :
    checkMaskFor missing19050 StrongPackedBucketN12A4Shard148.record19050 = true := by
  decide

def missing19051 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9624404403815448576
theorem maskCheck19051 :
    checkMaskFor missing19051 StrongPackedBucketN12A4Shard148.record19051 = true := by
  decide

def missing19052 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9696461997853376512
theorem maskCheck19052 :
    checkMaskFor missing19052 StrongPackedBucketN12A4Shard148.record19052 = true := by
  decide

def missing19053 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9732490794872340480
theorem maskCheck19053 :
    checkMaskFor missing19053 StrongPackedBucketN12A4Shard148.record19053 = true := by
  decide

def missing19054 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9912634779967160320
theorem maskCheck19054 :
    checkMaskFor missing19054 StrongPackedBucketN12A4Shard148.record19054 = true := by
  decide

def missing19055 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9984692374005088256
theorem maskCheck19055 :
    checkMaskFor missing19055 StrongPackedBucketN12A4Shard148.record19055 = true := by
  decide

def missing19056 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10020721171024052224
theorem maskCheck19056 :
    checkMaskFor missing19056 StrongPackedBucketN12A4Shard148.record19056 = true := by
  decide

def missing19057 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10128807562080944128
theorem maskCheck19057 :
    checkMaskFor missing19057 StrongPackedBucketN12A4Shard148.record19057 = true := by
  decide

def missing19058 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10164836359099908096
theorem maskCheck19058 :
    checkMaskFor missing19058 StrongPackedBucketN12A4Shard148.record19058 = true := by
  decide

def missing19059 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10236893953137836032
theorem maskCheck19059 :
    checkMaskFor missing19059 StrongPackedBucketN12A4Shard148.record19059 = true := by
  decide

def missing19060 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10993498690536079360
theorem maskCheck19060 :
    checkMaskFor missing19060 StrongPackedBucketN12A4Shard148.record19060 = true := by
  decide

def missing19061 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11029527487555043328
theorem maskCheck19061 :
    checkMaskFor missing19061 StrongPackedBucketN12A4Shard148.record19061 = true := by
  decide

def missing19062 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11101585081592971264
theorem maskCheck19062 :
    checkMaskFor missing19062 StrongPackedBucketN12A4Shard148.record19062 = true := by
  decide

def missing19063 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11245700269668827136
theorem maskCheck19063 :
    checkMaskFor missing19063 StrongPackedBucketN12A4Shard148.record19063 = true := by
  decide

def missing19064 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13263312902730809344
theorem maskCheck19064 :
    checkMaskFor missing19064 StrongPackedBucketN12A4Shard148.record19064 = true := by
  decide

def missing19065 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13947860046091124736
theorem maskCheck19065 :
    checkMaskFor missing19065 StrongPackedBucketN12A4Shard148.record19065 = true := by
  decide

def missing19066 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14019917640129052672
theorem maskCheck19066 :
    checkMaskFor missing19066 StrongPackedBucketN12A4Shard148.record19066 = true := by
  decide

def missing19067 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14055946437148016640
theorem maskCheck19067 :
    checkMaskFor missing19067 StrongPackedBucketN12A4Shard148.record19067 = true := by
  decide

def missing19068 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14164032828204908544
theorem maskCheck19068 :
    checkMaskFor missing19068 StrongPackedBucketN12A4Shard148.record19068 = true := by
  decide

def missing19069 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14200061625223872512
theorem maskCheck19069 :
    checkMaskFor missing19069 StrongPackedBucketN12A4Shard148.record19069 = true := by
  decide

def missing19070 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14272119219261800448
theorem maskCheck19070 :
    checkMaskFor missing19070 StrongPackedBucketN12A4Shard148.record19070 = true := by
  decide

def missing19071 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14452263204356620288
theorem maskCheck19071 :
    checkMaskFor missing19071 StrongPackedBucketN12A4Shard148.record19071 = true := by
  decide

def missing18944_18945 : List (BitVec (edgeCount 12)) :=
  [missing18944]
abbrev records18944_18945 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18944]
theorem aligned18944_18945 :
    AlignedValid 12 4 missing18944_18945 records18944_18945 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18944
    maskCheck18944 AlignedValid.nil

def missing18945_18946 : List (BitVec (edgeCount 12)) :=
  [missing18945]
abbrev records18945_18946 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18945]
theorem aligned18945_18946 :
    AlignedValid 12 4 missing18945_18946 records18945_18946 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18945
    maskCheck18945 AlignedValid.nil

def missing18944_18946 : List (BitVec (edgeCount 12)) :=
  missing18944_18945 ++ missing18945_18946
abbrev records18944_18946 : List Blob :=
  records18944_18945 ++ records18945_18946
theorem aligned18944_18946 :
    AlignedValid 12 4 missing18944_18946 records18944_18946 :=
  aligned18944_18945.append aligned18945_18946

def missing18946_18947 : List (BitVec (edgeCount 12)) :=
  [missing18946]
abbrev records18946_18947 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18946]
theorem aligned18946_18947 :
    AlignedValid 12 4 missing18946_18947 records18946_18947 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18946
    maskCheck18946 AlignedValid.nil

def missing18947_18948 : List (BitVec (edgeCount 12)) :=
  [missing18947]
abbrev records18947_18948 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18947]
theorem aligned18947_18948 :
    AlignedValid 12 4 missing18947_18948 records18947_18948 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18947
    maskCheck18947 AlignedValid.nil

def missing18946_18948 : List (BitVec (edgeCount 12)) :=
  missing18946_18947 ++ missing18947_18948
abbrev records18946_18948 : List Blob :=
  records18946_18947 ++ records18947_18948
theorem aligned18946_18948 :
    AlignedValid 12 4 missing18946_18948 records18946_18948 :=
  aligned18946_18947.append aligned18947_18948

def missing18944_18948 : List (BitVec (edgeCount 12)) :=
  missing18944_18946 ++ missing18946_18948
abbrev records18944_18948 : List Blob :=
  records18944_18946 ++ records18946_18948
theorem aligned18944_18948 :
    AlignedValid 12 4 missing18944_18948 records18944_18948 :=
  aligned18944_18946.append aligned18946_18948

def missing18948_18949 : List (BitVec (edgeCount 12)) :=
  [missing18948]
abbrev records18948_18949 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18948]
theorem aligned18948_18949 :
    AlignedValid 12 4 missing18948_18949 records18948_18949 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18948
    maskCheck18948 AlignedValid.nil

def missing18949_18950 : List (BitVec (edgeCount 12)) :=
  [missing18949]
abbrev records18949_18950 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18949]
theorem aligned18949_18950 :
    AlignedValid 12 4 missing18949_18950 records18949_18950 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18949
    maskCheck18949 AlignedValid.nil

def missing18948_18950 : List (BitVec (edgeCount 12)) :=
  missing18948_18949 ++ missing18949_18950
abbrev records18948_18950 : List Blob :=
  records18948_18949 ++ records18949_18950
theorem aligned18948_18950 :
    AlignedValid 12 4 missing18948_18950 records18948_18950 :=
  aligned18948_18949.append aligned18949_18950

def missing18950_18951 : List (BitVec (edgeCount 12)) :=
  [missing18950]
abbrev records18950_18951 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18950]
theorem aligned18950_18951 :
    AlignedValid 12 4 missing18950_18951 records18950_18951 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18950
    maskCheck18950 AlignedValid.nil

def missing18951_18952 : List (BitVec (edgeCount 12)) :=
  [missing18951]
abbrev records18951_18952 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18951]
theorem aligned18951_18952 :
    AlignedValid 12 4 missing18951_18952 records18951_18952 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18951
    maskCheck18951 AlignedValid.nil

def missing18950_18952 : List (BitVec (edgeCount 12)) :=
  missing18950_18951 ++ missing18951_18952
abbrev records18950_18952 : List Blob :=
  records18950_18951 ++ records18951_18952
theorem aligned18950_18952 :
    AlignedValid 12 4 missing18950_18952 records18950_18952 :=
  aligned18950_18951.append aligned18951_18952

def missing18948_18952 : List (BitVec (edgeCount 12)) :=
  missing18948_18950 ++ missing18950_18952
abbrev records18948_18952 : List Blob :=
  records18948_18950 ++ records18950_18952
theorem aligned18948_18952 :
    AlignedValid 12 4 missing18948_18952 records18948_18952 :=
  aligned18948_18950.append aligned18950_18952

def missing18944_18952 : List (BitVec (edgeCount 12)) :=
  missing18944_18948 ++ missing18948_18952
abbrev records18944_18952 : List Blob :=
  records18944_18948 ++ records18948_18952
theorem aligned18944_18952 :
    AlignedValid 12 4 missing18944_18952 records18944_18952 :=
  aligned18944_18948.append aligned18948_18952

def missing18952_18953 : List (BitVec (edgeCount 12)) :=
  [missing18952]
abbrev records18952_18953 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18952]
theorem aligned18952_18953 :
    AlignedValid 12 4 missing18952_18953 records18952_18953 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18952
    maskCheck18952 AlignedValid.nil

def missing18953_18954 : List (BitVec (edgeCount 12)) :=
  [missing18953]
abbrev records18953_18954 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18953]
theorem aligned18953_18954 :
    AlignedValid 12 4 missing18953_18954 records18953_18954 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18953
    maskCheck18953 AlignedValid.nil

def missing18952_18954 : List (BitVec (edgeCount 12)) :=
  missing18952_18953 ++ missing18953_18954
abbrev records18952_18954 : List Blob :=
  records18952_18953 ++ records18953_18954
theorem aligned18952_18954 :
    AlignedValid 12 4 missing18952_18954 records18952_18954 :=
  aligned18952_18953.append aligned18953_18954

def missing18954_18955 : List (BitVec (edgeCount 12)) :=
  [missing18954]
abbrev records18954_18955 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18954]
theorem aligned18954_18955 :
    AlignedValid 12 4 missing18954_18955 records18954_18955 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18954
    maskCheck18954 AlignedValid.nil

def missing18955_18956 : List (BitVec (edgeCount 12)) :=
  [missing18955]
abbrev records18955_18956 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18955]
theorem aligned18955_18956 :
    AlignedValid 12 4 missing18955_18956 records18955_18956 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18955
    maskCheck18955 AlignedValid.nil

def missing18954_18956 : List (BitVec (edgeCount 12)) :=
  missing18954_18955 ++ missing18955_18956
abbrev records18954_18956 : List Blob :=
  records18954_18955 ++ records18955_18956
theorem aligned18954_18956 :
    AlignedValid 12 4 missing18954_18956 records18954_18956 :=
  aligned18954_18955.append aligned18955_18956

def missing18952_18956 : List (BitVec (edgeCount 12)) :=
  missing18952_18954 ++ missing18954_18956
abbrev records18952_18956 : List Blob :=
  records18952_18954 ++ records18954_18956
theorem aligned18952_18956 :
    AlignedValid 12 4 missing18952_18956 records18952_18956 :=
  aligned18952_18954.append aligned18954_18956

def missing18956_18957 : List (BitVec (edgeCount 12)) :=
  [missing18956]
abbrev records18956_18957 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18956]
theorem aligned18956_18957 :
    AlignedValid 12 4 missing18956_18957 records18956_18957 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18956
    maskCheck18956 AlignedValid.nil

def missing18957_18958 : List (BitVec (edgeCount 12)) :=
  [missing18957]
abbrev records18957_18958 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18957]
theorem aligned18957_18958 :
    AlignedValid 12 4 missing18957_18958 records18957_18958 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18957
    maskCheck18957 AlignedValid.nil

def missing18956_18958 : List (BitVec (edgeCount 12)) :=
  missing18956_18957 ++ missing18957_18958
abbrev records18956_18958 : List Blob :=
  records18956_18957 ++ records18957_18958
theorem aligned18956_18958 :
    AlignedValid 12 4 missing18956_18958 records18956_18958 :=
  aligned18956_18957.append aligned18957_18958

def missing18958_18959 : List (BitVec (edgeCount 12)) :=
  [missing18958]
abbrev records18958_18959 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18958]
theorem aligned18958_18959 :
    AlignedValid 12 4 missing18958_18959 records18958_18959 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18958
    maskCheck18958 AlignedValid.nil

def missing18959_18960 : List (BitVec (edgeCount 12)) :=
  [missing18959]
abbrev records18959_18960 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18959]
theorem aligned18959_18960 :
    AlignedValid 12 4 missing18959_18960 records18959_18960 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18959
    maskCheck18959 AlignedValid.nil

def missing18958_18960 : List (BitVec (edgeCount 12)) :=
  missing18958_18959 ++ missing18959_18960
abbrev records18958_18960 : List Blob :=
  records18958_18959 ++ records18959_18960
theorem aligned18958_18960 :
    AlignedValid 12 4 missing18958_18960 records18958_18960 :=
  aligned18958_18959.append aligned18959_18960

def missing18956_18960 : List (BitVec (edgeCount 12)) :=
  missing18956_18958 ++ missing18958_18960
abbrev records18956_18960 : List Blob :=
  records18956_18958 ++ records18958_18960
theorem aligned18956_18960 :
    AlignedValid 12 4 missing18956_18960 records18956_18960 :=
  aligned18956_18958.append aligned18958_18960

def missing18952_18960 : List (BitVec (edgeCount 12)) :=
  missing18952_18956 ++ missing18956_18960
abbrev records18952_18960 : List Blob :=
  records18952_18956 ++ records18956_18960
theorem aligned18952_18960 :
    AlignedValid 12 4 missing18952_18960 records18952_18960 :=
  aligned18952_18956.append aligned18956_18960

def missing18944_18960 : List (BitVec (edgeCount 12)) :=
  missing18944_18952 ++ missing18952_18960
abbrev records18944_18960 : List Blob :=
  records18944_18952 ++ records18952_18960
theorem aligned18944_18960 :
    AlignedValid 12 4 missing18944_18960 records18944_18960 :=
  aligned18944_18952.append aligned18952_18960

def missing18960_18961 : List (BitVec (edgeCount 12)) :=
  [missing18960]
abbrev records18960_18961 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18960]
theorem aligned18960_18961 :
    AlignedValid 12 4 missing18960_18961 records18960_18961 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18960
    maskCheck18960 AlignedValid.nil

def missing18961_18962 : List (BitVec (edgeCount 12)) :=
  [missing18961]
abbrev records18961_18962 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18961]
theorem aligned18961_18962 :
    AlignedValid 12 4 missing18961_18962 records18961_18962 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18961
    maskCheck18961 AlignedValid.nil

def missing18960_18962 : List (BitVec (edgeCount 12)) :=
  missing18960_18961 ++ missing18961_18962
abbrev records18960_18962 : List Blob :=
  records18960_18961 ++ records18961_18962
theorem aligned18960_18962 :
    AlignedValid 12 4 missing18960_18962 records18960_18962 :=
  aligned18960_18961.append aligned18961_18962

def missing18962_18963 : List (BitVec (edgeCount 12)) :=
  [missing18962]
abbrev records18962_18963 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18962]
theorem aligned18962_18963 :
    AlignedValid 12 4 missing18962_18963 records18962_18963 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18962
    maskCheck18962 AlignedValid.nil

def missing18963_18964 : List (BitVec (edgeCount 12)) :=
  [missing18963]
abbrev records18963_18964 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18963]
theorem aligned18963_18964 :
    AlignedValid 12 4 missing18963_18964 records18963_18964 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18963
    maskCheck18963 AlignedValid.nil

def missing18962_18964 : List (BitVec (edgeCount 12)) :=
  missing18962_18963 ++ missing18963_18964
abbrev records18962_18964 : List Blob :=
  records18962_18963 ++ records18963_18964
theorem aligned18962_18964 :
    AlignedValid 12 4 missing18962_18964 records18962_18964 :=
  aligned18962_18963.append aligned18963_18964

def missing18960_18964 : List (BitVec (edgeCount 12)) :=
  missing18960_18962 ++ missing18962_18964
abbrev records18960_18964 : List Blob :=
  records18960_18962 ++ records18962_18964
theorem aligned18960_18964 :
    AlignedValid 12 4 missing18960_18964 records18960_18964 :=
  aligned18960_18962.append aligned18962_18964

def missing18964_18965 : List (BitVec (edgeCount 12)) :=
  [missing18964]
abbrev records18964_18965 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18964]
theorem aligned18964_18965 :
    AlignedValid 12 4 missing18964_18965 records18964_18965 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18964
    maskCheck18964 AlignedValid.nil

def missing18965_18966 : List (BitVec (edgeCount 12)) :=
  [missing18965]
abbrev records18965_18966 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18965]
theorem aligned18965_18966 :
    AlignedValid 12 4 missing18965_18966 records18965_18966 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18965
    maskCheck18965 AlignedValid.nil

def missing18964_18966 : List (BitVec (edgeCount 12)) :=
  missing18964_18965 ++ missing18965_18966
abbrev records18964_18966 : List Blob :=
  records18964_18965 ++ records18965_18966
theorem aligned18964_18966 :
    AlignedValid 12 4 missing18964_18966 records18964_18966 :=
  aligned18964_18965.append aligned18965_18966

def missing18966_18967 : List (BitVec (edgeCount 12)) :=
  [missing18966]
abbrev records18966_18967 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18966]
theorem aligned18966_18967 :
    AlignedValid 12 4 missing18966_18967 records18966_18967 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18966
    maskCheck18966 AlignedValid.nil

def missing18967_18968 : List (BitVec (edgeCount 12)) :=
  [missing18967]
abbrev records18967_18968 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18967]
theorem aligned18967_18968 :
    AlignedValid 12 4 missing18967_18968 records18967_18968 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18967
    maskCheck18967 AlignedValid.nil

def missing18966_18968 : List (BitVec (edgeCount 12)) :=
  missing18966_18967 ++ missing18967_18968
abbrev records18966_18968 : List Blob :=
  records18966_18967 ++ records18967_18968
theorem aligned18966_18968 :
    AlignedValid 12 4 missing18966_18968 records18966_18968 :=
  aligned18966_18967.append aligned18967_18968

def missing18964_18968 : List (BitVec (edgeCount 12)) :=
  missing18964_18966 ++ missing18966_18968
abbrev records18964_18968 : List Blob :=
  records18964_18966 ++ records18966_18968
theorem aligned18964_18968 :
    AlignedValid 12 4 missing18964_18968 records18964_18968 :=
  aligned18964_18966.append aligned18966_18968

def missing18960_18968 : List (BitVec (edgeCount 12)) :=
  missing18960_18964 ++ missing18964_18968
abbrev records18960_18968 : List Blob :=
  records18960_18964 ++ records18964_18968
theorem aligned18960_18968 :
    AlignedValid 12 4 missing18960_18968 records18960_18968 :=
  aligned18960_18964.append aligned18964_18968

def missing18968_18969 : List (BitVec (edgeCount 12)) :=
  [missing18968]
abbrev records18968_18969 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18968]
theorem aligned18968_18969 :
    AlignedValid 12 4 missing18968_18969 records18968_18969 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18968
    maskCheck18968 AlignedValid.nil

def missing18969_18970 : List (BitVec (edgeCount 12)) :=
  [missing18969]
abbrev records18969_18970 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18969]
theorem aligned18969_18970 :
    AlignedValid 12 4 missing18969_18970 records18969_18970 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18969
    maskCheck18969 AlignedValid.nil

def missing18968_18970 : List (BitVec (edgeCount 12)) :=
  missing18968_18969 ++ missing18969_18970
abbrev records18968_18970 : List Blob :=
  records18968_18969 ++ records18969_18970
theorem aligned18968_18970 :
    AlignedValid 12 4 missing18968_18970 records18968_18970 :=
  aligned18968_18969.append aligned18969_18970

def missing18970_18971 : List (BitVec (edgeCount 12)) :=
  [missing18970]
abbrev records18970_18971 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18970]
theorem aligned18970_18971 :
    AlignedValid 12 4 missing18970_18971 records18970_18971 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18970
    maskCheck18970 AlignedValid.nil

def missing18971_18972 : List (BitVec (edgeCount 12)) :=
  [missing18971]
abbrev records18971_18972 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18971]
theorem aligned18971_18972 :
    AlignedValid 12 4 missing18971_18972 records18971_18972 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18971
    maskCheck18971 AlignedValid.nil

def missing18970_18972 : List (BitVec (edgeCount 12)) :=
  missing18970_18971 ++ missing18971_18972
abbrev records18970_18972 : List Blob :=
  records18970_18971 ++ records18971_18972
theorem aligned18970_18972 :
    AlignedValid 12 4 missing18970_18972 records18970_18972 :=
  aligned18970_18971.append aligned18971_18972

def missing18968_18972 : List (BitVec (edgeCount 12)) :=
  missing18968_18970 ++ missing18970_18972
abbrev records18968_18972 : List Blob :=
  records18968_18970 ++ records18970_18972
theorem aligned18968_18972 :
    AlignedValid 12 4 missing18968_18972 records18968_18972 :=
  aligned18968_18970.append aligned18970_18972

def missing18972_18973 : List (BitVec (edgeCount 12)) :=
  [missing18972]
abbrev records18972_18973 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18972]
theorem aligned18972_18973 :
    AlignedValid 12 4 missing18972_18973 records18972_18973 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18972
    maskCheck18972 AlignedValid.nil

def missing18973_18974 : List (BitVec (edgeCount 12)) :=
  [missing18973]
abbrev records18973_18974 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18973]
theorem aligned18973_18974 :
    AlignedValid 12 4 missing18973_18974 records18973_18974 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18973
    maskCheck18973 AlignedValid.nil

def missing18972_18974 : List (BitVec (edgeCount 12)) :=
  missing18972_18973 ++ missing18973_18974
abbrev records18972_18974 : List Blob :=
  records18972_18973 ++ records18973_18974
theorem aligned18972_18974 :
    AlignedValid 12 4 missing18972_18974 records18972_18974 :=
  aligned18972_18973.append aligned18973_18974

def missing18974_18975 : List (BitVec (edgeCount 12)) :=
  [missing18974]
abbrev records18974_18975 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18974]
theorem aligned18974_18975 :
    AlignedValid 12 4 missing18974_18975 records18974_18975 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18974
    maskCheck18974 AlignedValid.nil

def missing18975_18976 : List (BitVec (edgeCount 12)) :=
  [missing18975]
abbrev records18975_18976 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18975]
theorem aligned18975_18976 :
    AlignedValid 12 4 missing18975_18976 records18975_18976 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18975
    maskCheck18975 AlignedValid.nil

def missing18974_18976 : List (BitVec (edgeCount 12)) :=
  missing18974_18975 ++ missing18975_18976
abbrev records18974_18976 : List Blob :=
  records18974_18975 ++ records18975_18976
theorem aligned18974_18976 :
    AlignedValid 12 4 missing18974_18976 records18974_18976 :=
  aligned18974_18975.append aligned18975_18976

def missing18972_18976 : List (BitVec (edgeCount 12)) :=
  missing18972_18974 ++ missing18974_18976
abbrev records18972_18976 : List Blob :=
  records18972_18974 ++ records18974_18976
theorem aligned18972_18976 :
    AlignedValid 12 4 missing18972_18976 records18972_18976 :=
  aligned18972_18974.append aligned18974_18976

def missing18968_18976 : List (BitVec (edgeCount 12)) :=
  missing18968_18972 ++ missing18972_18976
abbrev records18968_18976 : List Blob :=
  records18968_18972 ++ records18972_18976
theorem aligned18968_18976 :
    AlignedValid 12 4 missing18968_18976 records18968_18976 :=
  aligned18968_18972.append aligned18972_18976

def missing18960_18976 : List (BitVec (edgeCount 12)) :=
  missing18960_18968 ++ missing18968_18976
abbrev records18960_18976 : List Blob :=
  records18960_18968 ++ records18968_18976
theorem aligned18960_18976 :
    AlignedValid 12 4 missing18960_18976 records18960_18976 :=
  aligned18960_18968.append aligned18968_18976

def missing18944_18976 : List (BitVec (edgeCount 12)) :=
  missing18944_18960 ++ missing18960_18976
abbrev records18944_18976 : List Blob :=
  records18944_18960 ++ records18960_18976
theorem aligned18944_18976 :
    AlignedValid 12 4 missing18944_18976 records18944_18976 :=
  aligned18944_18960.append aligned18960_18976

def missing18976_18977 : List (BitVec (edgeCount 12)) :=
  [missing18976]
abbrev records18976_18977 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18976]
theorem aligned18976_18977 :
    AlignedValid 12 4 missing18976_18977 records18976_18977 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18976
    maskCheck18976 AlignedValid.nil

def missing18977_18978 : List (BitVec (edgeCount 12)) :=
  [missing18977]
abbrev records18977_18978 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18977]
theorem aligned18977_18978 :
    AlignedValid 12 4 missing18977_18978 records18977_18978 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18977
    maskCheck18977 AlignedValid.nil

def missing18976_18978 : List (BitVec (edgeCount 12)) :=
  missing18976_18977 ++ missing18977_18978
abbrev records18976_18978 : List Blob :=
  records18976_18977 ++ records18977_18978
theorem aligned18976_18978 :
    AlignedValid 12 4 missing18976_18978 records18976_18978 :=
  aligned18976_18977.append aligned18977_18978

def missing18978_18979 : List (BitVec (edgeCount 12)) :=
  [missing18978]
abbrev records18978_18979 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18978]
theorem aligned18978_18979 :
    AlignedValid 12 4 missing18978_18979 records18978_18979 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18978
    maskCheck18978 AlignedValid.nil

def missing18979_18980 : List (BitVec (edgeCount 12)) :=
  [missing18979]
abbrev records18979_18980 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18979]
theorem aligned18979_18980 :
    AlignedValid 12 4 missing18979_18980 records18979_18980 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18979
    maskCheck18979 AlignedValid.nil

def missing18978_18980 : List (BitVec (edgeCount 12)) :=
  missing18978_18979 ++ missing18979_18980
abbrev records18978_18980 : List Blob :=
  records18978_18979 ++ records18979_18980
theorem aligned18978_18980 :
    AlignedValid 12 4 missing18978_18980 records18978_18980 :=
  aligned18978_18979.append aligned18979_18980

def missing18976_18980 : List (BitVec (edgeCount 12)) :=
  missing18976_18978 ++ missing18978_18980
abbrev records18976_18980 : List Blob :=
  records18976_18978 ++ records18978_18980
theorem aligned18976_18980 :
    AlignedValid 12 4 missing18976_18980 records18976_18980 :=
  aligned18976_18978.append aligned18978_18980

def missing18980_18981 : List (BitVec (edgeCount 12)) :=
  [missing18980]
abbrev records18980_18981 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18980]
theorem aligned18980_18981 :
    AlignedValid 12 4 missing18980_18981 records18980_18981 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18980
    maskCheck18980 AlignedValid.nil

def missing18981_18982 : List (BitVec (edgeCount 12)) :=
  [missing18981]
abbrev records18981_18982 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18981]
theorem aligned18981_18982 :
    AlignedValid 12 4 missing18981_18982 records18981_18982 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18981
    maskCheck18981 AlignedValid.nil

def missing18980_18982 : List (BitVec (edgeCount 12)) :=
  missing18980_18981 ++ missing18981_18982
abbrev records18980_18982 : List Blob :=
  records18980_18981 ++ records18981_18982
theorem aligned18980_18982 :
    AlignedValid 12 4 missing18980_18982 records18980_18982 :=
  aligned18980_18981.append aligned18981_18982

def missing18982_18983 : List (BitVec (edgeCount 12)) :=
  [missing18982]
abbrev records18982_18983 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18982]
theorem aligned18982_18983 :
    AlignedValid 12 4 missing18982_18983 records18982_18983 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18982
    maskCheck18982 AlignedValid.nil

def missing18983_18984 : List (BitVec (edgeCount 12)) :=
  [missing18983]
abbrev records18983_18984 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18983]
theorem aligned18983_18984 :
    AlignedValid 12 4 missing18983_18984 records18983_18984 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18983
    maskCheck18983 AlignedValid.nil

def missing18982_18984 : List (BitVec (edgeCount 12)) :=
  missing18982_18983 ++ missing18983_18984
abbrev records18982_18984 : List Blob :=
  records18982_18983 ++ records18983_18984
theorem aligned18982_18984 :
    AlignedValid 12 4 missing18982_18984 records18982_18984 :=
  aligned18982_18983.append aligned18983_18984

def missing18980_18984 : List (BitVec (edgeCount 12)) :=
  missing18980_18982 ++ missing18982_18984
abbrev records18980_18984 : List Blob :=
  records18980_18982 ++ records18982_18984
theorem aligned18980_18984 :
    AlignedValid 12 4 missing18980_18984 records18980_18984 :=
  aligned18980_18982.append aligned18982_18984

def missing18976_18984 : List (BitVec (edgeCount 12)) :=
  missing18976_18980 ++ missing18980_18984
abbrev records18976_18984 : List Blob :=
  records18976_18980 ++ records18980_18984
theorem aligned18976_18984 :
    AlignedValid 12 4 missing18976_18984 records18976_18984 :=
  aligned18976_18980.append aligned18980_18984

def missing18984_18985 : List (BitVec (edgeCount 12)) :=
  [missing18984]
abbrev records18984_18985 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18984]
theorem aligned18984_18985 :
    AlignedValid 12 4 missing18984_18985 records18984_18985 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18984
    maskCheck18984 AlignedValid.nil

def missing18985_18986 : List (BitVec (edgeCount 12)) :=
  [missing18985]
abbrev records18985_18986 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18985]
theorem aligned18985_18986 :
    AlignedValid 12 4 missing18985_18986 records18985_18986 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18985
    maskCheck18985 AlignedValid.nil

def missing18984_18986 : List (BitVec (edgeCount 12)) :=
  missing18984_18985 ++ missing18985_18986
abbrev records18984_18986 : List Blob :=
  records18984_18985 ++ records18985_18986
theorem aligned18984_18986 :
    AlignedValid 12 4 missing18984_18986 records18984_18986 :=
  aligned18984_18985.append aligned18985_18986

def missing18986_18987 : List (BitVec (edgeCount 12)) :=
  [missing18986]
abbrev records18986_18987 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18986]
theorem aligned18986_18987 :
    AlignedValid 12 4 missing18986_18987 records18986_18987 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18986
    maskCheck18986 AlignedValid.nil

def missing18987_18988 : List (BitVec (edgeCount 12)) :=
  [missing18987]
abbrev records18987_18988 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18987]
theorem aligned18987_18988 :
    AlignedValid 12 4 missing18987_18988 records18987_18988 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18987
    maskCheck18987 AlignedValid.nil

def missing18986_18988 : List (BitVec (edgeCount 12)) :=
  missing18986_18987 ++ missing18987_18988
abbrev records18986_18988 : List Blob :=
  records18986_18987 ++ records18987_18988
theorem aligned18986_18988 :
    AlignedValid 12 4 missing18986_18988 records18986_18988 :=
  aligned18986_18987.append aligned18987_18988

def missing18984_18988 : List (BitVec (edgeCount 12)) :=
  missing18984_18986 ++ missing18986_18988
abbrev records18984_18988 : List Blob :=
  records18984_18986 ++ records18986_18988
theorem aligned18984_18988 :
    AlignedValid 12 4 missing18984_18988 records18984_18988 :=
  aligned18984_18986.append aligned18986_18988

def missing18988_18989 : List (BitVec (edgeCount 12)) :=
  [missing18988]
abbrev records18988_18989 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18988]
theorem aligned18988_18989 :
    AlignedValid 12 4 missing18988_18989 records18988_18989 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18988
    maskCheck18988 AlignedValid.nil

def missing18989_18990 : List (BitVec (edgeCount 12)) :=
  [missing18989]
abbrev records18989_18990 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18989]
theorem aligned18989_18990 :
    AlignedValid 12 4 missing18989_18990 records18989_18990 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18989
    maskCheck18989 AlignedValid.nil

def missing18988_18990 : List (BitVec (edgeCount 12)) :=
  missing18988_18989 ++ missing18989_18990
abbrev records18988_18990 : List Blob :=
  records18988_18989 ++ records18989_18990
theorem aligned18988_18990 :
    AlignedValid 12 4 missing18988_18990 records18988_18990 :=
  aligned18988_18989.append aligned18989_18990

def missing18990_18991 : List (BitVec (edgeCount 12)) :=
  [missing18990]
abbrev records18990_18991 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18990]
theorem aligned18990_18991 :
    AlignedValid 12 4 missing18990_18991 records18990_18991 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18990
    maskCheck18990 AlignedValid.nil

def missing18991_18992 : List (BitVec (edgeCount 12)) :=
  [missing18991]
abbrev records18991_18992 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18991]
theorem aligned18991_18992 :
    AlignedValid 12 4 missing18991_18992 records18991_18992 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18991
    maskCheck18991 AlignedValid.nil

def missing18990_18992 : List (BitVec (edgeCount 12)) :=
  missing18990_18991 ++ missing18991_18992
abbrev records18990_18992 : List Blob :=
  records18990_18991 ++ records18991_18992
theorem aligned18990_18992 :
    AlignedValid 12 4 missing18990_18992 records18990_18992 :=
  aligned18990_18991.append aligned18991_18992

def missing18988_18992 : List (BitVec (edgeCount 12)) :=
  missing18988_18990 ++ missing18990_18992
abbrev records18988_18992 : List Blob :=
  records18988_18990 ++ records18990_18992
theorem aligned18988_18992 :
    AlignedValid 12 4 missing18988_18992 records18988_18992 :=
  aligned18988_18990.append aligned18990_18992

def missing18984_18992 : List (BitVec (edgeCount 12)) :=
  missing18984_18988 ++ missing18988_18992
abbrev records18984_18992 : List Blob :=
  records18984_18988 ++ records18988_18992
theorem aligned18984_18992 :
    AlignedValid 12 4 missing18984_18992 records18984_18992 :=
  aligned18984_18988.append aligned18988_18992

def missing18976_18992 : List (BitVec (edgeCount 12)) :=
  missing18976_18984 ++ missing18984_18992
abbrev records18976_18992 : List Blob :=
  records18976_18984 ++ records18984_18992
theorem aligned18976_18992 :
    AlignedValid 12 4 missing18976_18992 records18976_18992 :=
  aligned18976_18984.append aligned18984_18992

def missing18992_18993 : List (BitVec (edgeCount 12)) :=
  [missing18992]
abbrev records18992_18993 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18992]
theorem aligned18992_18993 :
    AlignedValid 12 4 missing18992_18993 records18992_18993 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18992
    maskCheck18992 AlignedValid.nil

def missing18993_18994 : List (BitVec (edgeCount 12)) :=
  [missing18993]
abbrev records18993_18994 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18993]
theorem aligned18993_18994 :
    AlignedValid 12 4 missing18993_18994 records18993_18994 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18993
    maskCheck18993 AlignedValid.nil

def missing18992_18994 : List (BitVec (edgeCount 12)) :=
  missing18992_18993 ++ missing18993_18994
abbrev records18992_18994 : List Blob :=
  records18992_18993 ++ records18993_18994
theorem aligned18992_18994 :
    AlignedValid 12 4 missing18992_18994 records18992_18994 :=
  aligned18992_18993.append aligned18993_18994

def missing18994_18995 : List (BitVec (edgeCount 12)) :=
  [missing18994]
abbrev records18994_18995 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18994]
theorem aligned18994_18995 :
    AlignedValid 12 4 missing18994_18995 records18994_18995 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18994
    maskCheck18994 AlignedValid.nil

def missing18995_18996 : List (BitVec (edgeCount 12)) :=
  [missing18995]
abbrev records18995_18996 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18995]
theorem aligned18995_18996 :
    AlignedValid 12 4 missing18995_18996 records18995_18996 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18995
    maskCheck18995 AlignedValid.nil

def missing18994_18996 : List (BitVec (edgeCount 12)) :=
  missing18994_18995 ++ missing18995_18996
abbrev records18994_18996 : List Blob :=
  records18994_18995 ++ records18995_18996
theorem aligned18994_18996 :
    AlignedValid 12 4 missing18994_18996 records18994_18996 :=
  aligned18994_18995.append aligned18995_18996

def missing18992_18996 : List (BitVec (edgeCount 12)) :=
  missing18992_18994 ++ missing18994_18996
abbrev records18992_18996 : List Blob :=
  records18992_18994 ++ records18994_18996
theorem aligned18992_18996 :
    AlignedValid 12 4 missing18992_18996 records18992_18996 :=
  aligned18992_18994.append aligned18994_18996

def missing18996_18997 : List (BitVec (edgeCount 12)) :=
  [missing18996]
abbrev records18996_18997 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18996]
theorem aligned18996_18997 :
    AlignedValid 12 4 missing18996_18997 records18996_18997 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18996
    maskCheck18996 AlignedValid.nil

def missing18997_18998 : List (BitVec (edgeCount 12)) :=
  [missing18997]
abbrev records18997_18998 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18997]
theorem aligned18997_18998 :
    AlignedValid 12 4 missing18997_18998 records18997_18998 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18997
    maskCheck18997 AlignedValid.nil

def missing18996_18998 : List (BitVec (edgeCount 12)) :=
  missing18996_18997 ++ missing18997_18998
abbrev records18996_18998 : List Blob :=
  records18996_18997 ++ records18997_18998
theorem aligned18996_18998 :
    AlignedValid 12 4 missing18996_18998 records18996_18998 :=
  aligned18996_18997.append aligned18997_18998

def missing18998_18999 : List (BitVec (edgeCount 12)) :=
  [missing18998]
abbrev records18998_18999 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18998]
theorem aligned18998_18999 :
    AlignedValid 12 4 missing18998_18999 records18998_18999 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18998
    maskCheck18998 AlignedValid.nil

def missing18999_19000 : List (BitVec (edgeCount 12)) :=
  [missing18999]
abbrev records18999_19000 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record18999]
theorem aligned18999_19000 :
    AlignedValid 12 4 missing18999_19000 records18999_19000 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check18999
    maskCheck18999 AlignedValid.nil

def missing18998_19000 : List (BitVec (edgeCount 12)) :=
  missing18998_18999 ++ missing18999_19000
abbrev records18998_19000 : List Blob :=
  records18998_18999 ++ records18999_19000
theorem aligned18998_19000 :
    AlignedValid 12 4 missing18998_19000 records18998_19000 :=
  aligned18998_18999.append aligned18999_19000

def missing18996_19000 : List (BitVec (edgeCount 12)) :=
  missing18996_18998 ++ missing18998_19000
abbrev records18996_19000 : List Blob :=
  records18996_18998 ++ records18998_19000
theorem aligned18996_19000 :
    AlignedValid 12 4 missing18996_19000 records18996_19000 :=
  aligned18996_18998.append aligned18998_19000

def missing18992_19000 : List (BitVec (edgeCount 12)) :=
  missing18992_18996 ++ missing18996_19000
abbrev records18992_19000 : List Blob :=
  records18992_18996 ++ records18996_19000
theorem aligned18992_19000 :
    AlignedValid 12 4 missing18992_19000 records18992_19000 :=
  aligned18992_18996.append aligned18996_19000

def missing19000_19001 : List (BitVec (edgeCount 12)) :=
  [missing19000]
abbrev records19000_19001 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19000]
theorem aligned19000_19001 :
    AlignedValid 12 4 missing19000_19001 records19000_19001 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19000
    maskCheck19000 AlignedValid.nil

def missing19001_19002 : List (BitVec (edgeCount 12)) :=
  [missing19001]
abbrev records19001_19002 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19001]
theorem aligned19001_19002 :
    AlignedValid 12 4 missing19001_19002 records19001_19002 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19001
    maskCheck19001 AlignedValid.nil

def missing19000_19002 : List (BitVec (edgeCount 12)) :=
  missing19000_19001 ++ missing19001_19002
abbrev records19000_19002 : List Blob :=
  records19000_19001 ++ records19001_19002
theorem aligned19000_19002 :
    AlignedValid 12 4 missing19000_19002 records19000_19002 :=
  aligned19000_19001.append aligned19001_19002

def missing19002_19003 : List (BitVec (edgeCount 12)) :=
  [missing19002]
abbrev records19002_19003 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19002]
theorem aligned19002_19003 :
    AlignedValid 12 4 missing19002_19003 records19002_19003 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19002
    maskCheck19002 AlignedValid.nil

def missing19003_19004 : List (BitVec (edgeCount 12)) :=
  [missing19003]
abbrev records19003_19004 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19003]
theorem aligned19003_19004 :
    AlignedValid 12 4 missing19003_19004 records19003_19004 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19003
    maskCheck19003 AlignedValid.nil

def missing19002_19004 : List (BitVec (edgeCount 12)) :=
  missing19002_19003 ++ missing19003_19004
abbrev records19002_19004 : List Blob :=
  records19002_19003 ++ records19003_19004
theorem aligned19002_19004 :
    AlignedValid 12 4 missing19002_19004 records19002_19004 :=
  aligned19002_19003.append aligned19003_19004

def missing19000_19004 : List (BitVec (edgeCount 12)) :=
  missing19000_19002 ++ missing19002_19004
abbrev records19000_19004 : List Blob :=
  records19000_19002 ++ records19002_19004
theorem aligned19000_19004 :
    AlignedValid 12 4 missing19000_19004 records19000_19004 :=
  aligned19000_19002.append aligned19002_19004

def missing19004_19005 : List (BitVec (edgeCount 12)) :=
  [missing19004]
abbrev records19004_19005 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19004]
theorem aligned19004_19005 :
    AlignedValid 12 4 missing19004_19005 records19004_19005 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19004
    maskCheck19004 AlignedValid.nil

def missing19005_19006 : List (BitVec (edgeCount 12)) :=
  [missing19005]
abbrev records19005_19006 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19005]
theorem aligned19005_19006 :
    AlignedValid 12 4 missing19005_19006 records19005_19006 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19005
    maskCheck19005 AlignedValid.nil

def missing19004_19006 : List (BitVec (edgeCount 12)) :=
  missing19004_19005 ++ missing19005_19006
abbrev records19004_19006 : List Blob :=
  records19004_19005 ++ records19005_19006
theorem aligned19004_19006 :
    AlignedValid 12 4 missing19004_19006 records19004_19006 :=
  aligned19004_19005.append aligned19005_19006

def missing19006_19007 : List (BitVec (edgeCount 12)) :=
  [missing19006]
abbrev records19006_19007 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19006]
theorem aligned19006_19007 :
    AlignedValid 12 4 missing19006_19007 records19006_19007 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19006
    maskCheck19006 AlignedValid.nil

def missing19007_19008 : List (BitVec (edgeCount 12)) :=
  [missing19007]
abbrev records19007_19008 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19007]
theorem aligned19007_19008 :
    AlignedValid 12 4 missing19007_19008 records19007_19008 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19007
    maskCheck19007 AlignedValid.nil

def missing19006_19008 : List (BitVec (edgeCount 12)) :=
  missing19006_19007 ++ missing19007_19008
abbrev records19006_19008 : List Blob :=
  records19006_19007 ++ records19007_19008
theorem aligned19006_19008 :
    AlignedValid 12 4 missing19006_19008 records19006_19008 :=
  aligned19006_19007.append aligned19007_19008

def missing19004_19008 : List (BitVec (edgeCount 12)) :=
  missing19004_19006 ++ missing19006_19008
abbrev records19004_19008 : List Blob :=
  records19004_19006 ++ records19006_19008
theorem aligned19004_19008 :
    AlignedValid 12 4 missing19004_19008 records19004_19008 :=
  aligned19004_19006.append aligned19006_19008

def missing19000_19008 : List (BitVec (edgeCount 12)) :=
  missing19000_19004 ++ missing19004_19008
abbrev records19000_19008 : List Blob :=
  records19000_19004 ++ records19004_19008
theorem aligned19000_19008 :
    AlignedValid 12 4 missing19000_19008 records19000_19008 :=
  aligned19000_19004.append aligned19004_19008

def missing18992_19008 : List (BitVec (edgeCount 12)) :=
  missing18992_19000 ++ missing19000_19008
abbrev records18992_19008 : List Blob :=
  records18992_19000 ++ records19000_19008
theorem aligned18992_19008 :
    AlignedValid 12 4 missing18992_19008 records18992_19008 :=
  aligned18992_19000.append aligned19000_19008

def missing18976_19008 : List (BitVec (edgeCount 12)) :=
  missing18976_18992 ++ missing18992_19008
abbrev records18976_19008 : List Blob :=
  records18976_18992 ++ records18992_19008
theorem aligned18976_19008 :
    AlignedValid 12 4 missing18976_19008 records18976_19008 :=
  aligned18976_18992.append aligned18992_19008

def missing18944_19008 : List (BitVec (edgeCount 12)) :=
  missing18944_18976 ++ missing18976_19008
abbrev records18944_19008 : List Blob :=
  records18944_18976 ++ records18976_19008
theorem aligned18944_19008 :
    AlignedValid 12 4 missing18944_19008 records18944_19008 :=
  aligned18944_18976.append aligned18976_19008

def missing19008_19009 : List (BitVec (edgeCount 12)) :=
  [missing19008]
abbrev records19008_19009 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19008]
theorem aligned19008_19009 :
    AlignedValid 12 4 missing19008_19009 records19008_19009 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19008
    maskCheck19008 AlignedValid.nil

def missing19009_19010 : List (BitVec (edgeCount 12)) :=
  [missing19009]
abbrev records19009_19010 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19009]
theorem aligned19009_19010 :
    AlignedValid 12 4 missing19009_19010 records19009_19010 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19009
    maskCheck19009 AlignedValid.nil

def missing19008_19010 : List (BitVec (edgeCount 12)) :=
  missing19008_19009 ++ missing19009_19010
abbrev records19008_19010 : List Blob :=
  records19008_19009 ++ records19009_19010
theorem aligned19008_19010 :
    AlignedValid 12 4 missing19008_19010 records19008_19010 :=
  aligned19008_19009.append aligned19009_19010

def missing19010_19011 : List (BitVec (edgeCount 12)) :=
  [missing19010]
abbrev records19010_19011 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19010]
theorem aligned19010_19011 :
    AlignedValid 12 4 missing19010_19011 records19010_19011 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19010
    maskCheck19010 AlignedValid.nil

def missing19011_19012 : List (BitVec (edgeCount 12)) :=
  [missing19011]
abbrev records19011_19012 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19011]
theorem aligned19011_19012 :
    AlignedValid 12 4 missing19011_19012 records19011_19012 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19011
    maskCheck19011 AlignedValid.nil

def missing19010_19012 : List (BitVec (edgeCount 12)) :=
  missing19010_19011 ++ missing19011_19012
abbrev records19010_19012 : List Blob :=
  records19010_19011 ++ records19011_19012
theorem aligned19010_19012 :
    AlignedValid 12 4 missing19010_19012 records19010_19012 :=
  aligned19010_19011.append aligned19011_19012

def missing19008_19012 : List (BitVec (edgeCount 12)) :=
  missing19008_19010 ++ missing19010_19012
abbrev records19008_19012 : List Blob :=
  records19008_19010 ++ records19010_19012
theorem aligned19008_19012 :
    AlignedValid 12 4 missing19008_19012 records19008_19012 :=
  aligned19008_19010.append aligned19010_19012

def missing19012_19013 : List (BitVec (edgeCount 12)) :=
  [missing19012]
abbrev records19012_19013 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19012]
theorem aligned19012_19013 :
    AlignedValid 12 4 missing19012_19013 records19012_19013 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19012
    maskCheck19012 AlignedValid.nil

def missing19013_19014 : List (BitVec (edgeCount 12)) :=
  [missing19013]
abbrev records19013_19014 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19013]
theorem aligned19013_19014 :
    AlignedValid 12 4 missing19013_19014 records19013_19014 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19013
    maskCheck19013 AlignedValid.nil

def missing19012_19014 : List (BitVec (edgeCount 12)) :=
  missing19012_19013 ++ missing19013_19014
abbrev records19012_19014 : List Blob :=
  records19012_19013 ++ records19013_19014
theorem aligned19012_19014 :
    AlignedValid 12 4 missing19012_19014 records19012_19014 :=
  aligned19012_19013.append aligned19013_19014

def missing19014_19015 : List (BitVec (edgeCount 12)) :=
  [missing19014]
abbrev records19014_19015 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19014]
theorem aligned19014_19015 :
    AlignedValid 12 4 missing19014_19015 records19014_19015 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19014
    maskCheck19014 AlignedValid.nil

def missing19015_19016 : List (BitVec (edgeCount 12)) :=
  [missing19015]
abbrev records19015_19016 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19015]
theorem aligned19015_19016 :
    AlignedValid 12 4 missing19015_19016 records19015_19016 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19015
    maskCheck19015 AlignedValid.nil

def missing19014_19016 : List (BitVec (edgeCount 12)) :=
  missing19014_19015 ++ missing19015_19016
abbrev records19014_19016 : List Blob :=
  records19014_19015 ++ records19015_19016
theorem aligned19014_19016 :
    AlignedValid 12 4 missing19014_19016 records19014_19016 :=
  aligned19014_19015.append aligned19015_19016

def missing19012_19016 : List (BitVec (edgeCount 12)) :=
  missing19012_19014 ++ missing19014_19016
abbrev records19012_19016 : List Blob :=
  records19012_19014 ++ records19014_19016
theorem aligned19012_19016 :
    AlignedValid 12 4 missing19012_19016 records19012_19016 :=
  aligned19012_19014.append aligned19014_19016

def missing19008_19016 : List (BitVec (edgeCount 12)) :=
  missing19008_19012 ++ missing19012_19016
abbrev records19008_19016 : List Blob :=
  records19008_19012 ++ records19012_19016
theorem aligned19008_19016 :
    AlignedValid 12 4 missing19008_19016 records19008_19016 :=
  aligned19008_19012.append aligned19012_19016

def missing19016_19017 : List (BitVec (edgeCount 12)) :=
  [missing19016]
abbrev records19016_19017 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19016]
theorem aligned19016_19017 :
    AlignedValid 12 4 missing19016_19017 records19016_19017 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19016
    maskCheck19016 AlignedValid.nil

def missing19017_19018 : List (BitVec (edgeCount 12)) :=
  [missing19017]
abbrev records19017_19018 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19017]
theorem aligned19017_19018 :
    AlignedValid 12 4 missing19017_19018 records19017_19018 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19017
    maskCheck19017 AlignedValid.nil

def missing19016_19018 : List (BitVec (edgeCount 12)) :=
  missing19016_19017 ++ missing19017_19018
abbrev records19016_19018 : List Blob :=
  records19016_19017 ++ records19017_19018
theorem aligned19016_19018 :
    AlignedValid 12 4 missing19016_19018 records19016_19018 :=
  aligned19016_19017.append aligned19017_19018

def missing19018_19019 : List (BitVec (edgeCount 12)) :=
  [missing19018]
abbrev records19018_19019 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19018]
theorem aligned19018_19019 :
    AlignedValid 12 4 missing19018_19019 records19018_19019 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19018
    maskCheck19018 AlignedValid.nil

def missing19019_19020 : List (BitVec (edgeCount 12)) :=
  [missing19019]
abbrev records19019_19020 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19019]
theorem aligned19019_19020 :
    AlignedValid 12 4 missing19019_19020 records19019_19020 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19019
    maskCheck19019 AlignedValid.nil

def missing19018_19020 : List (BitVec (edgeCount 12)) :=
  missing19018_19019 ++ missing19019_19020
abbrev records19018_19020 : List Blob :=
  records19018_19019 ++ records19019_19020
theorem aligned19018_19020 :
    AlignedValid 12 4 missing19018_19020 records19018_19020 :=
  aligned19018_19019.append aligned19019_19020

def missing19016_19020 : List (BitVec (edgeCount 12)) :=
  missing19016_19018 ++ missing19018_19020
abbrev records19016_19020 : List Blob :=
  records19016_19018 ++ records19018_19020
theorem aligned19016_19020 :
    AlignedValid 12 4 missing19016_19020 records19016_19020 :=
  aligned19016_19018.append aligned19018_19020

def missing19020_19021 : List (BitVec (edgeCount 12)) :=
  [missing19020]
abbrev records19020_19021 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19020]
theorem aligned19020_19021 :
    AlignedValid 12 4 missing19020_19021 records19020_19021 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19020
    maskCheck19020 AlignedValid.nil

def missing19021_19022 : List (BitVec (edgeCount 12)) :=
  [missing19021]
abbrev records19021_19022 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19021]
theorem aligned19021_19022 :
    AlignedValid 12 4 missing19021_19022 records19021_19022 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19021
    maskCheck19021 AlignedValid.nil

def missing19020_19022 : List (BitVec (edgeCount 12)) :=
  missing19020_19021 ++ missing19021_19022
abbrev records19020_19022 : List Blob :=
  records19020_19021 ++ records19021_19022
theorem aligned19020_19022 :
    AlignedValid 12 4 missing19020_19022 records19020_19022 :=
  aligned19020_19021.append aligned19021_19022

def missing19022_19023 : List (BitVec (edgeCount 12)) :=
  [missing19022]
abbrev records19022_19023 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19022]
theorem aligned19022_19023 :
    AlignedValid 12 4 missing19022_19023 records19022_19023 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19022
    maskCheck19022 AlignedValid.nil

def missing19023_19024 : List (BitVec (edgeCount 12)) :=
  [missing19023]
abbrev records19023_19024 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19023]
theorem aligned19023_19024 :
    AlignedValid 12 4 missing19023_19024 records19023_19024 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19023
    maskCheck19023 AlignedValid.nil

def missing19022_19024 : List (BitVec (edgeCount 12)) :=
  missing19022_19023 ++ missing19023_19024
abbrev records19022_19024 : List Blob :=
  records19022_19023 ++ records19023_19024
theorem aligned19022_19024 :
    AlignedValid 12 4 missing19022_19024 records19022_19024 :=
  aligned19022_19023.append aligned19023_19024

def missing19020_19024 : List (BitVec (edgeCount 12)) :=
  missing19020_19022 ++ missing19022_19024
abbrev records19020_19024 : List Blob :=
  records19020_19022 ++ records19022_19024
theorem aligned19020_19024 :
    AlignedValid 12 4 missing19020_19024 records19020_19024 :=
  aligned19020_19022.append aligned19022_19024

def missing19016_19024 : List (BitVec (edgeCount 12)) :=
  missing19016_19020 ++ missing19020_19024
abbrev records19016_19024 : List Blob :=
  records19016_19020 ++ records19020_19024
theorem aligned19016_19024 :
    AlignedValid 12 4 missing19016_19024 records19016_19024 :=
  aligned19016_19020.append aligned19020_19024

def missing19008_19024 : List (BitVec (edgeCount 12)) :=
  missing19008_19016 ++ missing19016_19024
abbrev records19008_19024 : List Blob :=
  records19008_19016 ++ records19016_19024
theorem aligned19008_19024 :
    AlignedValid 12 4 missing19008_19024 records19008_19024 :=
  aligned19008_19016.append aligned19016_19024

def missing19024_19025 : List (BitVec (edgeCount 12)) :=
  [missing19024]
abbrev records19024_19025 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19024]
theorem aligned19024_19025 :
    AlignedValid 12 4 missing19024_19025 records19024_19025 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19024
    maskCheck19024 AlignedValid.nil

def missing19025_19026 : List (BitVec (edgeCount 12)) :=
  [missing19025]
abbrev records19025_19026 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19025]
theorem aligned19025_19026 :
    AlignedValid 12 4 missing19025_19026 records19025_19026 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19025
    maskCheck19025 AlignedValid.nil

def missing19024_19026 : List (BitVec (edgeCount 12)) :=
  missing19024_19025 ++ missing19025_19026
abbrev records19024_19026 : List Blob :=
  records19024_19025 ++ records19025_19026
theorem aligned19024_19026 :
    AlignedValid 12 4 missing19024_19026 records19024_19026 :=
  aligned19024_19025.append aligned19025_19026

def missing19026_19027 : List (BitVec (edgeCount 12)) :=
  [missing19026]
abbrev records19026_19027 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19026]
theorem aligned19026_19027 :
    AlignedValid 12 4 missing19026_19027 records19026_19027 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19026
    maskCheck19026 AlignedValid.nil

def missing19027_19028 : List (BitVec (edgeCount 12)) :=
  [missing19027]
abbrev records19027_19028 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19027]
theorem aligned19027_19028 :
    AlignedValid 12 4 missing19027_19028 records19027_19028 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19027
    maskCheck19027 AlignedValid.nil

def missing19026_19028 : List (BitVec (edgeCount 12)) :=
  missing19026_19027 ++ missing19027_19028
abbrev records19026_19028 : List Blob :=
  records19026_19027 ++ records19027_19028
theorem aligned19026_19028 :
    AlignedValid 12 4 missing19026_19028 records19026_19028 :=
  aligned19026_19027.append aligned19027_19028

def missing19024_19028 : List (BitVec (edgeCount 12)) :=
  missing19024_19026 ++ missing19026_19028
abbrev records19024_19028 : List Blob :=
  records19024_19026 ++ records19026_19028
theorem aligned19024_19028 :
    AlignedValid 12 4 missing19024_19028 records19024_19028 :=
  aligned19024_19026.append aligned19026_19028

def missing19028_19029 : List (BitVec (edgeCount 12)) :=
  [missing19028]
abbrev records19028_19029 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19028]
theorem aligned19028_19029 :
    AlignedValid 12 4 missing19028_19029 records19028_19029 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19028
    maskCheck19028 AlignedValid.nil

def missing19029_19030 : List (BitVec (edgeCount 12)) :=
  [missing19029]
abbrev records19029_19030 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19029]
theorem aligned19029_19030 :
    AlignedValid 12 4 missing19029_19030 records19029_19030 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19029
    maskCheck19029 AlignedValid.nil

def missing19028_19030 : List (BitVec (edgeCount 12)) :=
  missing19028_19029 ++ missing19029_19030
abbrev records19028_19030 : List Blob :=
  records19028_19029 ++ records19029_19030
theorem aligned19028_19030 :
    AlignedValid 12 4 missing19028_19030 records19028_19030 :=
  aligned19028_19029.append aligned19029_19030

def missing19030_19031 : List (BitVec (edgeCount 12)) :=
  [missing19030]
abbrev records19030_19031 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19030]
theorem aligned19030_19031 :
    AlignedValid 12 4 missing19030_19031 records19030_19031 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19030
    maskCheck19030 AlignedValid.nil

def missing19031_19032 : List (BitVec (edgeCount 12)) :=
  [missing19031]
abbrev records19031_19032 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19031]
theorem aligned19031_19032 :
    AlignedValid 12 4 missing19031_19032 records19031_19032 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19031
    maskCheck19031 AlignedValid.nil

def missing19030_19032 : List (BitVec (edgeCount 12)) :=
  missing19030_19031 ++ missing19031_19032
abbrev records19030_19032 : List Blob :=
  records19030_19031 ++ records19031_19032
theorem aligned19030_19032 :
    AlignedValid 12 4 missing19030_19032 records19030_19032 :=
  aligned19030_19031.append aligned19031_19032

def missing19028_19032 : List (BitVec (edgeCount 12)) :=
  missing19028_19030 ++ missing19030_19032
abbrev records19028_19032 : List Blob :=
  records19028_19030 ++ records19030_19032
theorem aligned19028_19032 :
    AlignedValid 12 4 missing19028_19032 records19028_19032 :=
  aligned19028_19030.append aligned19030_19032

def missing19024_19032 : List (BitVec (edgeCount 12)) :=
  missing19024_19028 ++ missing19028_19032
abbrev records19024_19032 : List Blob :=
  records19024_19028 ++ records19028_19032
theorem aligned19024_19032 :
    AlignedValid 12 4 missing19024_19032 records19024_19032 :=
  aligned19024_19028.append aligned19028_19032

def missing19032_19033 : List (BitVec (edgeCount 12)) :=
  [missing19032]
abbrev records19032_19033 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19032]
theorem aligned19032_19033 :
    AlignedValid 12 4 missing19032_19033 records19032_19033 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19032
    maskCheck19032 AlignedValid.nil

def missing19033_19034 : List (BitVec (edgeCount 12)) :=
  [missing19033]
abbrev records19033_19034 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19033]
theorem aligned19033_19034 :
    AlignedValid 12 4 missing19033_19034 records19033_19034 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19033
    maskCheck19033 AlignedValid.nil

def missing19032_19034 : List (BitVec (edgeCount 12)) :=
  missing19032_19033 ++ missing19033_19034
abbrev records19032_19034 : List Blob :=
  records19032_19033 ++ records19033_19034
theorem aligned19032_19034 :
    AlignedValid 12 4 missing19032_19034 records19032_19034 :=
  aligned19032_19033.append aligned19033_19034

def missing19034_19035 : List (BitVec (edgeCount 12)) :=
  [missing19034]
abbrev records19034_19035 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19034]
theorem aligned19034_19035 :
    AlignedValid 12 4 missing19034_19035 records19034_19035 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19034
    maskCheck19034 AlignedValid.nil

def missing19035_19036 : List (BitVec (edgeCount 12)) :=
  [missing19035]
abbrev records19035_19036 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19035]
theorem aligned19035_19036 :
    AlignedValid 12 4 missing19035_19036 records19035_19036 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19035
    maskCheck19035 AlignedValid.nil

def missing19034_19036 : List (BitVec (edgeCount 12)) :=
  missing19034_19035 ++ missing19035_19036
abbrev records19034_19036 : List Blob :=
  records19034_19035 ++ records19035_19036
theorem aligned19034_19036 :
    AlignedValid 12 4 missing19034_19036 records19034_19036 :=
  aligned19034_19035.append aligned19035_19036

def missing19032_19036 : List (BitVec (edgeCount 12)) :=
  missing19032_19034 ++ missing19034_19036
abbrev records19032_19036 : List Blob :=
  records19032_19034 ++ records19034_19036
theorem aligned19032_19036 :
    AlignedValid 12 4 missing19032_19036 records19032_19036 :=
  aligned19032_19034.append aligned19034_19036

def missing19036_19037 : List (BitVec (edgeCount 12)) :=
  [missing19036]
abbrev records19036_19037 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19036]
theorem aligned19036_19037 :
    AlignedValid 12 4 missing19036_19037 records19036_19037 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19036
    maskCheck19036 AlignedValid.nil

def missing19037_19038 : List (BitVec (edgeCount 12)) :=
  [missing19037]
abbrev records19037_19038 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19037]
theorem aligned19037_19038 :
    AlignedValid 12 4 missing19037_19038 records19037_19038 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19037
    maskCheck19037 AlignedValid.nil

def missing19036_19038 : List (BitVec (edgeCount 12)) :=
  missing19036_19037 ++ missing19037_19038
abbrev records19036_19038 : List Blob :=
  records19036_19037 ++ records19037_19038
theorem aligned19036_19038 :
    AlignedValid 12 4 missing19036_19038 records19036_19038 :=
  aligned19036_19037.append aligned19037_19038

def missing19038_19039 : List (BitVec (edgeCount 12)) :=
  [missing19038]
abbrev records19038_19039 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19038]
theorem aligned19038_19039 :
    AlignedValid 12 4 missing19038_19039 records19038_19039 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19038
    maskCheck19038 AlignedValid.nil

def missing19039_19040 : List (BitVec (edgeCount 12)) :=
  [missing19039]
abbrev records19039_19040 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19039]
theorem aligned19039_19040 :
    AlignedValid 12 4 missing19039_19040 records19039_19040 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19039
    maskCheck19039 AlignedValid.nil

def missing19038_19040 : List (BitVec (edgeCount 12)) :=
  missing19038_19039 ++ missing19039_19040
abbrev records19038_19040 : List Blob :=
  records19038_19039 ++ records19039_19040
theorem aligned19038_19040 :
    AlignedValid 12 4 missing19038_19040 records19038_19040 :=
  aligned19038_19039.append aligned19039_19040

def missing19036_19040 : List (BitVec (edgeCount 12)) :=
  missing19036_19038 ++ missing19038_19040
abbrev records19036_19040 : List Blob :=
  records19036_19038 ++ records19038_19040
theorem aligned19036_19040 :
    AlignedValid 12 4 missing19036_19040 records19036_19040 :=
  aligned19036_19038.append aligned19038_19040

def missing19032_19040 : List (BitVec (edgeCount 12)) :=
  missing19032_19036 ++ missing19036_19040
abbrev records19032_19040 : List Blob :=
  records19032_19036 ++ records19036_19040
theorem aligned19032_19040 :
    AlignedValid 12 4 missing19032_19040 records19032_19040 :=
  aligned19032_19036.append aligned19036_19040

def missing19024_19040 : List (BitVec (edgeCount 12)) :=
  missing19024_19032 ++ missing19032_19040
abbrev records19024_19040 : List Blob :=
  records19024_19032 ++ records19032_19040
theorem aligned19024_19040 :
    AlignedValid 12 4 missing19024_19040 records19024_19040 :=
  aligned19024_19032.append aligned19032_19040

def missing19008_19040 : List (BitVec (edgeCount 12)) :=
  missing19008_19024 ++ missing19024_19040
abbrev records19008_19040 : List Blob :=
  records19008_19024 ++ records19024_19040
theorem aligned19008_19040 :
    AlignedValid 12 4 missing19008_19040 records19008_19040 :=
  aligned19008_19024.append aligned19024_19040

def missing19040_19041 : List (BitVec (edgeCount 12)) :=
  [missing19040]
abbrev records19040_19041 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19040]
theorem aligned19040_19041 :
    AlignedValid 12 4 missing19040_19041 records19040_19041 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19040
    maskCheck19040 AlignedValid.nil

def missing19041_19042 : List (BitVec (edgeCount 12)) :=
  [missing19041]
abbrev records19041_19042 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19041]
theorem aligned19041_19042 :
    AlignedValid 12 4 missing19041_19042 records19041_19042 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19041
    maskCheck19041 AlignedValid.nil

def missing19040_19042 : List (BitVec (edgeCount 12)) :=
  missing19040_19041 ++ missing19041_19042
abbrev records19040_19042 : List Blob :=
  records19040_19041 ++ records19041_19042
theorem aligned19040_19042 :
    AlignedValid 12 4 missing19040_19042 records19040_19042 :=
  aligned19040_19041.append aligned19041_19042

def missing19042_19043 : List (BitVec (edgeCount 12)) :=
  [missing19042]
abbrev records19042_19043 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19042]
theorem aligned19042_19043 :
    AlignedValid 12 4 missing19042_19043 records19042_19043 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19042
    maskCheck19042 AlignedValid.nil

def missing19043_19044 : List (BitVec (edgeCount 12)) :=
  [missing19043]
abbrev records19043_19044 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19043]
theorem aligned19043_19044 :
    AlignedValid 12 4 missing19043_19044 records19043_19044 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19043
    maskCheck19043 AlignedValid.nil

def missing19042_19044 : List (BitVec (edgeCount 12)) :=
  missing19042_19043 ++ missing19043_19044
abbrev records19042_19044 : List Blob :=
  records19042_19043 ++ records19043_19044
theorem aligned19042_19044 :
    AlignedValid 12 4 missing19042_19044 records19042_19044 :=
  aligned19042_19043.append aligned19043_19044

def missing19040_19044 : List (BitVec (edgeCount 12)) :=
  missing19040_19042 ++ missing19042_19044
abbrev records19040_19044 : List Blob :=
  records19040_19042 ++ records19042_19044
theorem aligned19040_19044 :
    AlignedValid 12 4 missing19040_19044 records19040_19044 :=
  aligned19040_19042.append aligned19042_19044

def missing19044_19045 : List (BitVec (edgeCount 12)) :=
  [missing19044]
abbrev records19044_19045 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19044]
theorem aligned19044_19045 :
    AlignedValid 12 4 missing19044_19045 records19044_19045 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19044
    maskCheck19044 AlignedValid.nil

def missing19045_19046 : List (BitVec (edgeCount 12)) :=
  [missing19045]
abbrev records19045_19046 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19045]
theorem aligned19045_19046 :
    AlignedValid 12 4 missing19045_19046 records19045_19046 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19045
    maskCheck19045 AlignedValid.nil

def missing19044_19046 : List (BitVec (edgeCount 12)) :=
  missing19044_19045 ++ missing19045_19046
abbrev records19044_19046 : List Blob :=
  records19044_19045 ++ records19045_19046
theorem aligned19044_19046 :
    AlignedValid 12 4 missing19044_19046 records19044_19046 :=
  aligned19044_19045.append aligned19045_19046

def missing19046_19047 : List (BitVec (edgeCount 12)) :=
  [missing19046]
abbrev records19046_19047 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19046]
theorem aligned19046_19047 :
    AlignedValid 12 4 missing19046_19047 records19046_19047 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19046
    maskCheck19046 AlignedValid.nil

def missing19047_19048 : List (BitVec (edgeCount 12)) :=
  [missing19047]
abbrev records19047_19048 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19047]
theorem aligned19047_19048 :
    AlignedValid 12 4 missing19047_19048 records19047_19048 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19047
    maskCheck19047 AlignedValid.nil

def missing19046_19048 : List (BitVec (edgeCount 12)) :=
  missing19046_19047 ++ missing19047_19048
abbrev records19046_19048 : List Blob :=
  records19046_19047 ++ records19047_19048
theorem aligned19046_19048 :
    AlignedValid 12 4 missing19046_19048 records19046_19048 :=
  aligned19046_19047.append aligned19047_19048

def missing19044_19048 : List (BitVec (edgeCount 12)) :=
  missing19044_19046 ++ missing19046_19048
abbrev records19044_19048 : List Blob :=
  records19044_19046 ++ records19046_19048
theorem aligned19044_19048 :
    AlignedValid 12 4 missing19044_19048 records19044_19048 :=
  aligned19044_19046.append aligned19046_19048

def missing19040_19048 : List (BitVec (edgeCount 12)) :=
  missing19040_19044 ++ missing19044_19048
abbrev records19040_19048 : List Blob :=
  records19040_19044 ++ records19044_19048
theorem aligned19040_19048 :
    AlignedValid 12 4 missing19040_19048 records19040_19048 :=
  aligned19040_19044.append aligned19044_19048

def missing19048_19049 : List (BitVec (edgeCount 12)) :=
  [missing19048]
abbrev records19048_19049 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19048]
theorem aligned19048_19049 :
    AlignedValid 12 4 missing19048_19049 records19048_19049 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19048
    maskCheck19048 AlignedValid.nil

def missing19049_19050 : List (BitVec (edgeCount 12)) :=
  [missing19049]
abbrev records19049_19050 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19049]
theorem aligned19049_19050 :
    AlignedValid 12 4 missing19049_19050 records19049_19050 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19049
    maskCheck19049 AlignedValid.nil

def missing19048_19050 : List (BitVec (edgeCount 12)) :=
  missing19048_19049 ++ missing19049_19050
abbrev records19048_19050 : List Blob :=
  records19048_19049 ++ records19049_19050
theorem aligned19048_19050 :
    AlignedValid 12 4 missing19048_19050 records19048_19050 :=
  aligned19048_19049.append aligned19049_19050

def missing19050_19051 : List (BitVec (edgeCount 12)) :=
  [missing19050]
abbrev records19050_19051 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19050]
theorem aligned19050_19051 :
    AlignedValid 12 4 missing19050_19051 records19050_19051 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19050
    maskCheck19050 AlignedValid.nil

def missing19051_19052 : List (BitVec (edgeCount 12)) :=
  [missing19051]
abbrev records19051_19052 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19051]
theorem aligned19051_19052 :
    AlignedValid 12 4 missing19051_19052 records19051_19052 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19051
    maskCheck19051 AlignedValid.nil

def missing19050_19052 : List (BitVec (edgeCount 12)) :=
  missing19050_19051 ++ missing19051_19052
abbrev records19050_19052 : List Blob :=
  records19050_19051 ++ records19051_19052
theorem aligned19050_19052 :
    AlignedValid 12 4 missing19050_19052 records19050_19052 :=
  aligned19050_19051.append aligned19051_19052

def missing19048_19052 : List (BitVec (edgeCount 12)) :=
  missing19048_19050 ++ missing19050_19052
abbrev records19048_19052 : List Blob :=
  records19048_19050 ++ records19050_19052
theorem aligned19048_19052 :
    AlignedValid 12 4 missing19048_19052 records19048_19052 :=
  aligned19048_19050.append aligned19050_19052

def missing19052_19053 : List (BitVec (edgeCount 12)) :=
  [missing19052]
abbrev records19052_19053 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19052]
theorem aligned19052_19053 :
    AlignedValid 12 4 missing19052_19053 records19052_19053 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19052
    maskCheck19052 AlignedValid.nil

def missing19053_19054 : List (BitVec (edgeCount 12)) :=
  [missing19053]
abbrev records19053_19054 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19053]
theorem aligned19053_19054 :
    AlignedValid 12 4 missing19053_19054 records19053_19054 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19053
    maskCheck19053 AlignedValid.nil

def missing19052_19054 : List (BitVec (edgeCount 12)) :=
  missing19052_19053 ++ missing19053_19054
abbrev records19052_19054 : List Blob :=
  records19052_19053 ++ records19053_19054
theorem aligned19052_19054 :
    AlignedValid 12 4 missing19052_19054 records19052_19054 :=
  aligned19052_19053.append aligned19053_19054

def missing19054_19055 : List (BitVec (edgeCount 12)) :=
  [missing19054]
abbrev records19054_19055 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19054]
theorem aligned19054_19055 :
    AlignedValid 12 4 missing19054_19055 records19054_19055 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19054
    maskCheck19054 AlignedValid.nil

def missing19055_19056 : List (BitVec (edgeCount 12)) :=
  [missing19055]
abbrev records19055_19056 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19055]
theorem aligned19055_19056 :
    AlignedValid 12 4 missing19055_19056 records19055_19056 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19055
    maskCheck19055 AlignedValid.nil

def missing19054_19056 : List (BitVec (edgeCount 12)) :=
  missing19054_19055 ++ missing19055_19056
abbrev records19054_19056 : List Blob :=
  records19054_19055 ++ records19055_19056
theorem aligned19054_19056 :
    AlignedValid 12 4 missing19054_19056 records19054_19056 :=
  aligned19054_19055.append aligned19055_19056

def missing19052_19056 : List (BitVec (edgeCount 12)) :=
  missing19052_19054 ++ missing19054_19056
abbrev records19052_19056 : List Blob :=
  records19052_19054 ++ records19054_19056
theorem aligned19052_19056 :
    AlignedValid 12 4 missing19052_19056 records19052_19056 :=
  aligned19052_19054.append aligned19054_19056

def missing19048_19056 : List (BitVec (edgeCount 12)) :=
  missing19048_19052 ++ missing19052_19056
abbrev records19048_19056 : List Blob :=
  records19048_19052 ++ records19052_19056
theorem aligned19048_19056 :
    AlignedValid 12 4 missing19048_19056 records19048_19056 :=
  aligned19048_19052.append aligned19052_19056

def missing19040_19056 : List (BitVec (edgeCount 12)) :=
  missing19040_19048 ++ missing19048_19056
abbrev records19040_19056 : List Blob :=
  records19040_19048 ++ records19048_19056
theorem aligned19040_19056 :
    AlignedValid 12 4 missing19040_19056 records19040_19056 :=
  aligned19040_19048.append aligned19048_19056

def missing19056_19057 : List (BitVec (edgeCount 12)) :=
  [missing19056]
abbrev records19056_19057 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19056]
theorem aligned19056_19057 :
    AlignedValid 12 4 missing19056_19057 records19056_19057 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19056
    maskCheck19056 AlignedValid.nil

def missing19057_19058 : List (BitVec (edgeCount 12)) :=
  [missing19057]
abbrev records19057_19058 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19057]
theorem aligned19057_19058 :
    AlignedValid 12 4 missing19057_19058 records19057_19058 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19057
    maskCheck19057 AlignedValid.nil

def missing19056_19058 : List (BitVec (edgeCount 12)) :=
  missing19056_19057 ++ missing19057_19058
abbrev records19056_19058 : List Blob :=
  records19056_19057 ++ records19057_19058
theorem aligned19056_19058 :
    AlignedValid 12 4 missing19056_19058 records19056_19058 :=
  aligned19056_19057.append aligned19057_19058

def missing19058_19059 : List (BitVec (edgeCount 12)) :=
  [missing19058]
abbrev records19058_19059 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19058]
theorem aligned19058_19059 :
    AlignedValid 12 4 missing19058_19059 records19058_19059 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19058
    maskCheck19058 AlignedValid.nil

def missing19059_19060 : List (BitVec (edgeCount 12)) :=
  [missing19059]
abbrev records19059_19060 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19059]
theorem aligned19059_19060 :
    AlignedValid 12 4 missing19059_19060 records19059_19060 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19059
    maskCheck19059 AlignedValid.nil

def missing19058_19060 : List (BitVec (edgeCount 12)) :=
  missing19058_19059 ++ missing19059_19060
abbrev records19058_19060 : List Blob :=
  records19058_19059 ++ records19059_19060
theorem aligned19058_19060 :
    AlignedValid 12 4 missing19058_19060 records19058_19060 :=
  aligned19058_19059.append aligned19059_19060

def missing19056_19060 : List (BitVec (edgeCount 12)) :=
  missing19056_19058 ++ missing19058_19060
abbrev records19056_19060 : List Blob :=
  records19056_19058 ++ records19058_19060
theorem aligned19056_19060 :
    AlignedValid 12 4 missing19056_19060 records19056_19060 :=
  aligned19056_19058.append aligned19058_19060

def missing19060_19061 : List (BitVec (edgeCount 12)) :=
  [missing19060]
abbrev records19060_19061 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19060]
theorem aligned19060_19061 :
    AlignedValid 12 4 missing19060_19061 records19060_19061 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19060
    maskCheck19060 AlignedValid.nil

def missing19061_19062 : List (BitVec (edgeCount 12)) :=
  [missing19061]
abbrev records19061_19062 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19061]
theorem aligned19061_19062 :
    AlignedValid 12 4 missing19061_19062 records19061_19062 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19061
    maskCheck19061 AlignedValid.nil

def missing19060_19062 : List (BitVec (edgeCount 12)) :=
  missing19060_19061 ++ missing19061_19062
abbrev records19060_19062 : List Blob :=
  records19060_19061 ++ records19061_19062
theorem aligned19060_19062 :
    AlignedValid 12 4 missing19060_19062 records19060_19062 :=
  aligned19060_19061.append aligned19061_19062

def missing19062_19063 : List (BitVec (edgeCount 12)) :=
  [missing19062]
abbrev records19062_19063 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19062]
theorem aligned19062_19063 :
    AlignedValid 12 4 missing19062_19063 records19062_19063 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19062
    maskCheck19062 AlignedValid.nil

def missing19063_19064 : List (BitVec (edgeCount 12)) :=
  [missing19063]
abbrev records19063_19064 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19063]
theorem aligned19063_19064 :
    AlignedValid 12 4 missing19063_19064 records19063_19064 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19063
    maskCheck19063 AlignedValid.nil

def missing19062_19064 : List (BitVec (edgeCount 12)) :=
  missing19062_19063 ++ missing19063_19064
abbrev records19062_19064 : List Blob :=
  records19062_19063 ++ records19063_19064
theorem aligned19062_19064 :
    AlignedValid 12 4 missing19062_19064 records19062_19064 :=
  aligned19062_19063.append aligned19063_19064

def missing19060_19064 : List (BitVec (edgeCount 12)) :=
  missing19060_19062 ++ missing19062_19064
abbrev records19060_19064 : List Blob :=
  records19060_19062 ++ records19062_19064
theorem aligned19060_19064 :
    AlignedValid 12 4 missing19060_19064 records19060_19064 :=
  aligned19060_19062.append aligned19062_19064

def missing19056_19064 : List (BitVec (edgeCount 12)) :=
  missing19056_19060 ++ missing19060_19064
abbrev records19056_19064 : List Blob :=
  records19056_19060 ++ records19060_19064
theorem aligned19056_19064 :
    AlignedValid 12 4 missing19056_19064 records19056_19064 :=
  aligned19056_19060.append aligned19060_19064

def missing19064_19065 : List (BitVec (edgeCount 12)) :=
  [missing19064]
abbrev records19064_19065 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19064]
theorem aligned19064_19065 :
    AlignedValid 12 4 missing19064_19065 records19064_19065 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19064
    maskCheck19064 AlignedValid.nil

def missing19065_19066 : List (BitVec (edgeCount 12)) :=
  [missing19065]
abbrev records19065_19066 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19065]
theorem aligned19065_19066 :
    AlignedValid 12 4 missing19065_19066 records19065_19066 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19065
    maskCheck19065 AlignedValid.nil

def missing19064_19066 : List (BitVec (edgeCount 12)) :=
  missing19064_19065 ++ missing19065_19066
abbrev records19064_19066 : List Blob :=
  records19064_19065 ++ records19065_19066
theorem aligned19064_19066 :
    AlignedValid 12 4 missing19064_19066 records19064_19066 :=
  aligned19064_19065.append aligned19065_19066

def missing19066_19067 : List (BitVec (edgeCount 12)) :=
  [missing19066]
abbrev records19066_19067 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19066]
theorem aligned19066_19067 :
    AlignedValid 12 4 missing19066_19067 records19066_19067 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19066
    maskCheck19066 AlignedValid.nil

def missing19067_19068 : List (BitVec (edgeCount 12)) :=
  [missing19067]
abbrev records19067_19068 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19067]
theorem aligned19067_19068 :
    AlignedValid 12 4 missing19067_19068 records19067_19068 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19067
    maskCheck19067 AlignedValid.nil

def missing19066_19068 : List (BitVec (edgeCount 12)) :=
  missing19066_19067 ++ missing19067_19068
abbrev records19066_19068 : List Blob :=
  records19066_19067 ++ records19067_19068
theorem aligned19066_19068 :
    AlignedValid 12 4 missing19066_19068 records19066_19068 :=
  aligned19066_19067.append aligned19067_19068

def missing19064_19068 : List (BitVec (edgeCount 12)) :=
  missing19064_19066 ++ missing19066_19068
abbrev records19064_19068 : List Blob :=
  records19064_19066 ++ records19066_19068
theorem aligned19064_19068 :
    AlignedValid 12 4 missing19064_19068 records19064_19068 :=
  aligned19064_19066.append aligned19066_19068

def missing19068_19069 : List (BitVec (edgeCount 12)) :=
  [missing19068]
abbrev records19068_19069 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19068]
theorem aligned19068_19069 :
    AlignedValid 12 4 missing19068_19069 records19068_19069 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19068
    maskCheck19068 AlignedValid.nil

def missing19069_19070 : List (BitVec (edgeCount 12)) :=
  [missing19069]
abbrev records19069_19070 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19069]
theorem aligned19069_19070 :
    AlignedValid 12 4 missing19069_19070 records19069_19070 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19069
    maskCheck19069 AlignedValid.nil

def missing19068_19070 : List (BitVec (edgeCount 12)) :=
  missing19068_19069 ++ missing19069_19070
abbrev records19068_19070 : List Blob :=
  records19068_19069 ++ records19069_19070
theorem aligned19068_19070 :
    AlignedValid 12 4 missing19068_19070 records19068_19070 :=
  aligned19068_19069.append aligned19069_19070

def missing19070_19071 : List (BitVec (edgeCount 12)) :=
  [missing19070]
abbrev records19070_19071 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19070]
theorem aligned19070_19071 :
    AlignedValid 12 4 missing19070_19071 records19070_19071 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19070
    maskCheck19070 AlignedValid.nil

def missing19071_19072 : List (BitVec (edgeCount 12)) :=
  [missing19071]
abbrev records19071_19072 : List Blob :=
  [StrongPackedBucketN12A4Shard148.record19071]
theorem aligned19071_19072 :
    AlignedValid 12 4 missing19071_19072 records19071_19072 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard148.check19071
    maskCheck19071 AlignedValid.nil

def missing19070_19072 : List (BitVec (edgeCount 12)) :=
  missing19070_19071 ++ missing19071_19072
abbrev records19070_19072 : List Blob :=
  records19070_19071 ++ records19071_19072
theorem aligned19070_19072 :
    AlignedValid 12 4 missing19070_19072 records19070_19072 :=
  aligned19070_19071.append aligned19071_19072

def missing19068_19072 : List (BitVec (edgeCount 12)) :=
  missing19068_19070 ++ missing19070_19072
abbrev records19068_19072 : List Blob :=
  records19068_19070 ++ records19070_19072
theorem aligned19068_19072 :
    AlignedValid 12 4 missing19068_19072 records19068_19072 :=
  aligned19068_19070.append aligned19070_19072

def missing19064_19072 : List (BitVec (edgeCount 12)) :=
  missing19064_19068 ++ missing19068_19072
abbrev records19064_19072 : List Blob :=
  records19064_19068 ++ records19068_19072
theorem aligned19064_19072 :
    AlignedValid 12 4 missing19064_19072 records19064_19072 :=
  aligned19064_19068.append aligned19068_19072

def missing19056_19072 : List (BitVec (edgeCount 12)) :=
  missing19056_19064 ++ missing19064_19072
abbrev records19056_19072 : List Blob :=
  records19056_19064 ++ records19064_19072
theorem aligned19056_19072 :
    AlignedValid 12 4 missing19056_19072 records19056_19072 :=
  aligned19056_19064.append aligned19064_19072

def missing19040_19072 : List (BitVec (edgeCount 12)) :=
  missing19040_19056 ++ missing19056_19072
abbrev records19040_19072 : List Blob :=
  records19040_19056 ++ records19056_19072
theorem aligned19040_19072 :
    AlignedValid 12 4 missing19040_19072 records19040_19072 :=
  aligned19040_19056.append aligned19056_19072

def missing19008_19072 : List (BitVec (edgeCount 12)) :=
  missing19008_19040 ++ missing19040_19072
abbrev records19008_19072 : List Blob :=
  records19008_19040 ++ records19040_19072
theorem aligned19008_19072 :
    AlignedValid 12 4 missing19008_19072 records19008_19072 :=
  aligned19008_19040.append aligned19040_19072

def missing18944_19072 : List (BitVec (edgeCount 12)) :=
  missing18944_19008 ++ missing19008_19072
abbrev records18944_19072 : List Blob :=
  records18944_19008 ++ records19008_19072
theorem aligned18944_19072 :
    AlignedValid 12 4 missing18944_19072 records18944_19072 :=
  aligned18944_19008.append aligned19008_19072

abbrev missing : List (BitVec (edgeCount 12)) := missing18944_19072
abbrev records : List Blob := records18944_19072
theorem aligned : AlignedValid 12 4 missing records := aligned18944_19072

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard148
