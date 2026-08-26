/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard140

/-! Decode-only alignment checks for n=12, a=4, records 17920--18047. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard140

open PackedBucketCertificate

def missing17920 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46522404122321223680
theorem maskCheck17920 :
    checkMaskFor missing17920 StrongPackedBucketN12A4Shard140.record17920 = true := by
  decide

def missing17921 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46630490513378115584
theorem maskCheck17921 :
    checkMaskFor missing17921 StrongPackedBucketN12A4Shard140.record17921 = true := by
  decide

def missing17922 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47062836077605683200
theorem maskCheck17922 :
    checkMaskFor missing17922 StrongPackedBucketN12A4Shard140.record17922 = true := by
  decide

def missing17923 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50845859764596899840
theorem maskCheck17923 :
    checkMaskFor missing17923 StrongPackedBucketN12A4Shard140.record17923 = true := by
  decide

def missing17924 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60069231801451675648
theorem maskCheck17924 :
    checkMaskFor missing17924 StrongPackedBucketN12A4Shard140.record17924 = true := by
  decide

def missing17925 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60141289395489603584
theorem maskCheck17925 :
    checkMaskFor missing17925 StrongPackedBucketN12A4Shard140.record17925 = true := by
  decide

def missing17926 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60285404583565459456
theorem maskCheck17926 :
    checkMaskFor missing17926 StrongPackedBucketN12A4Shard140.record17926 = true := by
  decide

def missing17927 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1139454755448291328
theorem maskCheck17927 :
    checkMaskFor missing17927 StrongPackedBucketN12A4Shard140.record17927 = true := by
  decide

def missing17928 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2220318666017210368
theorem maskCheck17928 :
    checkMaskFor missing17928 StrongPackedBucketN12A4Shard140.record17928 = true := by
  decide

def missing17929 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2256347463036174336
theorem maskCheck17929 :
    checkMaskFor missing17929 StrongPackedBucketN12A4Shard140.record17929 = true := by
  decide

def missing17930 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4490132878211940352
theorem maskCheck17930 :
    checkMaskFor missing17930 StrongPackedBucketN12A4Shard140.record17930 = true := by
  decide

def missing17931 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5174680021572255744
theorem maskCheck17931 :
    checkMaskFor missing17931 StrongPackedBucketN12A4Shard140.record17931 = true := by
  decide

def missing17932 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5679083179837751296
theorem maskCheck17932 :
    checkMaskFor missing17932 StrongPackedBucketN12A4Shard140.record17932 = true := by
  decide

def missing17933 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9786366039999643648
theorem maskCheck17933 :
    checkMaskFor missing17933 StrongPackedBucketN12A4Shard140.record17933 = true := by
  decide

def missing17934 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10326797995284103168
theorem maskCheck17934 :
    checkMaskFor missing17934 StrongPackedBucketN12A4Shard140.record17934 = true := by
  decide

def missing17935 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14109821682275319808
theorem maskCheck17935 :
    checkMaskFor missing17935 StrongPackedBucketN12A4Shard140.record17935 = true := by
  decide

def missing17936 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23333193719130095616
theorem maskCheck17936 :
    checkMaskFor missing17936 StrongPackedBucketN12A4Shard140.record17936 = true := by
  decide

def missing17937 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23549366501243879424
theorem maskCheck17937 :
    checkMaskFor missing17937 StrongPackedBucketN12A4Shard140.record17937 = true := by
  decide

def missing17938 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32412450567909015552
theorem maskCheck17938 :
    checkMaskFor missing17938 StrongPackedBucketN12A4Shard140.record17938 = true := by
  decide

def missing17939 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60082566678473342976
theorem maskCheck17939 :
    checkMaskFor missing17939 StrongPackedBucketN12A4Shard140.record17939 = true := by
  decide

def missing17940 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60154624272511270912
theorem maskCheck17940 :
    checkMaskFor missing17940 StrongPackedBucketN12A4Shard140.record17940 = true := by
  decide

def missing17941 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5116625807625682944
theorem maskCheck17941 :
    checkMaskFor missing17941 StrongPackedBucketN12A4Shard140.record17941 = true := by
  decide

def missing17942 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5404856183777394688
theorem maskCheck17942 :
    checkMaskFor missing17942 StrongPackedBucketN12A4Shard140.record17942 = true := by
  decide

def missing17943 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6413662500308385792
theorem maskCheck17943 :
    checkMaskFor missing17943 StrongPackedBucketN12A4Shard140.record17943 = true := by
  decide

def missing17944 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9728311826053070848
theorem maskCheck17944 :
    checkMaskFor missing17944 StrongPackedBucketN12A4Shard140.record17944 = true := by
  decide

def missing17945 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10016542202204782592
theorem maskCheck17945 :
    checkMaskFor missing17945 StrongPackedBucketN12A4Shard140.record17945 = true := by
  decide

def missing17946 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11025348518735773696
theorem maskCheck17946 :
    checkMaskFor missing17946 StrongPackedBucketN12A4Shard140.record17946 = true := by
  decide

def missing17947 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14051767468328747008
theorem maskCheck17947 :
    checkMaskFor missing17947 StrongPackedBucketN12A4Shard140.record17947 = true := by
  decide

def missing17948 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14267940250442530816
theorem maskCheck17948 :
    checkMaskFor missing17948 StrongPackedBucketN12A4Shard140.record17948 = true := by
  decide

def missing17949 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14484113032556314624
theorem maskCheck17949 :
    checkMaskFor missing17949 StrongPackedBucketN12A4Shard140.record17949 = true := by
  decide

def missing17950 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14556170626594242560
theorem maskCheck17950 :
    checkMaskFor missing17950 StrongPackedBucketN12A4Shard140.record17950 = true := by
  decide

def missing17951 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15564976943125233664
theorem maskCheck17951 :
    checkMaskFor missing17951 StrongPackedBucketN12A4Shard140.record17951 = true := by
  decide

def missing17952 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23275139505183522816
theorem maskCheck17952 :
    checkMaskFor missing17952 StrongPackedBucketN12A4Shard140.record17952 = true := by
  decide

def missing17953 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23707485069411090432
theorem maskCheck17953 :
    checkMaskFor missing17953 StrongPackedBucketN12A4Shard140.record17953 = true := by
  decide

def missing17954 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32354396353962442752
theorem maskCheck17954 :
    checkMaskFor missing17954 StrongPackedBucketN12A4Shard140.record17954 = true := by
  decide

def missing17955 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32426453948000370688
theorem maskCheck17955 :
    checkMaskFor missing17955 StrongPackedBucketN12A4Shard140.record17955 = true := by
  decide

def missing17956 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32858799512227938304
theorem maskCheck17956 :
    checkMaskFor missing17956 StrongPackedBucketN12A4Shard140.record17956 = true := by
  decide

def missing17957 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081893122710962176
theorem maskCheck17957 :
    checkMaskFor missing17957 StrongPackedBucketN12A4Shard140.record17957 = true := by
  decide

def missing17958 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1658353875014385664
theorem maskCheck17958 :
    checkMaskFor missing17958 StrongPackedBucketN12A4Shard140.record17958 = true := by
  decide

def missing17959 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3675966508076367872
theorem maskCheck17959 :
    checkMaskFor missing17959 StrongPackedBucketN12A4Shard140.record17959 = true := by
  decide

def missing17960 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5117118388834926592
theorem maskCheck17960 :
    checkMaskFor missing17960 StrongPackedBucketN12A4Shard140.record17960 = true := by
  decide

def missing17961 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5621521547100422144
theorem maskCheck17961 :
    checkMaskFor missing17961 StrongPackedBucketN12A4Shard140.record17961 = true := by
  decide

def missing17962 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5981809517290061824
theorem maskCheck17962 :
    checkMaskFor missing17962 StrongPackedBucketN12A4Shard140.record17962 = true := by
  decide

def missing17963 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6197982299403845632
theorem maskCheck17963 :
    checkMaskFor missing17963 StrongPackedBucketN12A4Shard140.record17963 = true := by
  decide

def missing17964 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8143537338427899904
theorem maskCheck17964 :
    checkMaskFor missing17964 StrongPackedBucketN12A4Shard140.record17964 = true := by
  decide

def missing17965 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8215594932465827840
theorem maskCheck17965 :
    checkMaskFor missing17965 StrongPackedBucketN12A4Shard140.record17965 = true := by
  decide

def missing17966 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9728804407262314496
theorem maskCheck17966 :
    checkMaskFor missing17966 StrongPackedBucketN12A4Shard140.record17966 = true := by
  decide

def missing17967 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10593495535717449728
theorem maskCheck17967 :
    checkMaskFor missing17967 StrongPackedBucketN12A4Shard140.record17967 = true := by
  decide

def missing17968 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12755223356855287808
theorem maskCheck17968 :
    checkMaskFor missing17968 StrongPackedBucketN12A4Shard140.record17968 = true := by
  decide

def missing17969 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14052260049537990656
theorem maskCheck17969 :
    checkMaskFor missing17969 StrongPackedBucketN12A4Shard140.record17969 = true := by
  decide

def missing17970 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15061066366068981760
theorem maskCheck17970 :
    checkMaskFor missing17970 StrongPackedBucketN12A4Shard140.record17970 = true := by
  decide

def missing17971 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23275632086392766464
theorem maskCheck17971 :
    checkMaskFor missing17971 StrongPackedBucketN12A4Shard140.record17971 = true := by
  decide

def missing17972 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23491804868506550272
theorem maskCheck17972 :
    checkMaskFor missing17972 StrongPackedBucketN12A4Shard140.record17972 = true := by
  decide

def missing17973 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24284438402923757568
theorem maskCheck17973 :
    checkMaskFor missing17973 StrongPackedBucketN12A4Shard140.record17973 = true := by
  decide

def missing17974 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24356495996961685504
theorem maskCheck17974 :
    checkMaskFor missing17974 StrongPackedBucketN12A4Shard140.record17974 = true := by
  decide

def missing17975 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 26518223818099523584
theorem maskCheck17975 :
    checkMaskFor missing17975 StrongPackedBucketN12A4Shard140.record17975 = true := by
  decide

def missing17976 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32354888935171686400
theorem maskCheck17976 :
    checkMaskFor missing17976 StrongPackedBucketN12A4Shard140.record17976 = true := by
  decide

def missing17977 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 541496351798591488
theorem maskCheck17977 :
    checkMaskFor missing17977 StrongPackedBucketN12A4Shard140.record17977 = true := by
  decide

def missing17978 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081928307083051008
theorem maskCheck17978 :
    checkMaskFor missing17978 StrongPackedBucketN12A4Shard140.record17978 = true := by
  decide

def missing17979 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1406187480253726720
theorem maskCheck17979 :
    checkMaskFor missing17979 StrongPackedBucketN12A4Shard140.record17979 = true := by
  decide

def missing17980 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1658389059386474496
theorem maskCheck17980 :
    checkMaskFor missing17980 StrongPackedBucketN12A4Shard140.record17980 = true := by
  decide

def missing17981 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3567915301391564800
theorem maskCheck17981 :
    checkMaskFor missing17981 StrongPackedBucketN12A4Shard140.record17981 = true := by
  decide

def missing17982 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3676001692448456704
theorem maskCheck17982 :
    checkMaskFor missing17982 StrongPackedBucketN12A4Shard140.record17982 = true := by
  decide

def missing17983 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4864951994074267648
theorem maskCheck17983 :
    checkMaskFor missing17983 StrongPackedBucketN12A4Shard140.record17983 = true := by
  decide

def missing17984 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5873758310605258752
theorem maskCheck17984 :
    checkMaskFor missing17984 StrongPackedBucketN12A4Shard140.record17984 = true := by
  decide

def missing17985 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9476638012501655552
theorem maskCheck17985 :
    checkMaskFor missing17985 StrongPackedBucketN12A4Shard140.record17985 = true := by
  decide

def missing17986 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9692810794615439360
theorem maskCheck17986 :
    checkMaskFor missing17986 StrongPackedBucketN12A4Shard140.record17986 = true := by
  decide

def missing17987 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9728839591634403328
theorem maskCheck17987 :
    checkMaskFor missing17987 StrongPackedBucketN12A4Shard140.record17987 = true := by
  decide

def missing17988 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10233242749899898880
theorem maskCheck17988 :
    checkMaskFor missing17988 StrongPackedBucketN12A4Shard140.record17988 = true := by
  decide

def missing17989 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10485444329032646656
theorem maskCheck17989 :
    checkMaskFor missing17989 StrongPackedBucketN12A4Shard140.record17989 = true := by
  decide

def missing17990 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10557501923070574592
theorem maskCheck17990 :
    checkMaskFor missing17990 StrongPackedBucketN12A4Shard140.record17990 = true := by
  decide

def missing17991 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10593530720089538560
theorem maskCheck17991 :
    checkMaskFor missing17991 StrongPackedBucketN12A4Shard140.record17991 = true := by
  decide

def missing17992 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10809703502203322368
theorem maskCheck17992 :
    checkMaskFor missing17992 StrongPackedBucketN12A4Shard140.record17992 = true := by
  decide

def missing17993 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12719229744208412672
theorem maskCheck17993 :
    checkMaskFor missing17993 StrongPackedBucketN12A4Shard140.record17993 = true := by
  decide

def missing17994 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12755258541227376640
theorem maskCheck17994 :
    checkMaskFor missing17994 StrongPackedBucketN12A4Shard140.record17994 = true := by
  decide

def missing17995 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12827316135265304576
theorem maskCheck17995 :
    checkMaskFor missing17995 StrongPackedBucketN12A4Shard140.record17995 = true := by
  decide

def missing17996 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13944208842853187584
theorem maskCheck17996 :
    checkMaskFor missing17996 StrongPackedBucketN12A4Shard140.record17996 = true := by
  decide

def missing17997 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14016266436891115520
theorem maskCheck17997 :
    checkMaskFor missing17997 StrongPackedBucketN12A4Shard140.record17997 = true := by
  decide

def missing17998 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15025072753422106624
theorem maskCheck17998 :
    checkMaskFor missing17998 StrongPackedBucketN12A4Shard140.record17998 = true := by
  decide

def missing17999 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23167580879707963392
theorem maskCheck17999 :
    checkMaskFor missing17999 StrongPackedBucketN12A4Shard140.record17999 = true := by
  decide

def missing18000 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32318895322524811264
theorem maskCheck18000 :
    checkMaskFor missing18000 StrongPackedBucketN12A4Shard140.record18000 = true := by
  decide

def missing18001 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 542551882961256448
theorem maskCheck18001 :
    checkMaskFor missing18001 StrongPackedBucketN12A4Shard140.record18001 = true := by
  decide

def missing18002 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1046955041226752000
theorem maskCheck18002 :
    checkMaskFor missing18002 StrongPackedBucketN12A4Shard140.record18002 = true := by
  decide

def missing18003 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1082983838245715968
theorem maskCheck18003 :
    checkMaskFor missing18003 StrongPackedBucketN12A4Shard140.record18003 = true := by
  decide

def missing18004 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2163847748814635008
theorem maskCheck18004 :
    checkMaskFor missing18004 StrongPackedBucketN12A4Shard140.record18004 = true := by
  decide

def missing18005 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2560164516023238656
theorem maskCheck18005 :
    checkMaskFor missing18005 StrongPackedBucketN12A4Shard140.record18005 = true := by
  decide

def missing18006 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2776337298137022464
theorem maskCheck18006 :
    checkMaskFor missing18006 StrongPackedBucketN12A4Shard140.record18006 = true := by
  decide

def missing18007 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2812366095155986432
theorem maskCheck18007 :
    checkMaskFor missing18007 StrongPackedBucketN12A4Shard140.record18007 = true := by
  decide

def missing18008 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3316769253421481984
theorem maskCheck18008 :
    checkMaskFor missing18008 StrongPackedBucketN12A4Shard140.record18008 = true := by
  decide

def missing18009 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4866007525236932608
theorem maskCheck18009 :
    checkMaskFor missing18009 StrongPackedBucketN12A4Shard140.record18009 = true := by
  decide

def missing18010 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5082180307350716416
theorem maskCheck18010 :
    checkMaskFor missing18010 StrongPackedBucketN12A4Shard140.record18010 = true := by
  decide

def missing18011 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7027735346374770688
theorem maskCheck18011 :
    checkMaskFor missing18011 StrongPackedBucketN12A4Shard140.record18011 = true := by
  decide

def missing18012 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7099792940412698624
theorem maskCheck18012 :
    checkMaskFor missing18012 StrongPackedBucketN12A4Shard140.record18012 = true := by
  decide

def missing18013 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9477693543664320512
theorem maskCheck18013 :
    checkMaskFor missing18013 StrongPackedBucketN12A4Shard140.record18013 = true := by
  decide

def missing18014 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9729895122797068288
theorem maskCheck18014 :
    checkMaskFor missing18014 StrongPackedBucketN12A4Shard140.record18014 = true := by
  decide

def missing18015 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11639421364802158592
theorem maskCheck18015 :
    checkMaskFor missing18015 StrongPackedBucketN12A4Shard140.record18015 = true := by
  decide

def missing18016 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11747507755859050496
theorem maskCheck18016 :
    checkMaskFor missing18016 StrongPackedBucketN12A4Shard140.record18016 = true := by
  decide

def missing18017 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13945264374015852544
theorem maskCheck18017 :
    checkMaskFor missing18017 StrongPackedBucketN12A4Shard140.record18017 = true := by
  decide

def missing18018 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23168636410870628352
theorem maskCheck18018 :
    checkMaskFor missing18018 StrongPackedBucketN12A4Shard140.record18018 = true := by
  decide

def missing18019 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23240694004908556288
theorem maskCheck18019 :
    checkMaskFor missing18019 StrongPackedBucketN12A4Shard140.record18019 = true := by
  decide

def missing18020 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25402421826046394368
theorem maskCheck18020 :
    checkMaskFor missing18020 StrongPackedBucketN12A4Shard140.record18020 = true := by
  decide

def missing18021 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9732533950703730688
theorem maskCheck18021 :
    checkMaskFor missing18021 StrongPackedBucketN12A4Shard140.record18021 = true := by
  decide

def missing18022 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10164879514931298304
theorem maskCheck18022 :
    checkMaskFor missing18022 StrongPackedBucketN12A4Shard140.record18022 = true := by
  decide

def missing18023 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27891047648261570560
theorem maskCheck18023 :
    checkMaskFor missing18023 StrongPackedBucketN12A4Shard140.record18023 = true := by
  decide

def missing18024 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28035162836337426432
theorem maskCheck18024 :
    checkMaskFor missing18024 StrongPackedBucketN12A4Shard140.record18024 = true := by
  decide

def missing18025 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1085833772384911360
theorem maskCheck18025 :
    checkMaskFor missing18025 StrongPackedBucketN12A4Shard140.record18025 = true := by
  decide

def missing18026 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1950524900840046592
theorem maskCheck18026 :
    checkMaskFor missing18026 StrongPackedBucketN12A4Shard140.record18026 = true := by
  decide

def missing18027 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4112252721977884672
theorem maskCheck18027 :
    checkMaskFor missing18027 StrongPackedBucketN12A4Shard140.record18027 = true := by
  decide

def missing18028 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9732745056936263680
theorem maskCheck18028 :
    checkMaskFor missing18028 StrongPackedBucketN12A4Shard140.record18028 = true := by
  decide

def missing18029 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10020975433087975424
theorem maskCheck18029 :
    checkMaskFor missing18029 StrongPackedBucketN12A4Shard140.record18029 = true := by
  decide

def missing18030 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11029781749618966528
theorem maskCheck18030 :
    checkMaskFor missing18030 StrongPackedBucketN12A4Shard140.record18030 = true := by
  decide

def missing18031 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18956117093791039488
theorem maskCheck18031 :
    checkMaskFor missing18031 StrongPackedBucketN12A4Shard140.record18031 = true := by
  decide

def missing18032 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19244347469942751232
theorem maskCheck18032 :
    checkMaskFor missing18032 StrongPackedBucketN12A4Shard140.record18032 = true := by
  decide

def missing18033 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20253153786473742336
theorem maskCheck18033 :
    checkMaskFor missing18033 StrongPackedBucketN12A4Shard140.record18033 = true := by
  decide

def missing18034 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27891258754494103552
theorem maskCheck18034 :
    checkMaskFor missing18034 StrongPackedBucketN12A4Shard140.record18034 = true := by
  decide

def missing18035 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28323604318721671168
theorem maskCheck18035 :
    checkMaskFor missing18035 StrongPackedBucketN12A4Shard140.record18035 = true := by
  decide

def missing18036 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14060493192606777344
theorem maskCheck18036 :
    checkMaskFor missing18036 StrongPackedBucketN12A4Shard140.record18036 = true := by
  decide

def missing18037 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14204608380682633216
theorem maskCheck18037 :
    checkMaskFor missing18037 StrongPackedBucketN12A4Shard140.record18037 = true := by
  decide

def missing18038 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32363122078240473088
theorem maskCheck18038 :
    checkMaskFor missing18038 StrongPackedBucketN12A4Shard140.record18038 = true := by
  decide

def missing18039 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9485082261802975232
theorem maskCheck18039 :
    checkMaskFor missing18039 StrongPackedBucketN12A4Shard140.record18039 = true := by
  decide

def missing18040 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9737283840935723008
theorem maskCheck18040 :
    checkMaskFor missing18040 StrongPackedBucketN12A4Shard140.record18040 = true := by
  decide

def missing18041 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9917427826030542848
theorem maskCheck18041 :
    checkMaskFor missing18041 StrongPackedBucketN12A4Shard140.record18041 = true := by
  decide

def missing18042 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10025514217087434752
theorem maskCheck18042 :
    checkMaskFor missing18042 StrongPackedBucketN12A4Shard140.record18042 = true := by
  decide

def missing18043 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11034320533618425856
theorem maskCheck18043 :
    checkMaskFor missing18043 StrongPackedBucketN12A4Shard140.record18043 = true := by
  decide

def missing18044 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13952653092154507264
theorem maskCheck18044 :
    checkMaskFor missing18044 StrongPackedBucketN12A4Shard140.record18044 = true := by
  decide

def missing18045 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9750407611724857344
theorem maskCheck18045 :
    checkMaskFor missing18045 StrongPackedBucketN12A4Shard140.record18045 = true := by
  decide

def missing18046 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1103566695917682688
theorem maskCheck18046 :
    checkMaskFor missing18046 StrongPackedBucketN12A4Shard140.record18046 = true := by
  decide

def missing18047 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2112373012448673792
theorem maskCheck18047 :
    checkMaskFor missing18047 StrongPackedBucketN12A4Shard140.record18047 = true := by
  decide

def missing17920_17921 : List (BitVec (edgeCount 12)) :=
  [missing17920]
abbrev records17920_17921 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17920]
theorem aligned17920_17921 :
    AlignedValid 12 4 missing17920_17921 records17920_17921 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17920
    maskCheck17920 AlignedValid.nil

def missing17921_17922 : List (BitVec (edgeCount 12)) :=
  [missing17921]
abbrev records17921_17922 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17921]
theorem aligned17921_17922 :
    AlignedValid 12 4 missing17921_17922 records17921_17922 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17921
    maskCheck17921 AlignedValid.nil

def missing17920_17922 : List (BitVec (edgeCount 12)) :=
  missing17920_17921 ++ missing17921_17922
abbrev records17920_17922 : List Blob :=
  records17920_17921 ++ records17921_17922
theorem aligned17920_17922 :
    AlignedValid 12 4 missing17920_17922 records17920_17922 :=
  aligned17920_17921.append aligned17921_17922

def missing17922_17923 : List (BitVec (edgeCount 12)) :=
  [missing17922]
abbrev records17922_17923 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17922]
theorem aligned17922_17923 :
    AlignedValid 12 4 missing17922_17923 records17922_17923 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17922
    maskCheck17922 AlignedValid.nil

def missing17923_17924 : List (BitVec (edgeCount 12)) :=
  [missing17923]
abbrev records17923_17924 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17923]
theorem aligned17923_17924 :
    AlignedValid 12 4 missing17923_17924 records17923_17924 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17923
    maskCheck17923 AlignedValid.nil

def missing17922_17924 : List (BitVec (edgeCount 12)) :=
  missing17922_17923 ++ missing17923_17924
abbrev records17922_17924 : List Blob :=
  records17922_17923 ++ records17923_17924
theorem aligned17922_17924 :
    AlignedValid 12 4 missing17922_17924 records17922_17924 :=
  aligned17922_17923.append aligned17923_17924

def missing17920_17924 : List (BitVec (edgeCount 12)) :=
  missing17920_17922 ++ missing17922_17924
abbrev records17920_17924 : List Blob :=
  records17920_17922 ++ records17922_17924
theorem aligned17920_17924 :
    AlignedValid 12 4 missing17920_17924 records17920_17924 :=
  aligned17920_17922.append aligned17922_17924

def missing17924_17925 : List (BitVec (edgeCount 12)) :=
  [missing17924]
abbrev records17924_17925 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17924]
theorem aligned17924_17925 :
    AlignedValid 12 4 missing17924_17925 records17924_17925 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17924
    maskCheck17924 AlignedValid.nil

def missing17925_17926 : List (BitVec (edgeCount 12)) :=
  [missing17925]
abbrev records17925_17926 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17925]
theorem aligned17925_17926 :
    AlignedValid 12 4 missing17925_17926 records17925_17926 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17925
    maskCheck17925 AlignedValid.nil

def missing17924_17926 : List (BitVec (edgeCount 12)) :=
  missing17924_17925 ++ missing17925_17926
abbrev records17924_17926 : List Blob :=
  records17924_17925 ++ records17925_17926
theorem aligned17924_17926 :
    AlignedValid 12 4 missing17924_17926 records17924_17926 :=
  aligned17924_17925.append aligned17925_17926

def missing17926_17927 : List (BitVec (edgeCount 12)) :=
  [missing17926]
abbrev records17926_17927 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17926]
theorem aligned17926_17927 :
    AlignedValid 12 4 missing17926_17927 records17926_17927 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17926
    maskCheck17926 AlignedValid.nil

def missing17927_17928 : List (BitVec (edgeCount 12)) :=
  [missing17927]
abbrev records17927_17928 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17927]
theorem aligned17927_17928 :
    AlignedValid 12 4 missing17927_17928 records17927_17928 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17927
    maskCheck17927 AlignedValid.nil

def missing17926_17928 : List (BitVec (edgeCount 12)) :=
  missing17926_17927 ++ missing17927_17928
abbrev records17926_17928 : List Blob :=
  records17926_17927 ++ records17927_17928
theorem aligned17926_17928 :
    AlignedValid 12 4 missing17926_17928 records17926_17928 :=
  aligned17926_17927.append aligned17927_17928

def missing17924_17928 : List (BitVec (edgeCount 12)) :=
  missing17924_17926 ++ missing17926_17928
abbrev records17924_17928 : List Blob :=
  records17924_17926 ++ records17926_17928
theorem aligned17924_17928 :
    AlignedValid 12 4 missing17924_17928 records17924_17928 :=
  aligned17924_17926.append aligned17926_17928

def missing17920_17928 : List (BitVec (edgeCount 12)) :=
  missing17920_17924 ++ missing17924_17928
abbrev records17920_17928 : List Blob :=
  records17920_17924 ++ records17924_17928
theorem aligned17920_17928 :
    AlignedValid 12 4 missing17920_17928 records17920_17928 :=
  aligned17920_17924.append aligned17924_17928

def missing17928_17929 : List (BitVec (edgeCount 12)) :=
  [missing17928]
abbrev records17928_17929 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17928]
theorem aligned17928_17929 :
    AlignedValid 12 4 missing17928_17929 records17928_17929 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17928
    maskCheck17928 AlignedValid.nil

def missing17929_17930 : List (BitVec (edgeCount 12)) :=
  [missing17929]
abbrev records17929_17930 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17929]
theorem aligned17929_17930 :
    AlignedValid 12 4 missing17929_17930 records17929_17930 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17929
    maskCheck17929 AlignedValid.nil

def missing17928_17930 : List (BitVec (edgeCount 12)) :=
  missing17928_17929 ++ missing17929_17930
abbrev records17928_17930 : List Blob :=
  records17928_17929 ++ records17929_17930
theorem aligned17928_17930 :
    AlignedValid 12 4 missing17928_17930 records17928_17930 :=
  aligned17928_17929.append aligned17929_17930

def missing17930_17931 : List (BitVec (edgeCount 12)) :=
  [missing17930]
abbrev records17930_17931 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17930]
theorem aligned17930_17931 :
    AlignedValid 12 4 missing17930_17931 records17930_17931 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17930
    maskCheck17930 AlignedValid.nil

def missing17931_17932 : List (BitVec (edgeCount 12)) :=
  [missing17931]
abbrev records17931_17932 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17931]
theorem aligned17931_17932 :
    AlignedValid 12 4 missing17931_17932 records17931_17932 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17931
    maskCheck17931 AlignedValid.nil

def missing17930_17932 : List (BitVec (edgeCount 12)) :=
  missing17930_17931 ++ missing17931_17932
abbrev records17930_17932 : List Blob :=
  records17930_17931 ++ records17931_17932
theorem aligned17930_17932 :
    AlignedValid 12 4 missing17930_17932 records17930_17932 :=
  aligned17930_17931.append aligned17931_17932

def missing17928_17932 : List (BitVec (edgeCount 12)) :=
  missing17928_17930 ++ missing17930_17932
abbrev records17928_17932 : List Blob :=
  records17928_17930 ++ records17930_17932
theorem aligned17928_17932 :
    AlignedValid 12 4 missing17928_17932 records17928_17932 :=
  aligned17928_17930.append aligned17930_17932

def missing17932_17933 : List (BitVec (edgeCount 12)) :=
  [missing17932]
abbrev records17932_17933 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17932]
theorem aligned17932_17933 :
    AlignedValid 12 4 missing17932_17933 records17932_17933 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17932
    maskCheck17932 AlignedValid.nil

def missing17933_17934 : List (BitVec (edgeCount 12)) :=
  [missing17933]
abbrev records17933_17934 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17933]
theorem aligned17933_17934 :
    AlignedValid 12 4 missing17933_17934 records17933_17934 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17933
    maskCheck17933 AlignedValid.nil

def missing17932_17934 : List (BitVec (edgeCount 12)) :=
  missing17932_17933 ++ missing17933_17934
abbrev records17932_17934 : List Blob :=
  records17932_17933 ++ records17933_17934
theorem aligned17932_17934 :
    AlignedValid 12 4 missing17932_17934 records17932_17934 :=
  aligned17932_17933.append aligned17933_17934

def missing17934_17935 : List (BitVec (edgeCount 12)) :=
  [missing17934]
abbrev records17934_17935 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17934]
theorem aligned17934_17935 :
    AlignedValid 12 4 missing17934_17935 records17934_17935 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17934
    maskCheck17934 AlignedValid.nil

def missing17935_17936 : List (BitVec (edgeCount 12)) :=
  [missing17935]
abbrev records17935_17936 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17935]
theorem aligned17935_17936 :
    AlignedValid 12 4 missing17935_17936 records17935_17936 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17935
    maskCheck17935 AlignedValid.nil

def missing17934_17936 : List (BitVec (edgeCount 12)) :=
  missing17934_17935 ++ missing17935_17936
abbrev records17934_17936 : List Blob :=
  records17934_17935 ++ records17935_17936
theorem aligned17934_17936 :
    AlignedValid 12 4 missing17934_17936 records17934_17936 :=
  aligned17934_17935.append aligned17935_17936

def missing17932_17936 : List (BitVec (edgeCount 12)) :=
  missing17932_17934 ++ missing17934_17936
abbrev records17932_17936 : List Blob :=
  records17932_17934 ++ records17934_17936
theorem aligned17932_17936 :
    AlignedValid 12 4 missing17932_17936 records17932_17936 :=
  aligned17932_17934.append aligned17934_17936

def missing17928_17936 : List (BitVec (edgeCount 12)) :=
  missing17928_17932 ++ missing17932_17936
abbrev records17928_17936 : List Blob :=
  records17928_17932 ++ records17932_17936
theorem aligned17928_17936 :
    AlignedValid 12 4 missing17928_17936 records17928_17936 :=
  aligned17928_17932.append aligned17932_17936

def missing17920_17936 : List (BitVec (edgeCount 12)) :=
  missing17920_17928 ++ missing17928_17936
abbrev records17920_17936 : List Blob :=
  records17920_17928 ++ records17928_17936
theorem aligned17920_17936 :
    AlignedValid 12 4 missing17920_17936 records17920_17936 :=
  aligned17920_17928.append aligned17928_17936

def missing17936_17937 : List (BitVec (edgeCount 12)) :=
  [missing17936]
abbrev records17936_17937 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17936]
theorem aligned17936_17937 :
    AlignedValid 12 4 missing17936_17937 records17936_17937 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17936
    maskCheck17936 AlignedValid.nil

def missing17937_17938 : List (BitVec (edgeCount 12)) :=
  [missing17937]
abbrev records17937_17938 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17937]
theorem aligned17937_17938 :
    AlignedValid 12 4 missing17937_17938 records17937_17938 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17937
    maskCheck17937 AlignedValid.nil

def missing17936_17938 : List (BitVec (edgeCount 12)) :=
  missing17936_17937 ++ missing17937_17938
abbrev records17936_17938 : List Blob :=
  records17936_17937 ++ records17937_17938
theorem aligned17936_17938 :
    AlignedValid 12 4 missing17936_17938 records17936_17938 :=
  aligned17936_17937.append aligned17937_17938

def missing17938_17939 : List (BitVec (edgeCount 12)) :=
  [missing17938]
abbrev records17938_17939 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17938]
theorem aligned17938_17939 :
    AlignedValid 12 4 missing17938_17939 records17938_17939 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17938
    maskCheck17938 AlignedValid.nil

def missing17939_17940 : List (BitVec (edgeCount 12)) :=
  [missing17939]
abbrev records17939_17940 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17939]
theorem aligned17939_17940 :
    AlignedValid 12 4 missing17939_17940 records17939_17940 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17939
    maskCheck17939 AlignedValid.nil

def missing17938_17940 : List (BitVec (edgeCount 12)) :=
  missing17938_17939 ++ missing17939_17940
abbrev records17938_17940 : List Blob :=
  records17938_17939 ++ records17939_17940
theorem aligned17938_17940 :
    AlignedValid 12 4 missing17938_17940 records17938_17940 :=
  aligned17938_17939.append aligned17939_17940

def missing17936_17940 : List (BitVec (edgeCount 12)) :=
  missing17936_17938 ++ missing17938_17940
abbrev records17936_17940 : List Blob :=
  records17936_17938 ++ records17938_17940
theorem aligned17936_17940 :
    AlignedValid 12 4 missing17936_17940 records17936_17940 :=
  aligned17936_17938.append aligned17938_17940

def missing17940_17941 : List (BitVec (edgeCount 12)) :=
  [missing17940]
abbrev records17940_17941 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17940]
theorem aligned17940_17941 :
    AlignedValid 12 4 missing17940_17941 records17940_17941 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17940
    maskCheck17940 AlignedValid.nil

def missing17941_17942 : List (BitVec (edgeCount 12)) :=
  [missing17941]
abbrev records17941_17942 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17941]
theorem aligned17941_17942 :
    AlignedValid 12 4 missing17941_17942 records17941_17942 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17941
    maskCheck17941 AlignedValid.nil

def missing17940_17942 : List (BitVec (edgeCount 12)) :=
  missing17940_17941 ++ missing17941_17942
abbrev records17940_17942 : List Blob :=
  records17940_17941 ++ records17941_17942
theorem aligned17940_17942 :
    AlignedValid 12 4 missing17940_17942 records17940_17942 :=
  aligned17940_17941.append aligned17941_17942

def missing17942_17943 : List (BitVec (edgeCount 12)) :=
  [missing17942]
abbrev records17942_17943 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17942]
theorem aligned17942_17943 :
    AlignedValid 12 4 missing17942_17943 records17942_17943 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17942
    maskCheck17942 AlignedValid.nil

def missing17943_17944 : List (BitVec (edgeCount 12)) :=
  [missing17943]
abbrev records17943_17944 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17943]
theorem aligned17943_17944 :
    AlignedValid 12 4 missing17943_17944 records17943_17944 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17943
    maskCheck17943 AlignedValid.nil

def missing17942_17944 : List (BitVec (edgeCount 12)) :=
  missing17942_17943 ++ missing17943_17944
abbrev records17942_17944 : List Blob :=
  records17942_17943 ++ records17943_17944
theorem aligned17942_17944 :
    AlignedValid 12 4 missing17942_17944 records17942_17944 :=
  aligned17942_17943.append aligned17943_17944

def missing17940_17944 : List (BitVec (edgeCount 12)) :=
  missing17940_17942 ++ missing17942_17944
abbrev records17940_17944 : List Blob :=
  records17940_17942 ++ records17942_17944
theorem aligned17940_17944 :
    AlignedValid 12 4 missing17940_17944 records17940_17944 :=
  aligned17940_17942.append aligned17942_17944

def missing17936_17944 : List (BitVec (edgeCount 12)) :=
  missing17936_17940 ++ missing17940_17944
abbrev records17936_17944 : List Blob :=
  records17936_17940 ++ records17940_17944
theorem aligned17936_17944 :
    AlignedValid 12 4 missing17936_17944 records17936_17944 :=
  aligned17936_17940.append aligned17940_17944

def missing17944_17945 : List (BitVec (edgeCount 12)) :=
  [missing17944]
abbrev records17944_17945 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17944]
theorem aligned17944_17945 :
    AlignedValid 12 4 missing17944_17945 records17944_17945 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17944
    maskCheck17944 AlignedValid.nil

def missing17945_17946 : List (BitVec (edgeCount 12)) :=
  [missing17945]
abbrev records17945_17946 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17945]
theorem aligned17945_17946 :
    AlignedValid 12 4 missing17945_17946 records17945_17946 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17945
    maskCheck17945 AlignedValid.nil

def missing17944_17946 : List (BitVec (edgeCount 12)) :=
  missing17944_17945 ++ missing17945_17946
abbrev records17944_17946 : List Blob :=
  records17944_17945 ++ records17945_17946
theorem aligned17944_17946 :
    AlignedValid 12 4 missing17944_17946 records17944_17946 :=
  aligned17944_17945.append aligned17945_17946

def missing17946_17947 : List (BitVec (edgeCount 12)) :=
  [missing17946]
abbrev records17946_17947 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17946]
theorem aligned17946_17947 :
    AlignedValid 12 4 missing17946_17947 records17946_17947 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17946
    maskCheck17946 AlignedValid.nil

def missing17947_17948 : List (BitVec (edgeCount 12)) :=
  [missing17947]
abbrev records17947_17948 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17947]
theorem aligned17947_17948 :
    AlignedValid 12 4 missing17947_17948 records17947_17948 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17947
    maskCheck17947 AlignedValid.nil

def missing17946_17948 : List (BitVec (edgeCount 12)) :=
  missing17946_17947 ++ missing17947_17948
abbrev records17946_17948 : List Blob :=
  records17946_17947 ++ records17947_17948
theorem aligned17946_17948 :
    AlignedValid 12 4 missing17946_17948 records17946_17948 :=
  aligned17946_17947.append aligned17947_17948

def missing17944_17948 : List (BitVec (edgeCount 12)) :=
  missing17944_17946 ++ missing17946_17948
abbrev records17944_17948 : List Blob :=
  records17944_17946 ++ records17946_17948
theorem aligned17944_17948 :
    AlignedValid 12 4 missing17944_17948 records17944_17948 :=
  aligned17944_17946.append aligned17946_17948

def missing17948_17949 : List (BitVec (edgeCount 12)) :=
  [missing17948]
abbrev records17948_17949 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17948]
theorem aligned17948_17949 :
    AlignedValid 12 4 missing17948_17949 records17948_17949 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17948
    maskCheck17948 AlignedValid.nil

def missing17949_17950 : List (BitVec (edgeCount 12)) :=
  [missing17949]
abbrev records17949_17950 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17949]
theorem aligned17949_17950 :
    AlignedValid 12 4 missing17949_17950 records17949_17950 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17949
    maskCheck17949 AlignedValid.nil

def missing17948_17950 : List (BitVec (edgeCount 12)) :=
  missing17948_17949 ++ missing17949_17950
abbrev records17948_17950 : List Blob :=
  records17948_17949 ++ records17949_17950
theorem aligned17948_17950 :
    AlignedValid 12 4 missing17948_17950 records17948_17950 :=
  aligned17948_17949.append aligned17949_17950

def missing17950_17951 : List (BitVec (edgeCount 12)) :=
  [missing17950]
abbrev records17950_17951 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17950]
theorem aligned17950_17951 :
    AlignedValid 12 4 missing17950_17951 records17950_17951 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17950
    maskCheck17950 AlignedValid.nil

def missing17951_17952 : List (BitVec (edgeCount 12)) :=
  [missing17951]
abbrev records17951_17952 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17951]
theorem aligned17951_17952 :
    AlignedValid 12 4 missing17951_17952 records17951_17952 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17951
    maskCheck17951 AlignedValid.nil

def missing17950_17952 : List (BitVec (edgeCount 12)) :=
  missing17950_17951 ++ missing17951_17952
abbrev records17950_17952 : List Blob :=
  records17950_17951 ++ records17951_17952
theorem aligned17950_17952 :
    AlignedValid 12 4 missing17950_17952 records17950_17952 :=
  aligned17950_17951.append aligned17951_17952

def missing17948_17952 : List (BitVec (edgeCount 12)) :=
  missing17948_17950 ++ missing17950_17952
abbrev records17948_17952 : List Blob :=
  records17948_17950 ++ records17950_17952
theorem aligned17948_17952 :
    AlignedValid 12 4 missing17948_17952 records17948_17952 :=
  aligned17948_17950.append aligned17950_17952

def missing17944_17952 : List (BitVec (edgeCount 12)) :=
  missing17944_17948 ++ missing17948_17952
abbrev records17944_17952 : List Blob :=
  records17944_17948 ++ records17948_17952
theorem aligned17944_17952 :
    AlignedValid 12 4 missing17944_17952 records17944_17952 :=
  aligned17944_17948.append aligned17948_17952

def missing17936_17952 : List (BitVec (edgeCount 12)) :=
  missing17936_17944 ++ missing17944_17952
abbrev records17936_17952 : List Blob :=
  records17936_17944 ++ records17944_17952
theorem aligned17936_17952 :
    AlignedValid 12 4 missing17936_17952 records17936_17952 :=
  aligned17936_17944.append aligned17944_17952

def missing17920_17952 : List (BitVec (edgeCount 12)) :=
  missing17920_17936 ++ missing17936_17952
abbrev records17920_17952 : List Blob :=
  records17920_17936 ++ records17936_17952
theorem aligned17920_17952 :
    AlignedValid 12 4 missing17920_17952 records17920_17952 :=
  aligned17920_17936.append aligned17936_17952

def missing17952_17953 : List (BitVec (edgeCount 12)) :=
  [missing17952]
abbrev records17952_17953 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17952]
theorem aligned17952_17953 :
    AlignedValid 12 4 missing17952_17953 records17952_17953 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17952
    maskCheck17952 AlignedValid.nil

def missing17953_17954 : List (BitVec (edgeCount 12)) :=
  [missing17953]
abbrev records17953_17954 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17953]
theorem aligned17953_17954 :
    AlignedValid 12 4 missing17953_17954 records17953_17954 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17953
    maskCheck17953 AlignedValid.nil

def missing17952_17954 : List (BitVec (edgeCount 12)) :=
  missing17952_17953 ++ missing17953_17954
abbrev records17952_17954 : List Blob :=
  records17952_17953 ++ records17953_17954
theorem aligned17952_17954 :
    AlignedValid 12 4 missing17952_17954 records17952_17954 :=
  aligned17952_17953.append aligned17953_17954

def missing17954_17955 : List (BitVec (edgeCount 12)) :=
  [missing17954]
abbrev records17954_17955 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17954]
theorem aligned17954_17955 :
    AlignedValid 12 4 missing17954_17955 records17954_17955 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17954
    maskCheck17954 AlignedValid.nil

def missing17955_17956 : List (BitVec (edgeCount 12)) :=
  [missing17955]
abbrev records17955_17956 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17955]
theorem aligned17955_17956 :
    AlignedValid 12 4 missing17955_17956 records17955_17956 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17955
    maskCheck17955 AlignedValid.nil

def missing17954_17956 : List (BitVec (edgeCount 12)) :=
  missing17954_17955 ++ missing17955_17956
abbrev records17954_17956 : List Blob :=
  records17954_17955 ++ records17955_17956
theorem aligned17954_17956 :
    AlignedValid 12 4 missing17954_17956 records17954_17956 :=
  aligned17954_17955.append aligned17955_17956

def missing17952_17956 : List (BitVec (edgeCount 12)) :=
  missing17952_17954 ++ missing17954_17956
abbrev records17952_17956 : List Blob :=
  records17952_17954 ++ records17954_17956
theorem aligned17952_17956 :
    AlignedValid 12 4 missing17952_17956 records17952_17956 :=
  aligned17952_17954.append aligned17954_17956

def missing17956_17957 : List (BitVec (edgeCount 12)) :=
  [missing17956]
abbrev records17956_17957 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17956]
theorem aligned17956_17957 :
    AlignedValid 12 4 missing17956_17957 records17956_17957 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17956
    maskCheck17956 AlignedValid.nil

def missing17957_17958 : List (BitVec (edgeCount 12)) :=
  [missing17957]
abbrev records17957_17958 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17957]
theorem aligned17957_17958 :
    AlignedValid 12 4 missing17957_17958 records17957_17958 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17957
    maskCheck17957 AlignedValid.nil

def missing17956_17958 : List (BitVec (edgeCount 12)) :=
  missing17956_17957 ++ missing17957_17958
abbrev records17956_17958 : List Blob :=
  records17956_17957 ++ records17957_17958
theorem aligned17956_17958 :
    AlignedValid 12 4 missing17956_17958 records17956_17958 :=
  aligned17956_17957.append aligned17957_17958

def missing17958_17959 : List (BitVec (edgeCount 12)) :=
  [missing17958]
abbrev records17958_17959 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17958]
theorem aligned17958_17959 :
    AlignedValid 12 4 missing17958_17959 records17958_17959 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17958
    maskCheck17958 AlignedValid.nil

def missing17959_17960 : List (BitVec (edgeCount 12)) :=
  [missing17959]
abbrev records17959_17960 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17959]
theorem aligned17959_17960 :
    AlignedValid 12 4 missing17959_17960 records17959_17960 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17959
    maskCheck17959 AlignedValid.nil

def missing17958_17960 : List (BitVec (edgeCount 12)) :=
  missing17958_17959 ++ missing17959_17960
abbrev records17958_17960 : List Blob :=
  records17958_17959 ++ records17959_17960
theorem aligned17958_17960 :
    AlignedValid 12 4 missing17958_17960 records17958_17960 :=
  aligned17958_17959.append aligned17959_17960

def missing17956_17960 : List (BitVec (edgeCount 12)) :=
  missing17956_17958 ++ missing17958_17960
abbrev records17956_17960 : List Blob :=
  records17956_17958 ++ records17958_17960
theorem aligned17956_17960 :
    AlignedValid 12 4 missing17956_17960 records17956_17960 :=
  aligned17956_17958.append aligned17958_17960

def missing17952_17960 : List (BitVec (edgeCount 12)) :=
  missing17952_17956 ++ missing17956_17960
abbrev records17952_17960 : List Blob :=
  records17952_17956 ++ records17956_17960
theorem aligned17952_17960 :
    AlignedValid 12 4 missing17952_17960 records17952_17960 :=
  aligned17952_17956.append aligned17956_17960

def missing17960_17961 : List (BitVec (edgeCount 12)) :=
  [missing17960]
abbrev records17960_17961 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17960]
theorem aligned17960_17961 :
    AlignedValid 12 4 missing17960_17961 records17960_17961 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17960
    maskCheck17960 AlignedValid.nil

def missing17961_17962 : List (BitVec (edgeCount 12)) :=
  [missing17961]
abbrev records17961_17962 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17961]
theorem aligned17961_17962 :
    AlignedValid 12 4 missing17961_17962 records17961_17962 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17961
    maskCheck17961 AlignedValid.nil

def missing17960_17962 : List (BitVec (edgeCount 12)) :=
  missing17960_17961 ++ missing17961_17962
abbrev records17960_17962 : List Blob :=
  records17960_17961 ++ records17961_17962
theorem aligned17960_17962 :
    AlignedValid 12 4 missing17960_17962 records17960_17962 :=
  aligned17960_17961.append aligned17961_17962

def missing17962_17963 : List (BitVec (edgeCount 12)) :=
  [missing17962]
abbrev records17962_17963 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17962]
theorem aligned17962_17963 :
    AlignedValid 12 4 missing17962_17963 records17962_17963 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17962
    maskCheck17962 AlignedValid.nil

def missing17963_17964 : List (BitVec (edgeCount 12)) :=
  [missing17963]
abbrev records17963_17964 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17963]
theorem aligned17963_17964 :
    AlignedValid 12 4 missing17963_17964 records17963_17964 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17963
    maskCheck17963 AlignedValid.nil

def missing17962_17964 : List (BitVec (edgeCount 12)) :=
  missing17962_17963 ++ missing17963_17964
abbrev records17962_17964 : List Blob :=
  records17962_17963 ++ records17963_17964
theorem aligned17962_17964 :
    AlignedValid 12 4 missing17962_17964 records17962_17964 :=
  aligned17962_17963.append aligned17963_17964

def missing17960_17964 : List (BitVec (edgeCount 12)) :=
  missing17960_17962 ++ missing17962_17964
abbrev records17960_17964 : List Blob :=
  records17960_17962 ++ records17962_17964
theorem aligned17960_17964 :
    AlignedValid 12 4 missing17960_17964 records17960_17964 :=
  aligned17960_17962.append aligned17962_17964

def missing17964_17965 : List (BitVec (edgeCount 12)) :=
  [missing17964]
abbrev records17964_17965 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17964]
theorem aligned17964_17965 :
    AlignedValid 12 4 missing17964_17965 records17964_17965 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17964
    maskCheck17964 AlignedValid.nil

def missing17965_17966 : List (BitVec (edgeCount 12)) :=
  [missing17965]
abbrev records17965_17966 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17965]
theorem aligned17965_17966 :
    AlignedValid 12 4 missing17965_17966 records17965_17966 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17965
    maskCheck17965 AlignedValid.nil

def missing17964_17966 : List (BitVec (edgeCount 12)) :=
  missing17964_17965 ++ missing17965_17966
abbrev records17964_17966 : List Blob :=
  records17964_17965 ++ records17965_17966
theorem aligned17964_17966 :
    AlignedValid 12 4 missing17964_17966 records17964_17966 :=
  aligned17964_17965.append aligned17965_17966

def missing17966_17967 : List (BitVec (edgeCount 12)) :=
  [missing17966]
abbrev records17966_17967 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17966]
theorem aligned17966_17967 :
    AlignedValid 12 4 missing17966_17967 records17966_17967 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17966
    maskCheck17966 AlignedValid.nil

def missing17967_17968 : List (BitVec (edgeCount 12)) :=
  [missing17967]
abbrev records17967_17968 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17967]
theorem aligned17967_17968 :
    AlignedValid 12 4 missing17967_17968 records17967_17968 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17967
    maskCheck17967 AlignedValid.nil

def missing17966_17968 : List (BitVec (edgeCount 12)) :=
  missing17966_17967 ++ missing17967_17968
abbrev records17966_17968 : List Blob :=
  records17966_17967 ++ records17967_17968
theorem aligned17966_17968 :
    AlignedValid 12 4 missing17966_17968 records17966_17968 :=
  aligned17966_17967.append aligned17967_17968

def missing17964_17968 : List (BitVec (edgeCount 12)) :=
  missing17964_17966 ++ missing17966_17968
abbrev records17964_17968 : List Blob :=
  records17964_17966 ++ records17966_17968
theorem aligned17964_17968 :
    AlignedValid 12 4 missing17964_17968 records17964_17968 :=
  aligned17964_17966.append aligned17966_17968

def missing17960_17968 : List (BitVec (edgeCount 12)) :=
  missing17960_17964 ++ missing17964_17968
abbrev records17960_17968 : List Blob :=
  records17960_17964 ++ records17964_17968
theorem aligned17960_17968 :
    AlignedValid 12 4 missing17960_17968 records17960_17968 :=
  aligned17960_17964.append aligned17964_17968

def missing17952_17968 : List (BitVec (edgeCount 12)) :=
  missing17952_17960 ++ missing17960_17968
abbrev records17952_17968 : List Blob :=
  records17952_17960 ++ records17960_17968
theorem aligned17952_17968 :
    AlignedValid 12 4 missing17952_17968 records17952_17968 :=
  aligned17952_17960.append aligned17960_17968

def missing17968_17969 : List (BitVec (edgeCount 12)) :=
  [missing17968]
abbrev records17968_17969 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17968]
theorem aligned17968_17969 :
    AlignedValid 12 4 missing17968_17969 records17968_17969 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17968
    maskCheck17968 AlignedValid.nil

def missing17969_17970 : List (BitVec (edgeCount 12)) :=
  [missing17969]
abbrev records17969_17970 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17969]
theorem aligned17969_17970 :
    AlignedValid 12 4 missing17969_17970 records17969_17970 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17969
    maskCheck17969 AlignedValid.nil

def missing17968_17970 : List (BitVec (edgeCount 12)) :=
  missing17968_17969 ++ missing17969_17970
abbrev records17968_17970 : List Blob :=
  records17968_17969 ++ records17969_17970
theorem aligned17968_17970 :
    AlignedValid 12 4 missing17968_17970 records17968_17970 :=
  aligned17968_17969.append aligned17969_17970

def missing17970_17971 : List (BitVec (edgeCount 12)) :=
  [missing17970]
abbrev records17970_17971 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17970]
theorem aligned17970_17971 :
    AlignedValid 12 4 missing17970_17971 records17970_17971 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17970
    maskCheck17970 AlignedValid.nil

def missing17971_17972 : List (BitVec (edgeCount 12)) :=
  [missing17971]
abbrev records17971_17972 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17971]
theorem aligned17971_17972 :
    AlignedValid 12 4 missing17971_17972 records17971_17972 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17971
    maskCheck17971 AlignedValid.nil

def missing17970_17972 : List (BitVec (edgeCount 12)) :=
  missing17970_17971 ++ missing17971_17972
abbrev records17970_17972 : List Blob :=
  records17970_17971 ++ records17971_17972
theorem aligned17970_17972 :
    AlignedValid 12 4 missing17970_17972 records17970_17972 :=
  aligned17970_17971.append aligned17971_17972

def missing17968_17972 : List (BitVec (edgeCount 12)) :=
  missing17968_17970 ++ missing17970_17972
abbrev records17968_17972 : List Blob :=
  records17968_17970 ++ records17970_17972
theorem aligned17968_17972 :
    AlignedValid 12 4 missing17968_17972 records17968_17972 :=
  aligned17968_17970.append aligned17970_17972

def missing17972_17973 : List (BitVec (edgeCount 12)) :=
  [missing17972]
abbrev records17972_17973 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17972]
theorem aligned17972_17973 :
    AlignedValid 12 4 missing17972_17973 records17972_17973 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17972
    maskCheck17972 AlignedValid.nil

def missing17973_17974 : List (BitVec (edgeCount 12)) :=
  [missing17973]
abbrev records17973_17974 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17973]
theorem aligned17973_17974 :
    AlignedValid 12 4 missing17973_17974 records17973_17974 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17973
    maskCheck17973 AlignedValid.nil

def missing17972_17974 : List (BitVec (edgeCount 12)) :=
  missing17972_17973 ++ missing17973_17974
abbrev records17972_17974 : List Blob :=
  records17972_17973 ++ records17973_17974
theorem aligned17972_17974 :
    AlignedValid 12 4 missing17972_17974 records17972_17974 :=
  aligned17972_17973.append aligned17973_17974

def missing17974_17975 : List (BitVec (edgeCount 12)) :=
  [missing17974]
abbrev records17974_17975 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17974]
theorem aligned17974_17975 :
    AlignedValid 12 4 missing17974_17975 records17974_17975 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17974
    maskCheck17974 AlignedValid.nil

def missing17975_17976 : List (BitVec (edgeCount 12)) :=
  [missing17975]
abbrev records17975_17976 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17975]
theorem aligned17975_17976 :
    AlignedValid 12 4 missing17975_17976 records17975_17976 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17975
    maskCheck17975 AlignedValid.nil

def missing17974_17976 : List (BitVec (edgeCount 12)) :=
  missing17974_17975 ++ missing17975_17976
abbrev records17974_17976 : List Blob :=
  records17974_17975 ++ records17975_17976
theorem aligned17974_17976 :
    AlignedValid 12 4 missing17974_17976 records17974_17976 :=
  aligned17974_17975.append aligned17975_17976

def missing17972_17976 : List (BitVec (edgeCount 12)) :=
  missing17972_17974 ++ missing17974_17976
abbrev records17972_17976 : List Blob :=
  records17972_17974 ++ records17974_17976
theorem aligned17972_17976 :
    AlignedValid 12 4 missing17972_17976 records17972_17976 :=
  aligned17972_17974.append aligned17974_17976

def missing17968_17976 : List (BitVec (edgeCount 12)) :=
  missing17968_17972 ++ missing17972_17976
abbrev records17968_17976 : List Blob :=
  records17968_17972 ++ records17972_17976
theorem aligned17968_17976 :
    AlignedValid 12 4 missing17968_17976 records17968_17976 :=
  aligned17968_17972.append aligned17972_17976

def missing17976_17977 : List (BitVec (edgeCount 12)) :=
  [missing17976]
abbrev records17976_17977 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17976]
theorem aligned17976_17977 :
    AlignedValid 12 4 missing17976_17977 records17976_17977 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17976
    maskCheck17976 AlignedValid.nil

def missing17977_17978 : List (BitVec (edgeCount 12)) :=
  [missing17977]
abbrev records17977_17978 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17977]
theorem aligned17977_17978 :
    AlignedValid 12 4 missing17977_17978 records17977_17978 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17977
    maskCheck17977 AlignedValid.nil

def missing17976_17978 : List (BitVec (edgeCount 12)) :=
  missing17976_17977 ++ missing17977_17978
abbrev records17976_17978 : List Blob :=
  records17976_17977 ++ records17977_17978
theorem aligned17976_17978 :
    AlignedValid 12 4 missing17976_17978 records17976_17978 :=
  aligned17976_17977.append aligned17977_17978

def missing17978_17979 : List (BitVec (edgeCount 12)) :=
  [missing17978]
abbrev records17978_17979 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17978]
theorem aligned17978_17979 :
    AlignedValid 12 4 missing17978_17979 records17978_17979 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17978
    maskCheck17978 AlignedValid.nil

def missing17979_17980 : List (BitVec (edgeCount 12)) :=
  [missing17979]
abbrev records17979_17980 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17979]
theorem aligned17979_17980 :
    AlignedValid 12 4 missing17979_17980 records17979_17980 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17979
    maskCheck17979 AlignedValid.nil

def missing17978_17980 : List (BitVec (edgeCount 12)) :=
  missing17978_17979 ++ missing17979_17980
abbrev records17978_17980 : List Blob :=
  records17978_17979 ++ records17979_17980
theorem aligned17978_17980 :
    AlignedValid 12 4 missing17978_17980 records17978_17980 :=
  aligned17978_17979.append aligned17979_17980

def missing17976_17980 : List (BitVec (edgeCount 12)) :=
  missing17976_17978 ++ missing17978_17980
abbrev records17976_17980 : List Blob :=
  records17976_17978 ++ records17978_17980
theorem aligned17976_17980 :
    AlignedValid 12 4 missing17976_17980 records17976_17980 :=
  aligned17976_17978.append aligned17978_17980

def missing17980_17981 : List (BitVec (edgeCount 12)) :=
  [missing17980]
abbrev records17980_17981 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17980]
theorem aligned17980_17981 :
    AlignedValid 12 4 missing17980_17981 records17980_17981 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17980
    maskCheck17980 AlignedValid.nil

def missing17981_17982 : List (BitVec (edgeCount 12)) :=
  [missing17981]
abbrev records17981_17982 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17981]
theorem aligned17981_17982 :
    AlignedValid 12 4 missing17981_17982 records17981_17982 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17981
    maskCheck17981 AlignedValid.nil

def missing17980_17982 : List (BitVec (edgeCount 12)) :=
  missing17980_17981 ++ missing17981_17982
abbrev records17980_17982 : List Blob :=
  records17980_17981 ++ records17981_17982
theorem aligned17980_17982 :
    AlignedValid 12 4 missing17980_17982 records17980_17982 :=
  aligned17980_17981.append aligned17981_17982

def missing17982_17983 : List (BitVec (edgeCount 12)) :=
  [missing17982]
abbrev records17982_17983 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17982]
theorem aligned17982_17983 :
    AlignedValid 12 4 missing17982_17983 records17982_17983 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17982
    maskCheck17982 AlignedValid.nil

def missing17983_17984 : List (BitVec (edgeCount 12)) :=
  [missing17983]
abbrev records17983_17984 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17983]
theorem aligned17983_17984 :
    AlignedValid 12 4 missing17983_17984 records17983_17984 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17983
    maskCheck17983 AlignedValid.nil

def missing17982_17984 : List (BitVec (edgeCount 12)) :=
  missing17982_17983 ++ missing17983_17984
abbrev records17982_17984 : List Blob :=
  records17982_17983 ++ records17983_17984
theorem aligned17982_17984 :
    AlignedValid 12 4 missing17982_17984 records17982_17984 :=
  aligned17982_17983.append aligned17983_17984

def missing17980_17984 : List (BitVec (edgeCount 12)) :=
  missing17980_17982 ++ missing17982_17984
abbrev records17980_17984 : List Blob :=
  records17980_17982 ++ records17982_17984
theorem aligned17980_17984 :
    AlignedValid 12 4 missing17980_17984 records17980_17984 :=
  aligned17980_17982.append aligned17982_17984

def missing17976_17984 : List (BitVec (edgeCount 12)) :=
  missing17976_17980 ++ missing17980_17984
abbrev records17976_17984 : List Blob :=
  records17976_17980 ++ records17980_17984
theorem aligned17976_17984 :
    AlignedValid 12 4 missing17976_17984 records17976_17984 :=
  aligned17976_17980.append aligned17980_17984

def missing17968_17984 : List (BitVec (edgeCount 12)) :=
  missing17968_17976 ++ missing17976_17984
abbrev records17968_17984 : List Blob :=
  records17968_17976 ++ records17976_17984
theorem aligned17968_17984 :
    AlignedValid 12 4 missing17968_17984 records17968_17984 :=
  aligned17968_17976.append aligned17976_17984

def missing17952_17984 : List (BitVec (edgeCount 12)) :=
  missing17952_17968 ++ missing17968_17984
abbrev records17952_17984 : List Blob :=
  records17952_17968 ++ records17968_17984
theorem aligned17952_17984 :
    AlignedValid 12 4 missing17952_17984 records17952_17984 :=
  aligned17952_17968.append aligned17968_17984

def missing17920_17984 : List (BitVec (edgeCount 12)) :=
  missing17920_17952 ++ missing17952_17984
abbrev records17920_17984 : List Blob :=
  records17920_17952 ++ records17952_17984
theorem aligned17920_17984 :
    AlignedValid 12 4 missing17920_17984 records17920_17984 :=
  aligned17920_17952.append aligned17952_17984

def missing17984_17985 : List (BitVec (edgeCount 12)) :=
  [missing17984]
abbrev records17984_17985 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17984]
theorem aligned17984_17985 :
    AlignedValid 12 4 missing17984_17985 records17984_17985 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17984
    maskCheck17984 AlignedValid.nil

def missing17985_17986 : List (BitVec (edgeCount 12)) :=
  [missing17985]
abbrev records17985_17986 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17985]
theorem aligned17985_17986 :
    AlignedValid 12 4 missing17985_17986 records17985_17986 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17985
    maskCheck17985 AlignedValid.nil

def missing17984_17986 : List (BitVec (edgeCount 12)) :=
  missing17984_17985 ++ missing17985_17986
abbrev records17984_17986 : List Blob :=
  records17984_17985 ++ records17985_17986
theorem aligned17984_17986 :
    AlignedValid 12 4 missing17984_17986 records17984_17986 :=
  aligned17984_17985.append aligned17985_17986

def missing17986_17987 : List (BitVec (edgeCount 12)) :=
  [missing17986]
abbrev records17986_17987 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17986]
theorem aligned17986_17987 :
    AlignedValid 12 4 missing17986_17987 records17986_17987 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17986
    maskCheck17986 AlignedValid.nil

def missing17987_17988 : List (BitVec (edgeCount 12)) :=
  [missing17987]
abbrev records17987_17988 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17987]
theorem aligned17987_17988 :
    AlignedValid 12 4 missing17987_17988 records17987_17988 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17987
    maskCheck17987 AlignedValid.nil

def missing17986_17988 : List (BitVec (edgeCount 12)) :=
  missing17986_17987 ++ missing17987_17988
abbrev records17986_17988 : List Blob :=
  records17986_17987 ++ records17987_17988
theorem aligned17986_17988 :
    AlignedValid 12 4 missing17986_17988 records17986_17988 :=
  aligned17986_17987.append aligned17987_17988

def missing17984_17988 : List (BitVec (edgeCount 12)) :=
  missing17984_17986 ++ missing17986_17988
abbrev records17984_17988 : List Blob :=
  records17984_17986 ++ records17986_17988
theorem aligned17984_17988 :
    AlignedValid 12 4 missing17984_17988 records17984_17988 :=
  aligned17984_17986.append aligned17986_17988

def missing17988_17989 : List (BitVec (edgeCount 12)) :=
  [missing17988]
abbrev records17988_17989 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17988]
theorem aligned17988_17989 :
    AlignedValid 12 4 missing17988_17989 records17988_17989 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17988
    maskCheck17988 AlignedValid.nil

def missing17989_17990 : List (BitVec (edgeCount 12)) :=
  [missing17989]
abbrev records17989_17990 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17989]
theorem aligned17989_17990 :
    AlignedValid 12 4 missing17989_17990 records17989_17990 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17989
    maskCheck17989 AlignedValid.nil

def missing17988_17990 : List (BitVec (edgeCount 12)) :=
  missing17988_17989 ++ missing17989_17990
abbrev records17988_17990 : List Blob :=
  records17988_17989 ++ records17989_17990
theorem aligned17988_17990 :
    AlignedValid 12 4 missing17988_17990 records17988_17990 :=
  aligned17988_17989.append aligned17989_17990

def missing17990_17991 : List (BitVec (edgeCount 12)) :=
  [missing17990]
abbrev records17990_17991 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17990]
theorem aligned17990_17991 :
    AlignedValid 12 4 missing17990_17991 records17990_17991 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17990
    maskCheck17990 AlignedValid.nil

def missing17991_17992 : List (BitVec (edgeCount 12)) :=
  [missing17991]
abbrev records17991_17992 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17991]
theorem aligned17991_17992 :
    AlignedValid 12 4 missing17991_17992 records17991_17992 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17991
    maskCheck17991 AlignedValid.nil

def missing17990_17992 : List (BitVec (edgeCount 12)) :=
  missing17990_17991 ++ missing17991_17992
abbrev records17990_17992 : List Blob :=
  records17990_17991 ++ records17991_17992
theorem aligned17990_17992 :
    AlignedValid 12 4 missing17990_17992 records17990_17992 :=
  aligned17990_17991.append aligned17991_17992

def missing17988_17992 : List (BitVec (edgeCount 12)) :=
  missing17988_17990 ++ missing17990_17992
abbrev records17988_17992 : List Blob :=
  records17988_17990 ++ records17990_17992
theorem aligned17988_17992 :
    AlignedValid 12 4 missing17988_17992 records17988_17992 :=
  aligned17988_17990.append aligned17990_17992

def missing17984_17992 : List (BitVec (edgeCount 12)) :=
  missing17984_17988 ++ missing17988_17992
abbrev records17984_17992 : List Blob :=
  records17984_17988 ++ records17988_17992
theorem aligned17984_17992 :
    AlignedValid 12 4 missing17984_17992 records17984_17992 :=
  aligned17984_17988.append aligned17988_17992

def missing17992_17993 : List (BitVec (edgeCount 12)) :=
  [missing17992]
abbrev records17992_17993 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17992]
theorem aligned17992_17993 :
    AlignedValid 12 4 missing17992_17993 records17992_17993 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17992
    maskCheck17992 AlignedValid.nil

def missing17993_17994 : List (BitVec (edgeCount 12)) :=
  [missing17993]
abbrev records17993_17994 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17993]
theorem aligned17993_17994 :
    AlignedValid 12 4 missing17993_17994 records17993_17994 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17993
    maskCheck17993 AlignedValid.nil

def missing17992_17994 : List (BitVec (edgeCount 12)) :=
  missing17992_17993 ++ missing17993_17994
abbrev records17992_17994 : List Blob :=
  records17992_17993 ++ records17993_17994
theorem aligned17992_17994 :
    AlignedValid 12 4 missing17992_17994 records17992_17994 :=
  aligned17992_17993.append aligned17993_17994

def missing17994_17995 : List (BitVec (edgeCount 12)) :=
  [missing17994]
abbrev records17994_17995 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17994]
theorem aligned17994_17995 :
    AlignedValid 12 4 missing17994_17995 records17994_17995 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17994
    maskCheck17994 AlignedValid.nil

def missing17995_17996 : List (BitVec (edgeCount 12)) :=
  [missing17995]
abbrev records17995_17996 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17995]
theorem aligned17995_17996 :
    AlignedValid 12 4 missing17995_17996 records17995_17996 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17995
    maskCheck17995 AlignedValid.nil

def missing17994_17996 : List (BitVec (edgeCount 12)) :=
  missing17994_17995 ++ missing17995_17996
abbrev records17994_17996 : List Blob :=
  records17994_17995 ++ records17995_17996
theorem aligned17994_17996 :
    AlignedValid 12 4 missing17994_17996 records17994_17996 :=
  aligned17994_17995.append aligned17995_17996

def missing17992_17996 : List (BitVec (edgeCount 12)) :=
  missing17992_17994 ++ missing17994_17996
abbrev records17992_17996 : List Blob :=
  records17992_17994 ++ records17994_17996
theorem aligned17992_17996 :
    AlignedValid 12 4 missing17992_17996 records17992_17996 :=
  aligned17992_17994.append aligned17994_17996

def missing17996_17997 : List (BitVec (edgeCount 12)) :=
  [missing17996]
abbrev records17996_17997 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17996]
theorem aligned17996_17997 :
    AlignedValid 12 4 missing17996_17997 records17996_17997 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17996
    maskCheck17996 AlignedValid.nil

def missing17997_17998 : List (BitVec (edgeCount 12)) :=
  [missing17997]
abbrev records17997_17998 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17997]
theorem aligned17997_17998 :
    AlignedValid 12 4 missing17997_17998 records17997_17998 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17997
    maskCheck17997 AlignedValid.nil

def missing17996_17998 : List (BitVec (edgeCount 12)) :=
  missing17996_17997 ++ missing17997_17998
abbrev records17996_17998 : List Blob :=
  records17996_17997 ++ records17997_17998
theorem aligned17996_17998 :
    AlignedValid 12 4 missing17996_17998 records17996_17998 :=
  aligned17996_17997.append aligned17997_17998

def missing17998_17999 : List (BitVec (edgeCount 12)) :=
  [missing17998]
abbrev records17998_17999 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17998]
theorem aligned17998_17999 :
    AlignedValid 12 4 missing17998_17999 records17998_17999 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17998
    maskCheck17998 AlignedValid.nil

def missing17999_18000 : List (BitVec (edgeCount 12)) :=
  [missing17999]
abbrev records17999_18000 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record17999]
theorem aligned17999_18000 :
    AlignedValid 12 4 missing17999_18000 records17999_18000 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check17999
    maskCheck17999 AlignedValid.nil

def missing17998_18000 : List (BitVec (edgeCount 12)) :=
  missing17998_17999 ++ missing17999_18000
abbrev records17998_18000 : List Blob :=
  records17998_17999 ++ records17999_18000
theorem aligned17998_18000 :
    AlignedValid 12 4 missing17998_18000 records17998_18000 :=
  aligned17998_17999.append aligned17999_18000

def missing17996_18000 : List (BitVec (edgeCount 12)) :=
  missing17996_17998 ++ missing17998_18000
abbrev records17996_18000 : List Blob :=
  records17996_17998 ++ records17998_18000
theorem aligned17996_18000 :
    AlignedValid 12 4 missing17996_18000 records17996_18000 :=
  aligned17996_17998.append aligned17998_18000

def missing17992_18000 : List (BitVec (edgeCount 12)) :=
  missing17992_17996 ++ missing17996_18000
abbrev records17992_18000 : List Blob :=
  records17992_17996 ++ records17996_18000
theorem aligned17992_18000 :
    AlignedValid 12 4 missing17992_18000 records17992_18000 :=
  aligned17992_17996.append aligned17996_18000

def missing17984_18000 : List (BitVec (edgeCount 12)) :=
  missing17984_17992 ++ missing17992_18000
abbrev records17984_18000 : List Blob :=
  records17984_17992 ++ records17992_18000
theorem aligned17984_18000 :
    AlignedValid 12 4 missing17984_18000 records17984_18000 :=
  aligned17984_17992.append aligned17992_18000

def missing18000_18001 : List (BitVec (edgeCount 12)) :=
  [missing18000]
abbrev records18000_18001 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18000]
theorem aligned18000_18001 :
    AlignedValid 12 4 missing18000_18001 records18000_18001 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18000
    maskCheck18000 AlignedValid.nil

def missing18001_18002 : List (BitVec (edgeCount 12)) :=
  [missing18001]
abbrev records18001_18002 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18001]
theorem aligned18001_18002 :
    AlignedValid 12 4 missing18001_18002 records18001_18002 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18001
    maskCheck18001 AlignedValid.nil

def missing18000_18002 : List (BitVec (edgeCount 12)) :=
  missing18000_18001 ++ missing18001_18002
abbrev records18000_18002 : List Blob :=
  records18000_18001 ++ records18001_18002
theorem aligned18000_18002 :
    AlignedValid 12 4 missing18000_18002 records18000_18002 :=
  aligned18000_18001.append aligned18001_18002

def missing18002_18003 : List (BitVec (edgeCount 12)) :=
  [missing18002]
abbrev records18002_18003 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18002]
theorem aligned18002_18003 :
    AlignedValid 12 4 missing18002_18003 records18002_18003 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18002
    maskCheck18002 AlignedValid.nil

def missing18003_18004 : List (BitVec (edgeCount 12)) :=
  [missing18003]
abbrev records18003_18004 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18003]
theorem aligned18003_18004 :
    AlignedValid 12 4 missing18003_18004 records18003_18004 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18003
    maskCheck18003 AlignedValid.nil

def missing18002_18004 : List (BitVec (edgeCount 12)) :=
  missing18002_18003 ++ missing18003_18004
abbrev records18002_18004 : List Blob :=
  records18002_18003 ++ records18003_18004
theorem aligned18002_18004 :
    AlignedValid 12 4 missing18002_18004 records18002_18004 :=
  aligned18002_18003.append aligned18003_18004

def missing18000_18004 : List (BitVec (edgeCount 12)) :=
  missing18000_18002 ++ missing18002_18004
abbrev records18000_18004 : List Blob :=
  records18000_18002 ++ records18002_18004
theorem aligned18000_18004 :
    AlignedValid 12 4 missing18000_18004 records18000_18004 :=
  aligned18000_18002.append aligned18002_18004

def missing18004_18005 : List (BitVec (edgeCount 12)) :=
  [missing18004]
abbrev records18004_18005 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18004]
theorem aligned18004_18005 :
    AlignedValid 12 4 missing18004_18005 records18004_18005 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18004
    maskCheck18004 AlignedValid.nil

def missing18005_18006 : List (BitVec (edgeCount 12)) :=
  [missing18005]
abbrev records18005_18006 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18005]
theorem aligned18005_18006 :
    AlignedValid 12 4 missing18005_18006 records18005_18006 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18005
    maskCheck18005 AlignedValid.nil

def missing18004_18006 : List (BitVec (edgeCount 12)) :=
  missing18004_18005 ++ missing18005_18006
abbrev records18004_18006 : List Blob :=
  records18004_18005 ++ records18005_18006
theorem aligned18004_18006 :
    AlignedValid 12 4 missing18004_18006 records18004_18006 :=
  aligned18004_18005.append aligned18005_18006

def missing18006_18007 : List (BitVec (edgeCount 12)) :=
  [missing18006]
abbrev records18006_18007 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18006]
theorem aligned18006_18007 :
    AlignedValid 12 4 missing18006_18007 records18006_18007 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18006
    maskCheck18006 AlignedValid.nil

def missing18007_18008 : List (BitVec (edgeCount 12)) :=
  [missing18007]
abbrev records18007_18008 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18007]
theorem aligned18007_18008 :
    AlignedValid 12 4 missing18007_18008 records18007_18008 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18007
    maskCheck18007 AlignedValid.nil

def missing18006_18008 : List (BitVec (edgeCount 12)) :=
  missing18006_18007 ++ missing18007_18008
abbrev records18006_18008 : List Blob :=
  records18006_18007 ++ records18007_18008
theorem aligned18006_18008 :
    AlignedValid 12 4 missing18006_18008 records18006_18008 :=
  aligned18006_18007.append aligned18007_18008

def missing18004_18008 : List (BitVec (edgeCount 12)) :=
  missing18004_18006 ++ missing18006_18008
abbrev records18004_18008 : List Blob :=
  records18004_18006 ++ records18006_18008
theorem aligned18004_18008 :
    AlignedValid 12 4 missing18004_18008 records18004_18008 :=
  aligned18004_18006.append aligned18006_18008

def missing18000_18008 : List (BitVec (edgeCount 12)) :=
  missing18000_18004 ++ missing18004_18008
abbrev records18000_18008 : List Blob :=
  records18000_18004 ++ records18004_18008
theorem aligned18000_18008 :
    AlignedValid 12 4 missing18000_18008 records18000_18008 :=
  aligned18000_18004.append aligned18004_18008

def missing18008_18009 : List (BitVec (edgeCount 12)) :=
  [missing18008]
abbrev records18008_18009 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18008]
theorem aligned18008_18009 :
    AlignedValid 12 4 missing18008_18009 records18008_18009 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18008
    maskCheck18008 AlignedValid.nil

def missing18009_18010 : List (BitVec (edgeCount 12)) :=
  [missing18009]
abbrev records18009_18010 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18009]
theorem aligned18009_18010 :
    AlignedValid 12 4 missing18009_18010 records18009_18010 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18009
    maskCheck18009 AlignedValid.nil

def missing18008_18010 : List (BitVec (edgeCount 12)) :=
  missing18008_18009 ++ missing18009_18010
abbrev records18008_18010 : List Blob :=
  records18008_18009 ++ records18009_18010
theorem aligned18008_18010 :
    AlignedValid 12 4 missing18008_18010 records18008_18010 :=
  aligned18008_18009.append aligned18009_18010

def missing18010_18011 : List (BitVec (edgeCount 12)) :=
  [missing18010]
abbrev records18010_18011 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18010]
theorem aligned18010_18011 :
    AlignedValid 12 4 missing18010_18011 records18010_18011 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18010
    maskCheck18010 AlignedValid.nil

def missing18011_18012 : List (BitVec (edgeCount 12)) :=
  [missing18011]
abbrev records18011_18012 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18011]
theorem aligned18011_18012 :
    AlignedValid 12 4 missing18011_18012 records18011_18012 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18011
    maskCheck18011 AlignedValid.nil

def missing18010_18012 : List (BitVec (edgeCount 12)) :=
  missing18010_18011 ++ missing18011_18012
abbrev records18010_18012 : List Blob :=
  records18010_18011 ++ records18011_18012
theorem aligned18010_18012 :
    AlignedValid 12 4 missing18010_18012 records18010_18012 :=
  aligned18010_18011.append aligned18011_18012

def missing18008_18012 : List (BitVec (edgeCount 12)) :=
  missing18008_18010 ++ missing18010_18012
abbrev records18008_18012 : List Blob :=
  records18008_18010 ++ records18010_18012
theorem aligned18008_18012 :
    AlignedValid 12 4 missing18008_18012 records18008_18012 :=
  aligned18008_18010.append aligned18010_18012

def missing18012_18013 : List (BitVec (edgeCount 12)) :=
  [missing18012]
abbrev records18012_18013 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18012]
theorem aligned18012_18013 :
    AlignedValid 12 4 missing18012_18013 records18012_18013 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18012
    maskCheck18012 AlignedValid.nil

def missing18013_18014 : List (BitVec (edgeCount 12)) :=
  [missing18013]
abbrev records18013_18014 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18013]
theorem aligned18013_18014 :
    AlignedValid 12 4 missing18013_18014 records18013_18014 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18013
    maskCheck18013 AlignedValid.nil

def missing18012_18014 : List (BitVec (edgeCount 12)) :=
  missing18012_18013 ++ missing18013_18014
abbrev records18012_18014 : List Blob :=
  records18012_18013 ++ records18013_18014
theorem aligned18012_18014 :
    AlignedValid 12 4 missing18012_18014 records18012_18014 :=
  aligned18012_18013.append aligned18013_18014

def missing18014_18015 : List (BitVec (edgeCount 12)) :=
  [missing18014]
abbrev records18014_18015 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18014]
theorem aligned18014_18015 :
    AlignedValid 12 4 missing18014_18015 records18014_18015 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18014
    maskCheck18014 AlignedValid.nil

def missing18015_18016 : List (BitVec (edgeCount 12)) :=
  [missing18015]
abbrev records18015_18016 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18015]
theorem aligned18015_18016 :
    AlignedValid 12 4 missing18015_18016 records18015_18016 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18015
    maskCheck18015 AlignedValid.nil

def missing18014_18016 : List (BitVec (edgeCount 12)) :=
  missing18014_18015 ++ missing18015_18016
abbrev records18014_18016 : List Blob :=
  records18014_18015 ++ records18015_18016
theorem aligned18014_18016 :
    AlignedValid 12 4 missing18014_18016 records18014_18016 :=
  aligned18014_18015.append aligned18015_18016

def missing18012_18016 : List (BitVec (edgeCount 12)) :=
  missing18012_18014 ++ missing18014_18016
abbrev records18012_18016 : List Blob :=
  records18012_18014 ++ records18014_18016
theorem aligned18012_18016 :
    AlignedValid 12 4 missing18012_18016 records18012_18016 :=
  aligned18012_18014.append aligned18014_18016

def missing18008_18016 : List (BitVec (edgeCount 12)) :=
  missing18008_18012 ++ missing18012_18016
abbrev records18008_18016 : List Blob :=
  records18008_18012 ++ records18012_18016
theorem aligned18008_18016 :
    AlignedValid 12 4 missing18008_18016 records18008_18016 :=
  aligned18008_18012.append aligned18012_18016

def missing18000_18016 : List (BitVec (edgeCount 12)) :=
  missing18000_18008 ++ missing18008_18016
abbrev records18000_18016 : List Blob :=
  records18000_18008 ++ records18008_18016
theorem aligned18000_18016 :
    AlignedValid 12 4 missing18000_18016 records18000_18016 :=
  aligned18000_18008.append aligned18008_18016

def missing17984_18016 : List (BitVec (edgeCount 12)) :=
  missing17984_18000 ++ missing18000_18016
abbrev records17984_18016 : List Blob :=
  records17984_18000 ++ records18000_18016
theorem aligned17984_18016 :
    AlignedValid 12 4 missing17984_18016 records17984_18016 :=
  aligned17984_18000.append aligned18000_18016

def missing18016_18017 : List (BitVec (edgeCount 12)) :=
  [missing18016]
abbrev records18016_18017 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18016]
theorem aligned18016_18017 :
    AlignedValid 12 4 missing18016_18017 records18016_18017 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18016
    maskCheck18016 AlignedValid.nil

def missing18017_18018 : List (BitVec (edgeCount 12)) :=
  [missing18017]
abbrev records18017_18018 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18017]
theorem aligned18017_18018 :
    AlignedValid 12 4 missing18017_18018 records18017_18018 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18017
    maskCheck18017 AlignedValid.nil

def missing18016_18018 : List (BitVec (edgeCount 12)) :=
  missing18016_18017 ++ missing18017_18018
abbrev records18016_18018 : List Blob :=
  records18016_18017 ++ records18017_18018
theorem aligned18016_18018 :
    AlignedValid 12 4 missing18016_18018 records18016_18018 :=
  aligned18016_18017.append aligned18017_18018

def missing18018_18019 : List (BitVec (edgeCount 12)) :=
  [missing18018]
abbrev records18018_18019 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18018]
theorem aligned18018_18019 :
    AlignedValid 12 4 missing18018_18019 records18018_18019 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18018
    maskCheck18018 AlignedValid.nil

def missing18019_18020 : List (BitVec (edgeCount 12)) :=
  [missing18019]
abbrev records18019_18020 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18019]
theorem aligned18019_18020 :
    AlignedValid 12 4 missing18019_18020 records18019_18020 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18019
    maskCheck18019 AlignedValid.nil

def missing18018_18020 : List (BitVec (edgeCount 12)) :=
  missing18018_18019 ++ missing18019_18020
abbrev records18018_18020 : List Blob :=
  records18018_18019 ++ records18019_18020
theorem aligned18018_18020 :
    AlignedValid 12 4 missing18018_18020 records18018_18020 :=
  aligned18018_18019.append aligned18019_18020

def missing18016_18020 : List (BitVec (edgeCount 12)) :=
  missing18016_18018 ++ missing18018_18020
abbrev records18016_18020 : List Blob :=
  records18016_18018 ++ records18018_18020
theorem aligned18016_18020 :
    AlignedValid 12 4 missing18016_18020 records18016_18020 :=
  aligned18016_18018.append aligned18018_18020

def missing18020_18021 : List (BitVec (edgeCount 12)) :=
  [missing18020]
abbrev records18020_18021 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18020]
theorem aligned18020_18021 :
    AlignedValid 12 4 missing18020_18021 records18020_18021 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18020
    maskCheck18020 AlignedValid.nil

def missing18021_18022 : List (BitVec (edgeCount 12)) :=
  [missing18021]
abbrev records18021_18022 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18021]
theorem aligned18021_18022 :
    AlignedValid 12 4 missing18021_18022 records18021_18022 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18021
    maskCheck18021 AlignedValid.nil

def missing18020_18022 : List (BitVec (edgeCount 12)) :=
  missing18020_18021 ++ missing18021_18022
abbrev records18020_18022 : List Blob :=
  records18020_18021 ++ records18021_18022
theorem aligned18020_18022 :
    AlignedValid 12 4 missing18020_18022 records18020_18022 :=
  aligned18020_18021.append aligned18021_18022

def missing18022_18023 : List (BitVec (edgeCount 12)) :=
  [missing18022]
abbrev records18022_18023 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18022]
theorem aligned18022_18023 :
    AlignedValid 12 4 missing18022_18023 records18022_18023 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18022
    maskCheck18022 AlignedValid.nil

def missing18023_18024 : List (BitVec (edgeCount 12)) :=
  [missing18023]
abbrev records18023_18024 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18023]
theorem aligned18023_18024 :
    AlignedValid 12 4 missing18023_18024 records18023_18024 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18023
    maskCheck18023 AlignedValid.nil

def missing18022_18024 : List (BitVec (edgeCount 12)) :=
  missing18022_18023 ++ missing18023_18024
abbrev records18022_18024 : List Blob :=
  records18022_18023 ++ records18023_18024
theorem aligned18022_18024 :
    AlignedValid 12 4 missing18022_18024 records18022_18024 :=
  aligned18022_18023.append aligned18023_18024

def missing18020_18024 : List (BitVec (edgeCount 12)) :=
  missing18020_18022 ++ missing18022_18024
abbrev records18020_18024 : List Blob :=
  records18020_18022 ++ records18022_18024
theorem aligned18020_18024 :
    AlignedValid 12 4 missing18020_18024 records18020_18024 :=
  aligned18020_18022.append aligned18022_18024

def missing18016_18024 : List (BitVec (edgeCount 12)) :=
  missing18016_18020 ++ missing18020_18024
abbrev records18016_18024 : List Blob :=
  records18016_18020 ++ records18020_18024
theorem aligned18016_18024 :
    AlignedValid 12 4 missing18016_18024 records18016_18024 :=
  aligned18016_18020.append aligned18020_18024

def missing18024_18025 : List (BitVec (edgeCount 12)) :=
  [missing18024]
abbrev records18024_18025 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18024]
theorem aligned18024_18025 :
    AlignedValid 12 4 missing18024_18025 records18024_18025 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18024
    maskCheck18024 AlignedValid.nil

def missing18025_18026 : List (BitVec (edgeCount 12)) :=
  [missing18025]
abbrev records18025_18026 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18025]
theorem aligned18025_18026 :
    AlignedValid 12 4 missing18025_18026 records18025_18026 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18025
    maskCheck18025 AlignedValid.nil

def missing18024_18026 : List (BitVec (edgeCount 12)) :=
  missing18024_18025 ++ missing18025_18026
abbrev records18024_18026 : List Blob :=
  records18024_18025 ++ records18025_18026
theorem aligned18024_18026 :
    AlignedValid 12 4 missing18024_18026 records18024_18026 :=
  aligned18024_18025.append aligned18025_18026

def missing18026_18027 : List (BitVec (edgeCount 12)) :=
  [missing18026]
abbrev records18026_18027 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18026]
theorem aligned18026_18027 :
    AlignedValid 12 4 missing18026_18027 records18026_18027 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18026
    maskCheck18026 AlignedValid.nil

def missing18027_18028 : List (BitVec (edgeCount 12)) :=
  [missing18027]
abbrev records18027_18028 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18027]
theorem aligned18027_18028 :
    AlignedValid 12 4 missing18027_18028 records18027_18028 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18027
    maskCheck18027 AlignedValid.nil

def missing18026_18028 : List (BitVec (edgeCount 12)) :=
  missing18026_18027 ++ missing18027_18028
abbrev records18026_18028 : List Blob :=
  records18026_18027 ++ records18027_18028
theorem aligned18026_18028 :
    AlignedValid 12 4 missing18026_18028 records18026_18028 :=
  aligned18026_18027.append aligned18027_18028

def missing18024_18028 : List (BitVec (edgeCount 12)) :=
  missing18024_18026 ++ missing18026_18028
abbrev records18024_18028 : List Blob :=
  records18024_18026 ++ records18026_18028
theorem aligned18024_18028 :
    AlignedValid 12 4 missing18024_18028 records18024_18028 :=
  aligned18024_18026.append aligned18026_18028

def missing18028_18029 : List (BitVec (edgeCount 12)) :=
  [missing18028]
abbrev records18028_18029 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18028]
theorem aligned18028_18029 :
    AlignedValid 12 4 missing18028_18029 records18028_18029 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18028
    maskCheck18028 AlignedValid.nil

def missing18029_18030 : List (BitVec (edgeCount 12)) :=
  [missing18029]
abbrev records18029_18030 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18029]
theorem aligned18029_18030 :
    AlignedValid 12 4 missing18029_18030 records18029_18030 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18029
    maskCheck18029 AlignedValid.nil

def missing18028_18030 : List (BitVec (edgeCount 12)) :=
  missing18028_18029 ++ missing18029_18030
abbrev records18028_18030 : List Blob :=
  records18028_18029 ++ records18029_18030
theorem aligned18028_18030 :
    AlignedValid 12 4 missing18028_18030 records18028_18030 :=
  aligned18028_18029.append aligned18029_18030

def missing18030_18031 : List (BitVec (edgeCount 12)) :=
  [missing18030]
abbrev records18030_18031 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18030]
theorem aligned18030_18031 :
    AlignedValid 12 4 missing18030_18031 records18030_18031 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18030
    maskCheck18030 AlignedValid.nil

def missing18031_18032 : List (BitVec (edgeCount 12)) :=
  [missing18031]
abbrev records18031_18032 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18031]
theorem aligned18031_18032 :
    AlignedValid 12 4 missing18031_18032 records18031_18032 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18031
    maskCheck18031 AlignedValid.nil

def missing18030_18032 : List (BitVec (edgeCount 12)) :=
  missing18030_18031 ++ missing18031_18032
abbrev records18030_18032 : List Blob :=
  records18030_18031 ++ records18031_18032
theorem aligned18030_18032 :
    AlignedValid 12 4 missing18030_18032 records18030_18032 :=
  aligned18030_18031.append aligned18031_18032

def missing18028_18032 : List (BitVec (edgeCount 12)) :=
  missing18028_18030 ++ missing18030_18032
abbrev records18028_18032 : List Blob :=
  records18028_18030 ++ records18030_18032
theorem aligned18028_18032 :
    AlignedValid 12 4 missing18028_18032 records18028_18032 :=
  aligned18028_18030.append aligned18030_18032

def missing18024_18032 : List (BitVec (edgeCount 12)) :=
  missing18024_18028 ++ missing18028_18032
abbrev records18024_18032 : List Blob :=
  records18024_18028 ++ records18028_18032
theorem aligned18024_18032 :
    AlignedValid 12 4 missing18024_18032 records18024_18032 :=
  aligned18024_18028.append aligned18028_18032

def missing18016_18032 : List (BitVec (edgeCount 12)) :=
  missing18016_18024 ++ missing18024_18032
abbrev records18016_18032 : List Blob :=
  records18016_18024 ++ records18024_18032
theorem aligned18016_18032 :
    AlignedValid 12 4 missing18016_18032 records18016_18032 :=
  aligned18016_18024.append aligned18024_18032

def missing18032_18033 : List (BitVec (edgeCount 12)) :=
  [missing18032]
abbrev records18032_18033 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18032]
theorem aligned18032_18033 :
    AlignedValid 12 4 missing18032_18033 records18032_18033 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18032
    maskCheck18032 AlignedValid.nil

def missing18033_18034 : List (BitVec (edgeCount 12)) :=
  [missing18033]
abbrev records18033_18034 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18033]
theorem aligned18033_18034 :
    AlignedValid 12 4 missing18033_18034 records18033_18034 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18033
    maskCheck18033 AlignedValid.nil

def missing18032_18034 : List (BitVec (edgeCount 12)) :=
  missing18032_18033 ++ missing18033_18034
abbrev records18032_18034 : List Blob :=
  records18032_18033 ++ records18033_18034
theorem aligned18032_18034 :
    AlignedValid 12 4 missing18032_18034 records18032_18034 :=
  aligned18032_18033.append aligned18033_18034

def missing18034_18035 : List (BitVec (edgeCount 12)) :=
  [missing18034]
abbrev records18034_18035 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18034]
theorem aligned18034_18035 :
    AlignedValid 12 4 missing18034_18035 records18034_18035 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18034
    maskCheck18034 AlignedValid.nil

def missing18035_18036 : List (BitVec (edgeCount 12)) :=
  [missing18035]
abbrev records18035_18036 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18035]
theorem aligned18035_18036 :
    AlignedValid 12 4 missing18035_18036 records18035_18036 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18035
    maskCheck18035 AlignedValid.nil

def missing18034_18036 : List (BitVec (edgeCount 12)) :=
  missing18034_18035 ++ missing18035_18036
abbrev records18034_18036 : List Blob :=
  records18034_18035 ++ records18035_18036
theorem aligned18034_18036 :
    AlignedValid 12 4 missing18034_18036 records18034_18036 :=
  aligned18034_18035.append aligned18035_18036

def missing18032_18036 : List (BitVec (edgeCount 12)) :=
  missing18032_18034 ++ missing18034_18036
abbrev records18032_18036 : List Blob :=
  records18032_18034 ++ records18034_18036
theorem aligned18032_18036 :
    AlignedValid 12 4 missing18032_18036 records18032_18036 :=
  aligned18032_18034.append aligned18034_18036

def missing18036_18037 : List (BitVec (edgeCount 12)) :=
  [missing18036]
abbrev records18036_18037 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18036]
theorem aligned18036_18037 :
    AlignedValid 12 4 missing18036_18037 records18036_18037 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18036
    maskCheck18036 AlignedValid.nil

def missing18037_18038 : List (BitVec (edgeCount 12)) :=
  [missing18037]
abbrev records18037_18038 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18037]
theorem aligned18037_18038 :
    AlignedValid 12 4 missing18037_18038 records18037_18038 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18037
    maskCheck18037 AlignedValid.nil

def missing18036_18038 : List (BitVec (edgeCount 12)) :=
  missing18036_18037 ++ missing18037_18038
abbrev records18036_18038 : List Blob :=
  records18036_18037 ++ records18037_18038
theorem aligned18036_18038 :
    AlignedValid 12 4 missing18036_18038 records18036_18038 :=
  aligned18036_18037.append aligned18037_18038

def missing18038_18039 : List (BitVec (edgeCount 12)) :=
  [missing18038]
abbrev records18038_18039 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18038]
theorem aligned18038_18039 :
    AlignedValid 12 4 missing18038_18039 records18038_18039 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18038
    maskCheck18038 AlignedValid.nil

def missing18039_18040 : List (BitVec (edgeCount 12)) :=
  [missing18039]
abbrev records18039_18040 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18039]
theorem aligned18039_18040 :
    AlignedValid 12 4 missing18039_18040 records18039_18040 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18039
    maskCheck18039 AlignedValid.nil

def missing18038_18040 : List (BitVec (edgeCount 12)) :=
  missing18038_18039 ++ missing18039_18040
abbrev records18038_18040 : List Blob :=
  records18038_18039 ++ records18039_18040
theorem aligned18038_18040 :
    AlignedValid 12 4 missing18038_18040 records18038_18040 :=
  aligned18038_18039.append aligned18039_18040

def missing18036_18040 : List (BitVec (edgeCount 12)) :=
  missing18036_18038 ++ missing18038_18040
abbrev records18036_18040 : List Blob :=
  records18036_18038 ++ records18038_18040
theorem aligned18036_18040 :
    AlignedValid 12 4 missing18036_18040 records18036_18040 :=
  aligned18036_18038.append aligned18038_18040

def missing18032_18040 : List (BitVec (edgeCount 12)) :=
  missing18032_18036 ++ missing18036_18040
abbrev records18032_18040 : List Blob :=
  records18032_18036 ++ records18036_18040
theorem aligned18032_18040 :
    AlignedValid 12 4 missing18032_18040 records18032_18040 :=
  aligned18032_18036.append aligned18036_18040

def missing18040_18041 : List (BitVec (edgeCount 12)) :=
  [missing18040]
abbrev records18040_18041 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18040]
theorem aligned18040_18041 :
    AlignedValid 12 4 missing18040_18041 records18040_18041 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18040
    maskCheck18040 AlignedValid.nil

def missing18041_18042 : List (BitVec (edgeCount 12)) :=
  [missing18041]
abbrev records18041_18042 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18041]
theorem aligned18041_18042 :
    AlignedValid 12 4 missing18041_18042 records18041_18042 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18041
    maskCheck18041 AlignedValid.nil

def missing18040_18042 : List (BitVec (edgeCount 12)) :=
  missing18040_18041 ++ missing18041_18042
abbrev records18040_18042 : List Blob :=
  records18040_18041 ++ records18041_18042
theorem aligned18040_18042 :
    AlignedValid 12 4 missing18040_18042 records18040_18042 :=
  aligned18040_18041.append aligned18041_18042

def missing18042_18043 : List (BitVec (edgeCount 12)) :=
  [missing18042]
abbrev records18042_18043 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18042]
theorem aligned18042_18043 :
    AlignedValid 12 4 missing18042_18043 records18042_18043 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18042
    maskCheck18042 AlignedValid.nil

def missing18043_18044 : List (BitVec (edgeCount 12)) :=
  [missing18043]
abbrev records18043_18044 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18043]
theorem aligned18043_18044 :
    AlignedValid 12 4 missing18043_18044 records18043_18044 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18043
    maskCheck18043 AlignedValid.nil

def missing18042_18044 : List (BitVec (edgeCount 12)) :=
  missing18042_18043 ++ missing18043_18044
abbrev records18042_18044 : List Blob :=
  records18042_18043 ++ records18043_18044
theorem aligned18042_18044 :
    AlignedValid 12 4 missing18042_18044 records18042_18044 :=
  aligned18042_18043.append aligned18043_18044

def missing18040_18044 : List (BitVec (edgeCount 12)) :=
  missing18040_18042 ++ missing18042_18044
abbrev records18040_18044 : List Blob :=
  records18040_18042 ++ records18042_18044
theorem aligned18040_18044 :
    AlignedValid 12 4 missing18040_18044 records18040_18044 :=
  aligned18040_18042.append aligned18042_18044

def missing18044_18045 : List (BitVec (edgeCount 12)) :=
  [missing18044]
abbrev records18044_18045 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18044]
theorem aligned18044_18045 :
    AlignedValid 12 4 missing18044_18045 records18044_18045 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18044
    maskCheck18044 AlignedValid.nil

def missing18045_18046 : List (BitVec (edgeCount 12)) :=
  [missing18045]
abbrev records18045_18046 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18045]
theorem aligned18045_18046 :
    AlignedValid 12 4 missing18045_18046 records18045_18046 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18045
    maskCheck18045 AlignedValid.nil

def missing18044_18046 : List (BitVec (edgeCount 12)) :=
  missing18044_18045 ++ missing18045_18046
abbrev records18044_18046 : List Blob :=
  records18044_18045 ++ records18045_18046
theorem aligned18044_18046 :
    AlignedValid 12 4 missing18044_18046 records18044_18046 :=
  aligned18044_18045.append aligned18045_18046

def missing18046_18047 : List (BitVec (edgeCount 12)) :=
  [missing18046]
abbrev records18046_18047 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18046]
theorem aligned18046_18047 :
    AlignedValid 12 4 missing18046_18047 records18046_18047 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18046
    maskCheck18046 AlignedValid.nil

def missing18047_18048 : List (BitVec (edgeCount 12)) :=
  [missing18047]
abbrev records18047_18048 : List Blob :=
  [StrongPackedBucketN12A4Shard140.record18047]
theorem aligned18047_18048 :
    AlignedValid 12 4 missing18047_18048 records18047_18048 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard140.check18047
    maskCheck18047 AlignedValid.nil

def missing18046_18048 : List (BitVec (edgeCount 12)) :=
  missing18046_18047 ++ missing18047_18048
abbrev records18046_18048 : List Blob :=
  records18046_18047 ++ records18047_18048
theorem aligned18046_18048 :
    AlignedValid 12 4 missing18046_18048 records18046_18048 :=
  aligned18046_18047.append aligned18047_18048

def missing18044_18048 : List (BitVec (edgeCount 12)) :=
  missing18044_18046 ++ missing18046_18048
abbrev records18044_18048 : List Blob :=
  records18044_18046 ++ records18046_18048
theorem aligned18044_18048 :
    AlignedValid 12 4 missing18044_18048 records18044_18048 :=
  aligned18044_18046.append aligned18046_18048

def missing18040_18048 : List (BitVec (edgeCount 12)) :=
  missing18040_18044 ++ missing18044_18048
abbrev records18040_18048 : List Blob :=
  records18040_18044 ++ records18044_18048
theorem aligned18040_18048 :
    AlignedValid 12 4 missing18040_18048 records18040_18048 :=
  aligned18040_18044.append aligned18044_18048

def missing18032_18048 : List (BitVec (edgeCount 12)) :=
  missing18032_18040 ++ missing18040_18048
abbrev records18032_18048 : List Blob :=
  records18032_18040 ++ records18040_18048
theorem aligned18032_18048 :
    AlignedValid 12 4 missing18032_18048 records18032_18048 :=
  aligned18032_18040.append aligned18040_18048

def missing18016_18048 : List (BitVec (edgeCount 12)) :=
  missing18016_18032 ++ missing18032_18048
abbrev records18016_18048 : List Blob :=
  records18016_18032 ++ records18032_18048
theorem aligned18016_18048 :
    AlignedValid 12 4 missing18016_18048 records18016_18048 :=
  aligned18016_18032.append aligned18032_18048

def missing17984_18048 : List (BitVec (edgeCount 12)) :=
  missing17984_18016 ++ missing18016_18048
abbrev records17984_18048 : List Blob :=
  records17984_18016 ++ records18016_18048
theorem aligned17984_18048 :
    AlignedValid 12 4 missing17984_18048 records17984_18048 :=
  aligned17984_18016.append aligned18016_18048

def missing17920_18048 : List (BitVec (edgeCount 12)) :=
  missing17920_17984 ++ missing17984_18048
abbrev records17920_18048 : List Blob :=
  records17920_17984 ++ records17984_18048
theorem aligned17920_18048 :
    AlignedValid 12 4 missing17920_18048 records17920_18048 :=
  aligned17920_17984.append aligned17984_18048

abbrev missing : List (BitVec (edgeCount 12)) := missing17920_18048
abbrev records : List Blob := records17920_18048
theorem aligned : AlignedValid 12 4 missing records := aligned17920_18048

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard140
