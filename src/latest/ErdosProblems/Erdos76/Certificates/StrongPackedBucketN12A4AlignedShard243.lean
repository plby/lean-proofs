/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard243

/-! Decode-only alignment checks for n=12, a=4, records 31104--31231. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard243

open PackedBucketCertificate

def missing31104 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4468204768602390528
theorem maskCheck31104 :
    checkMaskFor missing31104 StrongPackedBucketN12A4Shard243.record31104 = true := by
  decide

def missing31105 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7170364545024688128
theorem maskCheck31105 :
    checkMaskFor missing31105 StrongPackedBucketN12A4Shard243.record31105 = true := by
  decide

def missing31106 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7314479733100544000
theorem maskCheck31106 :
    checkMaskFor missing31106 StrongPackedBucketN12A4Shard243.record31106 = true := by
  decide

def missing31107 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7422566124157435904
theorem maskCheck31107 :
    checkMaskFor missing31107 StrongPackedBucketN12A4Shard243.record31107 = true := by
  decide

def missing31108 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7818882891366039552
theorem maskCheck31108 :
    checkMaskFor missing31108 StrongPackedBucketN12A4Shard243.record31108 = true := by
  decide

def missing31109 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7926969282422931456
theorem maskCheck31109 :
    checkMaskFor missing31109 StrongPackedBucketN12A4Shard243.record31109 = true := by
  decide

def missing31110 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8179170861555679232
theorem maskCheck31110 :
    checkMaskFor missing31110 StrongPackedBucketN12A4Shard243.record31110 = true := by
  decide

def missing31111 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8431372440688427008
theorem maskCheck31111 :
    checkMaskFor missing31111 StrongPackedBucketN12A4Shard243.record31111 = true := by
  decide

def missing31112 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8935775598953922560
theorem maskCheck31112 :
    checkMaskFor missing31112 StrongPackedBucketN12A4Shard243.record31112 = true := by
  decide

def missing31113 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9764437930390093824
theorem maskCheck31113 :
    checkMaskFor missing31113 StrongPackedBucketN12A4Shard243.record31113 = true := by
  decide

def missing31114 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10268841088655589376
theorem maskCheck31114 :
    checkMaskFor missing31114 StrongPackedBucketN12A4Shard243.record31114 = true := by
  decide

def missing31115 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10629129058845229056
theorem maskCheck31115 :
    checkMaskFor missing31115 StrongPackedBucketN12A4Shard243.record31115 = true := by
  decide

def missing31116 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10845301840959012864
theorem maskCheck31116 :
    checkMaskFor missing31116 StrongPackedBucketN12A4Shard243.record31116 = true := by
  decide

def missing31117 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10881330637977976832
theorem maskCheck31117 :
    checkMaskFor missing31117 StrongPackedBucketN12A4Shard243.record31117 = true := by
  decide

def missing31118 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11385733796243472384
theorem maskCheck31118 :
    checkMaskFor missing31118 StrongPackedBucketN12A4Shard243.record31118 = true := by
  decide

def missing31119 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11782050563452076032
theorem maskCheck31119 :
    checkMaskFor missing31119 StrongPackedBucketN12A4Shard243.record31119 = true := by
  decide

def missing31120 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11998223345565859840
theorem maskCheck31120 :
    checkMaskFor missing31120 StrongPackedBucketN12A4Shard243.record31120 = true := by
  decide

def missing31121 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12034252142584823808
theorem maskCheck31121 :
    checkMaskFor missing31121 StrongPackedBucketN12A4Shard243.record31121 = true := by
  decide

def missing31122 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12286453721717571584
theorem maskCheck31122 :
    checkMaskFor missing31122 StrongPackedBucketN12A4Shard243.record31122 = true := by
  decide

def missing31123 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12538655300850319360
theorem maskCheck31123 :
    checkMaskFor missing31123 StrongPackedBucketN12A4Shard243.record31123 = true := by
  decide

def missing31124 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12862914474020995072
theorem maskCheck31124 :
    checkMaskFor missing31124 StrongPackedBucketN12A4Shard243.record31124 = true := by
  decide

def missing31125 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13115116053153742848
theorem maskCheck31125 :
    checkMaskFor missing31125 StrongPackedBucketN12A4Shard243.record31125 = true := by
  decide

def missing31126 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18987809967244869632
theorem maskCheck31126 :
    checkMaskFor missing31126 StrongPackedBucketN12A4Shard243.record31126 = true := by
  decide

def missing31127 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19276040343396581376
theorem maskCheck31127 :
    checkMaskFor missing31127 StrongPackedBucketN12A4Shard243.record31127 = true := by
  decide

def missing31128 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19420155531472437248
theorem maskCheck31128 :
    checkMaskFor missing31128 StrongPackedBucketN12A4Shard243.record31128 = true := by
  decide

def missing31129 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19492213125510365184
theorem maskCheck31129 :
    checkMaskFor missing31129 StrongPackedBucketN12A4Shard243.record31129 = true := by
  decide

def missing31130 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19852501095700004864
theorem maskCheck31130 :
    checkMaskFor missing31130 StrongPackedBucketN12A4Shard243.record31130 = true := by
  decide

def missing31131 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19996616283775860736
theorem maskCheck31131 :
    checkMaskFor missing31131 StrongPackedBucketN12A4Shard243.record31131 = true := by
  decide

def missing31132 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20068673877813788672
theorem maskCheck31132 :
    checkMaskFor missing31132 StrongPackedBucketN12A4Shard243.record31132 = true := by
  decide

def missing31133 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20284846659927572480
theorem maskCheck31133 :
    checkMaskFor missing31133 StrongPackedBucketN12A4Shard243.record31133 = true := by
  decide

def missing31134 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20356904253965500416
theorem maskCheck31134 :
    checkMaskFor missing31134 StrongPackedBucketN12A4Shard243.record31134 = true := by
  decide

def missing31135 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20501019442041356288
theorem maskCheck31135 :
    checkMaskFor missing31135 StrongPackedBucketN12A4Shard243.record31135 = true := by
  decide

def missing31136 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21149537788382707712
theorem maskCheck31136 :
    checkMaskFor missing31136 StrongPackedBucketN12A4Shard243.record31136 = true := by
  decide

def missing31137 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21221595382420635648
theorem maskCheck31137 :
    checkMaskFor missing31137 StrongPackedBucketN12A4Shard243.record31137 = true := by
  decide

def missing31138 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21653940946648203264
theorem maskCheck31138 :
    checkMaskFor missing31138 StrongPackedBucketN12A4Shard243.record31138 = true := by
  decide

def missing31139 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22230401698951626752
theorem maskCheck31139 :
    checkMaskFor missing31139 StrongPackedBucketN12A4Shard243.record31139 = true := by
  decide

def missing31140 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23311265609520545792
theorem maskCheck31140 :
    checkMaskFor missing31140 StrongPackedBucketN12A4Shard243.record31140 = true := by
  decide

def missing31141 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23455380797596401664
theorem maskCheck31141 :
    checkMaskFor missing31141 StrongPackedBucketN12A4Shard243.record31141 = true := by
  decide

def missing31142 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23743611173748113408
theorem maskCheck31142 :
    checkMaskFor missing31142 StrongPackedBucketN12A4Shard243.record31142 = true := by
  decide

def missing31143 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23815668767786041344
theorem maskCheck31143 :
    checkMaskFor missing31143 StrongPackedBucketN12A4Shard243.record31143 = true := by
  decide

def missing31144 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23959783955861897216
theorem maskCheck31144 :
    checkMaskFor missing31144 StrongPackedBucketN12A4Shard243.record31144 = true := by
  decide

def missing31145 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24320071926051536896
theorem maskCheck31145 :
    checkMaskFor missing31145 StrongPackedBucketN12A4Shard243.record31145 = true := by
  decide

def missing31146 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24824475084317032448
theorem maskCheck31146 :
    checkMaskFor missing31146 StrongPackedBucketN12A4Shard243.record31146 = true := by
  decide

def missing31147 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27922951627947933696
theorem maskCheck31147 :
    checkMaskFor missing31147 StrongPackedBucketN12A4Shard243.record31147 = true := by
  decide

def missing31148 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28139124410061717504
theorem maskCheck31148 :
    checkMaskFor missing31148 StrongPackedBucketN12A4Shard243.record31148 = true := by
  decide

def missing31149 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28427354786213429248
theorem maskCheck31149 :
    checkMaskFor missing31149 StrongPackedBucketN12A4Shard243.record31149 = true := by
  decide

def missing31150 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29003815538516852736
theorem maskCheck31150 :
    checkMaskFor missing31150 StrongPackedBucketN12A4Shard243.record31150 = true := by
  decide

def missing31151 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55593067738512261120
theorem maskCheck31151 :
    checkMaskFor missing31151 StrongPackedBucketN12A4Shard243.record31151 = true := by
  decide

def missing31152 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55737182926588116992
theorem maskCheck31152 :
    checkMaskFor missing31152 StrongPackedBucketN12A4Shard243.record31152 = true := by
  decide

def missing31153 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56601874055043252224
theorem maskCheck31153 :
    checkMaskFor missing31153 StrongPackedBucketN12A4Shard243.record31153 = true := by
  decide

def missing31154 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117737752071274496
theorem maskCheck31154 :
    checkMaskFor missing31154 StrongPackedBucketN12A4Shard243.record31154 = true := by
  decide

def missing31155 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1694198504374697984
theorem maskCheck31155 :
    checkMaskFor missing31155 StrongPackedBucketN12A4Shard243.record31155 = true := by
  decide

def missing31156 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1982428880526409728
theorem maskCheck31156 :
    checkMaskFor missing31156 StrongPackedBucketN12A4Shard243.record31156 = true := by
  decide

def missing31157 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2126544068602265600
theorem maskCheck31157 :
    checkMaskFor missing31157 StrongPackedBucketN12A4Shard243.record31157 = true := by
  decide

def missing31158 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2234630459659157504
theorem maskCheck31158 :
    checkMaskFor missing31158 StrongPackedBucketN12A4Shard243.record31158 = true := by
  decide

def missing31159 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2847120008981544960
theorem maskCheck31159 :
    checkMaskFor missing31159 StrongPackedBucketN12A4Shard243.record31159 = true := by
  decide

def missing31160 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3135350385133256704
theorem maskCheck31160 :
    checkMaskFor missing31160 StrongPackedBucketN12A4Shard243.record31160 = true := by
  decide

def missing31161 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3279465573209112576
theorem maskCheck31161 :
    checkMaskFor missing31161 StrongPackedBucketN12A4Shard243.record31161 = true := by
  decide

def missing31162 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3387551964266004480
theorem maskCheck31162 :
    checkMaskFor missing31162 StrongPackedBucketN12A4Shard243.record31162 = true := by
  decide

def missing31163 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3711811137436680192
theorem maskCheck31163 :
    checkMaskFor missing31163 StrongPackedBucketN12A4Shard243.record31163 = true := by
  decide

def missing31164 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3855926325512536064
theorem maskCheck31164 :
    checkMaskFor missing31164 StrongPackedBucketN12A4Shard243.record31164 = true := by
  decide

def missing31165 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3964012716569427968
theorem maskCheck31165 :
    checkMaskFor missing31165 StrongPackedBucketN12A4Shard243.record31165 = true := by
  decide

def missing31166 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4144156701664247808
theorem maskCheck31166 :
    checkMaskFor missing31166 StrongPackedBucketN12A4Shard243.record31166 = true := by
  decide

def missing31167 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4252243092721139712
theorem maskCheck31167 :
    checkMaskFor missing31167 StrongPackedBucketN12A4Shard243.record31167 = true := by
  decide

def missing31168 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4360329483778031616
theorem maskCheck31168 :
    checkMaskFor missing31168 StrongPackedBucketN12A4Shard243.record31168 = true := by
  decide

def missing31169 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4396358280796995584
theorem maskCheck31169 :
    checkMaskFor missing31169 StrongPackedBucketN12A4Shard243.record31169 = true := by
  decide

def missing31170 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5152963018195238912
theorem maskCheck31170 :
    checkMaskFor missing31170 StrongPackedBucketN12A4Shard243.record31170 = true := by
  decide

def missing31171 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5441193394346950656
theorem maskCheck31171 :
    checkMaskFor missing31171 StrongPackedBucketN12A4Shard243.record31171 = true := by
  decide

def missing31172 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5585308582422806528
theorem maskCheck31172 :
    checkMaskFor missing31172 StrongPackedBucketN12A4Shard243.record31172 = true := by
  decide

def missing31173 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5693394973479698432
theorem maskCheck31173 :
    checkMaskFor missing31173 StrongPackedBucketN12A4Shard243.record31173 = true := by
  decide

def missing31174 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6017654146650374144
theorem maskCheck31174 :
    checkMaskFor missing31174 StrongPackedBucketN12A4Shard243.record31174 = true := by
  decide

def missing31175 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6161769334726230016
theorem maskCheck31175 :
    checkMaskFor missing31175 StrongPackedBucketN12A4Shard243.record31175 = true := by
  decide

def missing31176 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6269855725783121920
theorem maskCheck31176 :
    checkMaskFor missing31176 StrongPackedBucketN12A4Shard243.record31176 = true := by
  decide

def missing31177 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6449999710877941760
theorem maskCheck31177 :
    checkMaskFor missing31177 StrongPackedBucketN12A4Shard243.record31177 = true := by
  decide

def missing31178 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6558086101934833664
theorem maskCheck31178 :
    checkMaskFor missing31178 StrongPackedBucketN12A4Shard243.record31178 = true := by
  decide

def missing31179 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6702201290010689536
theorem maskCheck31179 :
    checkMaskFor missing31179 StrongPackedBucketN12A4Shard243.record31179 = true := by
  decide

def missing31180 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7170575651257221120
theorem maskCheck31180 :
    checkMaskFor missing31180 StrongPackedBucketN12A4Shard243.record31180 = true := by
  decide

def missing31181 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7314690839333076992
theorem maskCheck31181 :
    checkMaskFor missing31181 StrongPackedBucketN12A4Shard243.record31181 = true := by
  decide

def missing31182 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7422777230389968896
theorem maskCheck31182 :
    checkMaskFor missing31182 StrongPackedBucketN12A4Shard243.record31182 = true := by
  decide

def missing31183 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7602921215484788736
theorem maskCheck31183 :
    checkMaskFor missing31183 StrongPackedBucketN12A4Shard243.record31183 = true := by
  decide

def missing31184 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7711007606541680640
theorem maskCheck31184 :
    checkMaskFor missing31184 StrongPackedBucketN12A4Shard243.record31184 = true := by
  decide

def missing31185 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7855122794617536512
theorem maskCheck31185 :
    checkMaskFor missing31185 StrongPackedBucketN12A4Shard243.record31185 = true := by
  decide

def missing31186 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8179381967788212224
theorem maskCheck31186 :
    checkMaskFor missing31186 StrongPackedBucketN12A4Shard243.record31186 = true := by
  decide

def missing31187 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8431583546920960000
theorem maskCheck31187 :
    checkMaskFor missing31187 StrongPackedBucketN12A4Shard243.record31187 = true := by
  decide

def missing31188 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8719813923072671744
theorem maskCheck31188 :
    checkMaskFor missing31188 StrongPackedBucketN12A4Shard243.record31188 = true := by
  decide

def missing31189 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14088104678898302976
theorem maskCheck31189 :
    checkMaskFor missing31189 StrongPackedBucketN12A4Shard243.record31189 = true := by
  decide

def missing31190 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14340306258031050752
theorem maskCheck31190 :
    checkMaskFor missing31190 StrongPackedBucketN12A4Shard243.record31190 = true := by
  decide

def missing31191 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14628536634182762496
theorem maskCheck31191 :
    checkMaskFor missing31191 StrongPackedBucketN12A4Shard243.record31191 = true := by
  decide

def missing31192 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15204997386486185984
theorem maskCheck31192 :
    checkMaskFor missing31192 StrongPackedBucketN12A4Shard243.record31192 = true := by
  decide

def missing31193 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18988021073477402624
theorem maskCheck31193 :
    checkMaskFor missing31193 StrongPackedBucketN12A4Shard243.record31193 = true := by
  decide

def missing31194 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19276251449629114368
theorem maskCheck31194 :
    checkMaskFor missing31194 StrongPackedBucketN12A4Shard243.record31194 = true := by
  decide

def missing31195 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19420366637704970240
theorem maskCheck31195 :
    checkMaskFor missing31195 StrongPackedBucketN12A4Shard243.record31195 = true := by
  decide

def missing31196 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19528453028761862144
theorem maskCheck31196 :
    checkMaskFor missing31196 StrongPackedBucketN12A4Shard243.record31196 = true := by
  decide

def missing31197 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19852712201932537856
theorem maskCheck31197 :
    checkMaskFor missing31197 StrongPackedBucketN12A4Shard243.record31197 = true := by
  decide

def missing31198 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19996827390008393728
theorem maskCheck31198 :
    checkMaskFor missing31198 StrongPackedBucketN12A4Shard243.record31198 = true := by
  decide

def missing31199 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20104913781065285632
theorem maskCheck31199 :
    checkMaskFor missing31199 StrongPackedBucketN12A4Shard243.record31199 = true := by
  decide

def missing31200 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20285057766160105472
theorem maskCheck31200 :
    checkMaskFor missing31200 StrongPackedBucketN12A4Shard243.record31200 = true := by
  decide

def missing31201 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20501230548273889280
theorem maskCheck31201 :
    checkMaskFor missing31201 StrongPackedBucketN12A4Shard243.record31201 = true := by
  decide

def missing31202 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20537259345292853248
theorem maskCheck31202 :
    checkMaskFor missing31202 StrongPackedBucketN12A4Shard243.record31202 = true := by
  decide

def missing31203 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21005633706539384832
theorem maskCheck31203 :
    checkMaskFor missing31203 StrongPackedBucketN12A4Shard243.record31203 = true := by
  decide

def missing31204 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21149748894615240704
theorem maskCheck31204 :
    checkMaskFor missing31204 StrongPackedBucketN12A4Shard243.record31204 = true := by
  decide

def missing31205 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21437979270766952448
theorem maskCheck31205 :
    checkMaskFor missing31205 StrongPackedBucketN12A4Shard243.record31205 = true := by
  decide

def missing31206 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21654152052880736256
theorem maskCheck31206 :
    checkMaskFor missing31206 StrongPackedBucketN12A4Shard243.record31206 = true := by
  decide

def missing31207 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21690180849899700224
theorem maskCheck31207 :
    checkMaskFor missing31207 StrongPackedBucketN12A4Shard243.record31207 = true := by
  decide

def missing31208 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22014440023070375936
theorem maskCheck31208 :
    checkMaskFor missing31208 StrongPackedBucketN12A4Shard243.record31208 = true := by
  decide

def missing31209 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22230612805184159744
theorem maskCheck31209 :
    checkMaskFor missing31209 StrongPackedBucketN12A4Shard243.record31209 = true := by
  decide

def missing31210 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22518843181335871488
theorem maskCheck31210 :
    checkMaskFor missing31210 StrongPackedBucketN12A4Shard243.record31210 = true := by
  decide

def missing31211 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22771044760468619264
theorem maskCheck31211 :
    checkMaskFor missing31211 StrongPackedBucketN12A4Shard243.record31211 = true := by
  decide

def missing31212 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23311476715753078784
theorem maskCheck31212 :
    checkMaskFor missing31212 StrongPackedBucketN12A4Shard243.record31212 = true := by
  decide

def missing31213 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23455591903828934656
theorem maskCheck31213 :
    checkMaskFor missing31213 StrongPackedBucketN12A4Shard243.record31213 = true := by
  decide

def missing31214 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23563678294885826560
theorem maskCheck31214 :
    checkMaskFor missing31214 StrongPackedBucketN12A4Shard243.record31214 = true := by
  decide

def missing31215 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23743822279980646400
theorem maskCheck31215 :
    checkMaskFor missing31215 StrongPackedBucketN12A4Shard243.record31215 = true := by
  decide

def missing31216 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23996023859113394176
theorem maskCheck31216 :
    checkMaskFor missing31216 StrongPackedBucketN12A4Shard243.record31216 = true := by
  decide

def missing31217 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24320283032284069888
theorem maskCheck31217 :
    checkMaskFor missing31217 StrongPackedBucketN12A4Shard243.record31217 = true := by
  decide

def missing31218 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24572484611416817664
theorem maskCheck31218 :
    checkMaskFor missing31218 StrongPackedBucketN12A4Shard243.record31218 = true := by
  decide

def missing31219 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25473204536890916864
theorem maskCheck31219 :
    checkMaskFor missing31219 StrongPackedBucketN12A4Shard243.record31219 = true := by
  decide

def missing31220 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37434765147186954240
theorem maskCheck31220 :
    checkMaskFor missing31220 StrongPackedBucketN12A4Shard243.record31220 = true := by
  decide

def missing31221 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37722995523338665984
theorem maskCheck31221 :
    checkMaskFor missing31221 StrongPackedBucketN12A4Shard243.record31221 = true := by
  decide

def missing31222 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37867110711414521856
theorem maskCheck31222 :
    checkMaskFor missing31222 StrongPackedBucketN12A4Shard243.record31222 = true := by
  decide

def missing31223 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38299456275642089472
theorem maskCheck31223 :
    checkMaskFor missing31223 StrongPackedBucketN12A4Shard243.record31223 = true := by
  decide

def missing31224 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38443571463717945344
theorem maskCheck31224 :
    checkMaskFor missing31224 StrongPackedBucketN12A4Shard243.record31224 = true := by
  decide

def missing31225 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38731801839869657088
theorem maskCheck31225 :
    checkMaskFor missing31225 StrongPackedBucketN12A4Shard243.record31225 = true := by
  decide

def missing31226 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38947974621983440896
theorem maskCheck31226 :
    checkMaskFor missing31226 StrongPackedBucketN12A4Shard243.record31226 = true := by
  decide

def missing31227 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39596492968324792320
theorem maskCheck31227 :
    checkMaskFor missing31227 StrongPackedBucketN12A4Shard243.record31227 = true := by
  decide

def missing31228 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39884723344476504064
theorem maskCheck31228 :
    checkMaskFor missing31228 StrongPackedBucketN12A4Shard243.record31228 = true := by
  decide

def missing31229 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40100896126590287872
theorem maskCheck31229 :
    checkMaskFor missing31229 StrongPackedBucketN12A4Shard243.record31229 = true := by
  decide

def missing31230 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40677356878893711360
theorem maskCheck31230 :
    checkMaskFor missing31230 StrongPackedBucketN12A4Shard243.record31230 = true := by
  decide

def missing31231 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40965587255045423104
theorem maskCheck31231 :
    checkMaskFor missing31231 StrongPackedBucketN12A4Shard243.record31231 = true := by
  decide

def missing31104_31105 : List (BitVec (edgeCount 12)) :=
  [missing31104]
abbrev records31104_31105 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31104]
theorem aligned31104_31105 :
    AlignedValid 12 4 missing31104_31105 records31104_31105 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31104
    maskCheck31104 AlignedValid.nil

def missing31105_31106 : List (BitVec (edgeCount 12)) :=
  [missing31105]
abbrev records31105_31106 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31105]
theorem aligned31105_31106 :
    AlignedValid 12 4 missing31105_31106 records31105_31106 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31105
    maskCheck31105 AlignedValid.nil

def missing31104_31106 : List (BitVec (edgeCount 12)) :=
  missing31104_31105 ++ missing31105_31106
abbrev records31104_31106 : List Blob :=
  records31104_31105 ++ records31105_31106
theorem aligned31104_31106 :
    AlignedValid 12 4 missing31104_31106 records31104_31106 :=
  aligned31104_31105.append aligned31105_31106

def missing31106_31107 : List (BitVec (edgeCount 12)) :=
  [missing31106]
abbrev records31106_31107 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31106]
theorem aligned31106_31107 :
    AlignedValid 12 4 missing31106_31107 records31106_31107 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31106
    maskCheck31106 AlignedValid.nil

def missing31107_31108 : List (BitVec (edgeCount 12)) :=
  [missing31107]
abbrev records31107_31108 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31107]
theorem aligned31107_31108 :
    AlignedValid 12 4 missing31107_31108 records31107_31108 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31107
    maskCheck31107 AlignedValid.nil

def missing31106_31108 : List (BitVec (edgeCount 12)) :=
  missing31106_31107 ++ missing31107_31108
abbrev records31106_31108 : List Blob :=
  records31106_31107 ++ records31107_31108
theorem aligned31106_31108 :
    AlignedValid 12 4 missing31106_31108 records31106_31108 :=
  aligned31106_31107.append aligned31107_31108

def missing31104_31108 : List (BitVec (edgeCount 12)) :=
  missing31104_31106 ++ missing31106_31108
abbrev records31104_31108 : List Blob :=
  records31104_31106 ++ records31106_31108
theorem aligned31104_31108 :
    AlignedValid 12 4 missing31104_31108 records31104_31108 :=
  aligned31104_31106.append aligned31106_31108

def missing31108_31109 : List (BitVec (edgeCount 12)) :=
  [missing31108]
abbrev records31108_31109 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31108]
theorem aligned31108_31109 :
    AlignedValid 12 4 missing31108_31109 records31108_31109 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31108
    maskCheck31108 AlignedValid.nil

def missing31109_31110 : List (BitVec (edgeCount 12)) :=
  [missing31109]
abbrev records31109_31110 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31109]
theorem aligned31109_31110 :
    AlignedValid 12 4 missing31109_31110 records31109_31110 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31109
    maskCheck31109 AlignedValid.nil

def missing31108_31110 : List (BitVec (edgeCount 12)) :=
  missing31108_31109 ++ missing31109_31110
abbrev records31108_31110 : List Blob :=
  records31108_31109 ++ records31109_31110
theorem aligned31108_31110 :
    AlignedValid 12 4 missing31108_31110 records31108_31110 :=
  aligned31108_31109.append aligned31109_31110

def missing31110_31111 : List (BitVec (edgeCount 12)) :=
  [missing31110]
abbrev records31110_31111 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31110]
theorem aligned31110_31111 :
    AlignedValid 12 4 missing31110_31111 records31110_31111 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31110
    maskCheck31110 AlignedValid.nil

def missing31111_31112 : List (BitVec (edgeCount 12)) :=
  [missing31111]
abbrev records31111_31112 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31111]
theorem aligned31111_31112 :
    AlignedValid 12 4 missing31111_31112 records31111_31112 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31111
    maskCheck31111 AlignedValid.nil

def missing31110_31112 : List (BitVec (edgeCount 12)) :=
  missing31110_31111 ++ missing31111_31112
abbrev records31110_31112 : List Blob :=
  records31110_31111 ++ records31111_31112
theorem aligned31110_31112 :
    AlignedValid 12 4 missing31110_31112 records31110_31112 :=
  aligned31110_31111.append aligned31111_31112

def missing31108_31112 : List (BitVec (edgeCount 12)) :=
  missing31108_31110 ++ missing31110_31112
abbrev records31108_31112 : List Blob :=
  records31108_31110 ++ records31110_31112
theorem aligned31108_31112 :
    AlignedValid 12 4 missing31108_31112 records31108_31112 :=
  aligned31108_31110.append aligned31110_31112

def missing31104_31112 : List (BitVec (edgeCount 12)) :=
  missing31104_31108 ++ missing31108_31112
abbrev records31104_31112 : List Blob :=
  records31104_31108 ++ records31108_31112
theorem aligned31104_31112 :
    AlignedValid 12 4 missing31104_31112 records31104_31112 :=
  aligned31104_31108.append aligned31108_31112

def missing31112_31113 : List (BitVec (edgeCount 12)) :=
  [missing31112]
abbrev records31112_31113 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31112]
theorem aligned31112_31113 :
    AlignedValid 12 4 missing31112_31113 records31112_31113 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31112
    maskCheck31112 AlignedValid.nil

def missing31113_31114 : List (BitVec (edgeCount 12)) :=
  [missing31113]
abbrev records31113_31114 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31113]
theorem aligned31113_31114 :
    AlignedValid 12 4 missing31113_31114 records31113_31114 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31113
    maskCheck31113 AlignedValid.nil

def missing31112_31114 : List (BitVec (edgeCount 12)) :=
  missing31112_31113 ++ missing31113_31114
abbrev records31112_31114 : List Blob :=
  records31112_31113 ++ records31113_31114
theorem aligned31112_31114 :
    AlignedValid 12 4 missing31112_31114 records31112_31114 :=
  aligned31112_31113.append aligned31113_31114

def missing31114_31115 : List (BitVec (edgeCount 12)) :=
  [missing31114]
abbrev records31114_31115 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31114]
theorem aligned31114_31115 :
    AlignedValid 12 4 missing31114_31115 records31114_31115 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31114
    maskCheck31114 AlignedValid.nil

def missing31115_31116 : List (BitVec (edgeCount 12)) :=
  [missing31115]
abbrev records31115_31116 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31115]
theorem aligned31115_31116 :
    AlignedValid 12 4 missing31115_31116 records31115_31116 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31115
    maskCheck31115 AlignedValid.nil

def missing31114_31116 : List (BitVec (edgeCount 12)) :=
  missing31114_31115 ++ missing31115_31116
abbrev records31114_31116 : List Blob :=
  records31114_31115 ++ records31115_31116
theorem aligned31114_31116 :
    AlignedValid 12 4 missing31114_31116 records31114_31116 :=
  aligned31114_31115.append aligned31115_31116

def missing31112_31116 : List (BitVec (edgeCount 12)) :=
  missing31112_31114 ++ missing31114_31116
abbrev records31112_31116 : List Blob :=
  records31112_31114 ++ records31114_31116
theorem aligned31112_31116 :
    AlignedValid 12 4 missing31112_31116 records31112_31116 :=
  aligned31112_31114.append aligned31114_31116

def missing31116_31117 : List (BitVec (edgeCount 12)) :=
  [missing31116]
abbrev records31116_31117 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31116]
theorem aligned31116_31117 :
    AlignedValid 12 4 missing31116_31117 records31116_31117 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31116
    maskCheck31116 AlignedValid.nil

def missing31117_31118 : List (BitVec (edgeCount 12)) :=
  [missing31117]
abbrev records31117_31118 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31117]
theorem aligned31117_31118 :
    AlignedValid 12 4 missing31117_31118 records31117_31118 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31117
    maskCheck31117 AlignedValid.nil

def missing31116_31118 : List (BitVec (edgeCount 12)) :=
  missing31116_31117 ++ missing31117_31118
abbrev records31116_31118 : List Blob :=
  records31116_31117 ++ records31117_31118
theorem aligned31116_31118 :
    AlignedValid 12 4 missing31116_31118 records31116_31118 :=
  aligned31116_31117.append aligned31117_31118

def missing31118_31119 : List (BitVec (edgeCount 12)) :=
  [missing31118]
abbrev records31118_31119 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31118]
theorem aligned31118_31119 :
    AlignedValid 12 4 missing31118_31119 records31118_31119 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31118
    maskCheck31118 AlignedValid.nil

def missing31119_31120 : List (BitVec (edgeCount 12)) :=
  [missing31119]
abbrev records31119_31120 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31119]
theorem aligned31119_31120 :
    AlignedValid 12 4 missing31119_31120 records31119_31120 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31119
    maskCheck31119 AlignedValid.nil

def missing31118_31120 : List (BitVec (edgeCount 12)) :=
  missing31118_31119 ++ missing31119_31120
abbrev records31118_31120 : List Blob :=
  records31118_31119 ++ records31119_31120
theorem aligned31118_31120 :
    AlignedValid 12 4 missing31118_31120 records31118_31120 :=
  aligned31118_31119.append aligned31119_31120

def missing31116_31120 : List (BitVec (edgeCount 12)) :=
  missing31116_31118 ++ missing31118_31120
abbrev records31116_31120 : List Blob :=
  records31116_31118 ++ records31118_31120
theorem aligned31116_31120 :
    AlignedValid 12 4 missing31116_31120 records31116_31120 :=
  aligned31116_31118.append aligned31118_31120

def missing31112_31120 : List (BitVec (edgeCount 12)) :=
  missing31112_31116 ++ missing31116_31120
abbrev records31112_31120 : List Blob :=
  records31112_31116 ++ records31116_31120
theorem aligned31112_31120 :
    AlignedValid 12 4 missing31112_31120 records31112_31120 :=
  aligned31112_31116.append aligned31116_31120

def missing31104_31120 : List (BitVec (edgeCount 12)) :=
  missing31104_31112 ++ missing31112_31120
abbrev records31104_31120 : List Blob :=
  records31104_31112 ++ records31112_31120
theorem aligned31104_31120 :
    AlignedValid 12 4 missing31104_31120 records31104_31120 :=
  aligned31104_31112.append aligned31112_31120

def missing31120_31121 : List (BitVec (edgeCount 12)) :=
  [missing31120]
abbrev records31120_31121 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31120]
theorem aligned31120_31121 :
    AlignedValid 12 4 missing31120_31121 records31120_31121 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31120
    maskCheck31120 AlignedValid.nil

def missing31121_31122 : List (BitVec (edgeCount 12)) :=
  [missing31121]
abbrev records31121_31122 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31121]
theorem aligned31121_31122 :
    AlignedValid 12 4 missing31121_31122 records31121_31122 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31121
    maskCheck31121 AlignedValid.nil

def missing31120_31122 : List (BitVec (edgeCount 12)) :=
  missing31120_31121 ++ missing31121_31122
abbrev records31120_31122 : List Blob :=
  records31120_31121 ++ records31121_31122
theorem aligned31120_31122 :
    AlignedValid 12 4 missing31120_31122 records31120_31122 :=
  aligned31120_31121.append aligned31121_31122

def missing31122_31123 : List (BitVec (edgeCount 12)) :=
  [missing31122]
abbrev records31122_31123 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31122]
theorem aligned31122_31123 :
    AlignedValid 12 4 missing31122_31123 records31122_31123 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31122
    maskCheck31122 AlignedValid.nil

def missing31123_31124 : List (BitVec (edgeCount 12)) :=
  [missing31123]
abbrev records31123_31124 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31123]
theorem aligned31123_31124 :
    AlignedValid 12 4 missing31123_31124 records31123_31124 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31123
    maskCheck31123 AlignedValid.nil

def missing31122_31124 : List (BitVec (edgeCount 12)) :=
  missing31122_31123 ++ missing31123_31124
abbrev records31122_31124 : List Blob :=
  records31122_31123 ++ records31123_31124
theorem aligned31122_31124 :
    AlignedValid 12 4 missing31122_31124 records31122_31124 :=
  aligned31122_31123.append aligned31123_31124

def missing31120_31124 : List (BitVec (edgeCount 12)) :=
  missing31120_31122 ++ missing31122_31124
abbrev records31120_31124 : List Blob :=
  records31120_31122 ++ records31122_31124
theorem aligned31120_31124 :
    AlignedValid 12 4 missing31120_31124 records31120_31124 :=
  aligned31120_31122.append aligned31122_31124

def missing31124_31125 : List (BitVec (edgeCount 12)) :=
  [missing31124]
abbrev records31124_31125 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31124]
theorem aligned31124_31125 :
    AlignedValid 12 4 missing31124_31125 records31124_31125 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31124
    maskCheck31124 AlignedValid.nil

def missing31125_31126 : List (BitVec (edgeCount 12)) :=
  [missing31125]
abbrev records31125_31126 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31125]
theorem aligned31125_31126 :
    AlignedValid 12 4 missing31125_31126 records31125_31126 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31125
    maskCheck31125 AlignedValid.nil

def missing31124_31126 : List (BitVec (edgeCount 12)) :=
  missing31124_31125 ++ missing31125_31126
abbrev records31124_31126 : List Blob :=
  records31124_31125 ++ records31125_31126
theorem aligned31124_31126 :
    AlignedValid 12 4 missing31124_31126 records31124_31126 :=
  aligned31124_31125.append aligned31125_31126

def missing31126_31127 : List (BitVec (edgeCount 12)) :=
  [missing31126]
abbrev records31126_31127 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31126]
theorem aligned31126_31127 :
    AlignedValid 12 4 missing31126_31127 records31126_31127 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31126
    maskCheck31126 AlignedValid.nil

def missing31127_31128 : List (BitVec (edgeCount 12)) :=
  [missing31127]
abbrev records31127_31128 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31127]
theorem aligned31127_31128 :
    AlignedValid 12 4 missing31127_31128 records31127_31128 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31127
    maskCheck31127 AlignedValid.nil

def missing31126_31128 : List (BitVec (edgeCount 12)) :=
  missing31126_31127 ++ missing31127_31128
abbrev records31126_31128 : List Blob :=
  records31126_31127 ++ records31127_31128
theorem aligned31126_31128 :
    AlignedValid 12 4 missing31126_31128 records31126_31128 :=
  aligned31126_31127.append aligned31127_31128

def missing31124_31128 : List (BitVec (edgeCount 12)) :=
  missing31124_31126 ++ missing31126_31128
abbrev records31124_31128 : List Blob :=
  records31124_31126 ++ records31126_31128
theorem aligned31124_31128 :
    AlignedValid 12 4 missing31124_31128 records31124_31128 :=
  aligned31124_31126.append aligned31126_31128

def missing31120_31128 : List (BitVec (edgeCount 12)) :=
  missing31120_31124 ++ missing31124_31128
abbrev records31120_31128 : List Blob :=
  records31120_31124 ++ records31124_31128
theorem aligned31120_31128 :
    AlignedValid 12 4 missing31120_31128 records31120_31128 :=
  aligned31120_31124.append aligned31124_31128

def missing31128_31129 : List (BitVec (edgeCount 12)) :=
  [missing31128]
abbrev records31128_31129 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31128]
theorem aligned31128_31129 :
    AlignedValid 12 4 missing31128_31129 records31128_31129 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31128
    maskCheck31128 AlignedValid.nil

def missing31129_31130 : List (BitVec (edgeCount 12)) :=
  [missing31129]
abbrev records31129_31130 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31129]
theorem aligned31129_31130 :
    AlignedValid 12 4 missing31129_31130 records31129_31130 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31129
    maskCheck31129 AlignedValid.nil

def missing31128_31130 : List (BitVec (edgeCount 12)) :=
  missing31128_31129 ++ missing31129_31130
abbrev records31128_31130 : List Blob :=
  records31128_31129 ++ records31129_31130
theorem aligned31128_31130 :
    AlignedValid 12 4 missing31128_31130 records31128_31130 :=
  aligned31128_31129.append aligned31129_31130

def missing31130_31131 : List (BitVec (edgeCount 12)) :=
  [missing31130]
abbrev records31130_31131 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31130]
theorem aligned31130_31131 :
    AlignedValid 12 4 missing31130_31131 records31130_31131 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31130
    maskCheck31130 AlignedValid.nil

def missing31131_31132 : List (BitVec (edgeCount 12)) :=
  [missing31131]
abbrev records31131_31132 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31131]
theorem aligned31131_31132 :
    AlignedValid 12 4 missing31131_31132 records31131_31132 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31131
    maskCheck31131 AlignedValid.nil

def missing31130_31132 : List (BitVec (edgeCount 12)) :=
  missing31130_31131 ++ missing31131_31132
abbrev records31130_31132 : List Blob :=
  records31130_31131 ++ records31131_31132
theorem aligned31130_31132 :
    AlignedValid 12 4 missing31130_31132 records31130_31132 :=
  aligned31130_31131.append aligned31131_31132

def missing31128_31132 : List (BitVec (edgeCount 12)) :=
  missing31128_31130 ++ missing31130_31132
abbrev records31128_31132 : List Blob :=
  records31128_31130 ++ records31130_31132
theorem aligned31128_31132 :
    AlignedValid 12 4 missing31128_31132 records31128_31132 :=
  aligned31128_31130.append aligned31130_31132

def missing31132_31133 : List (BitVec (edgeCount 12)) :=
  [missing31132]
abbrev records31132_31133 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31132]
theorem aligned31132_31133 :
    AlignedValid 12 4 missing31132_31133 records31132_31133 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31132
    maskCheck31132 AlignedValid.nil

def missing31133_31134 : List (BitVec (edgeCount 12)) :=
  [missing31133]
abbrev records31133_31134 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31133]
theorem aligned31133_31134 :
    AlignedValid 12 4 missing31133_31134 records31133_31134 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31133
    maskCheck31133 AlignedValid.nil

def missing31132_31134 : List (BitVec (edgeCount 12)) :=
  missing31132_31133 ++ missing31133_31134
abbrev records31132_31134 : List Blob :=
  records31132_31133 ++ records31133_31134
theorem aligned31132_31134 :
    AlignedValid 12 4 missing31132_31134 records31132_31134 :=
  aligned31132_31133.append aligned31133_31134

def missing31134_31135 : List (BitVec (edgeCount 12)) :=
  [missing31134]
abbrev records31134_31135 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31134]
theorem aligned31134_31135 :
    AlignedValid 12 4 missing31134_31135 records31134_31135 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31134
    maskCheck31134 AlignedValid.nil

def missing31135_31136 : List (BitVec (edgeCount 12)) :=
  [missing31135]
abbrev records31135_31136 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31135]
theorem aligned31135_31136 :
    AlignedValid 12 4 missing31135_31136 records31135_31136 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31135
    maskCheck31135 AlignedValid.nil

def missing31134_31136 : List (BitVec (edgeCount 12)) :=
  missing31134_31135 ++ missing31135_31136
abbrev records31134_31136 : List Blob :=
  records31134_31135 ++ records31135_31136
theorem aligned31134_31136 :
    AlignedValid 12 4 missing31134_31136 records31134_31136 :=
  aligned31134_31135.append aligned31135_31136

def missing31132_31136 : List (BitVec (edgeCount 12)) :=
  missing31132_31134 ++ missing31134_31136
abbrev records31132_31136 : List Blob :=
  records31132_31134 ++ records31134_31136
theorem aligned31132_31136 :
    AlignedValid 12 4 missing31132_31136 records31132_31136 :=
  aligned31132_31134.append aligned31134_31136

def missing31128_31136 : List (BitVec (edgeCount 12)) :=
  missing31128_31132 ++ missing31132_31136
abbrev records31128_31136 : List Blob :=
  records31128_31132 ++ records31132_31136
theorem aligned31128_31136 :
    AlignedValid 12 4 missing31128_31136 records31128_31136 :=
  aligned31128_31132.append aligned31132_31136

def missing31120_31136 : List (BitVec (edgeCount 12)) :=
  missing31120_31128 ++ missing31128_31136
abbrev records31120_31136 : List Blob :=
  records31120_31128 ++ records31128_31136
theorem aligned31120_31136 :
    AlignedValid 12 4 missing31120_31136 records31120_31136 :=
  aligned31120_31128.append aligned31128_31136

def missing31104_31136 : List (BitVec (edgeCount 12)) :=
  missing31104_31120 ++ missing31120_31136
abbrev records31104_31136 : List Blob :=
  records31104_31120 ++ records31120_31136
theorem aligned31104_31136 :
    AlignedValid 12 4 missing31104_31136 records31104_31136 :=
  aligned31104_31120.append aligned31120_31136

def missing31136_31137 : List (BitVec (edgeCount 12)) :=
  [missing31136]
abbrev records31136_31137 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31136]
theorem aligned31136_31137 :
    AlignedValid 12 4 missing31136_31137 records31136_31137 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31136
    maskCheck31136 AlignedValid.nil

def missing31137_31138 : List (BitVec (edgeCount 12)) :=
  [missing31137]
abbrev records31137_31138 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31137]
theorem aligned31137_31138 :
    AlignedValid 12 4 missing31137_31138 records31137_31138 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31137
    maskCheck31137 AlignedValid.nil

def missing31136_31138 : List (BitVec (edgeCount 12)) :=
  missing31136_31137 ++ missing31137_31138
abbrev records31136_31138 : List Blob :=
  records31136_31137 ++ records31137_31138
theorem aligned31136_31138 :
    AlignedValid 12 4 missing31136_31138 records31136_31138 :=
  aligned31136_31137.append aligned31137_31138

def missing31138_31139 : List (BitVec (edgeCount 12)) :=
  [missing31138]
abbrev records31138_31139 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31138]
theorem aligned31138_31139 :
    AlignedValid 12 4 missing31138_31139 records31138_31139 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31138
    maskCheck31138 AlignedValid.nil

def missing31139_31140 : List (BitVec (edgeCount 12)) :=
  [missing31139]
abbrev records31139_31140 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31139]
theorem aligned31139_31140 :
    AlignedValid 12 4 missing31139_31140 records31139_31140 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31139
    maskCheck31139 AlignedValid.nil

def missing31138_31140 : List (BitVec (edgeCount 12)) :=
  missing31138_31139 ++ missing31139_31140
abbrev records31138_31140 : List Blob :=
  records31138_31139 ++ records31139_31140
theorem aligned31138_31140 :
    AlignedValid 12 4 missing31138_31140 records31138_31140 :=
  aligned31138_31139.append aligned31139_31140

def missing31136_31140 : List (BitVec (edgeCount 12)) :=
  missing31136_31138 ++ missing31138_31140
abbrev records31136_31140 : List Blob :=
  records31136_31138 ++ records31138_31140
theorem aligned31136_31140 :
    AlignedValid 12 4 missing31136_31140 records31136_31140 :=
  aligned31136_31138.append aligned31138_31140

def missing31140_31141 : List (BitVec (edgeCount 12)) :=
  [missing31140]
abbrev records31140_31141 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31140]
theorem aligned31140_31141 :
    AlignedValid 12 4 missing31140_31141 records31140_31141 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31140
    maskCheck31140 AlignedValid.nil

def missing31141_31142 : List (BitVec (edgeCount 12)) :=
  [missing31141]
abbrev records31141_31142 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31141]
theorem aligned31141_31142 :
    AlignedValid 12 4 missing31141_31142 records31141_31142 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31141
    maskCheck31141 AlignedValid.nil

def missing31140_31142 : List (BitVec (edgeCount 12)) :=
  missing31140_31141 ++ missing31141_31142
abbrev records31140_31142 : List Blob :=
  records31140_31141 ++ records31141_31142
theorem aligned31140_31142 :
    AlignedValid 12 4 missing31140_31142 records31140_31142 :=
  aligned31140_31141.append aligned31141_31142

def missing31142_31143 : List (BitVec (edgeCount 12)) :=
  [missing31142]
abbrev records31142_31143 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31142]
theorem aligned31142_31143 :
    AlignedValid 12 4 missing31142_31143 records31142_31143 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31142
    maskCheck31142 AlignedValid.nil

def missing31143_31144 : List (BitVec (edgeCount 12)) :=
  [missing31143]
abbrev records31143_31144 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31143]
theorem aligned31143_31144 :
    AlignedValid 12 4 missing31143_31144 records31143_31144 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31143
    maskCheck31143 AlignedValid.nil

def missing31142_31144 : List (BitVec (edgeCount 12)) :=
  missing31142_31143 ++ missing31143_31144
abbrev records31142_31144 : List Blob :=
  records31142_31143 ++ records31143_31144
theorem aligned31142_31144 :
    AlignedValid 12 4 missing31142_31144 records31142_31144 :=
  aligned31142_31143.append aligned31143_31144

def missing31140_31144 : List (BitVec (edgeCount 12)) :=
  missing31140_31142 ++ missing31142_31144
abbrev records31140_31144 : List Blob :=
  records31140_31142 ++ records31142_31144
theorem aligned31140_31144 :
    AlignedValid 12 4 missing31140_31144 records31140_31144 :=
  aligned31140_31142.append aligned31142_31144

def missing31136_31144 : List (BitVec (edgeCount 12)) :=
  missing31136_31140 ++ missing31140_31144
abbrev records31136_31144 : List Blob :=
  records31136_31140 ++ records31140_31144
theorem aligned31136_31144 :
    AlignedValid 12 4 missing31136_31144 records31136_31144 :=
  aligned31136_31140.append aligned31140_31144

def missing31144_31145 : List (BitVec (edgeCount 12)) :=
  [missing31144]
abbrev records31144_31145 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31144]
theorem aligned31144_31145 :
    AlignedValid 12 4 missing31144_31145 records31144_31145 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31144
    maskCheck31144 AlignedValid.nil

def missing31145_31146 : List (BitVec (edgeCount 12)) :=
  [missing31145]
abbrev records31145_31146 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31145]
theorem aligned31145_31146 :
    AlignedValid 12 4 missing31145_31146 records31145_31146 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31145
    maskCheck31145 AlignedValid.nil

def missing31144_31146 : List (BitVec (edgeCount 12)) :=
  missing31144_31145 ++ missing31145_31146
abbrev records31144_31146 : List Blob :=
  records31144_31145 ++ records31145_31146
theorem aligned31144_31146 :
    AlignedValid 12 4 missing31144_31146 records31144_31146 :=
  aligned31144_31145.append aligned31145_31146

def missing31146_31147 : List (BitVec (edgeCount 12)) :=
  [missing31146]
abbrev records31146_31147 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31146]
theorem aligned31146_31147 :
    AlignedValid 12 4 missing31146_31147 records31146_31147 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31146
    maskCheck31146 AlignedValid.nil

def missing31147_31148 : List (BitVec (edgeCount 12)) :=
  [missing31147]
abbrev records31147_31148 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31147]
theorem aligned31147_31148 :
    AlignedValid 12 4 missing31147_31148 records31147_31148 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31147
    maskCheck31147 AlignedValid.nil

def missing31146_31148 : List (BitVec (edgeCount 12)) :=
  missing31146_31147 ++ missing31147_31148
abbrev records31146_31148 : List Blob :=
  records31146_31147 ++ records31147_31148
theorem aligned31146_31148 :
    AlignedValid 12 4 missing31146_31148 records31146_31148 :=
  aligned31146_31147.append aligned31147_31148

def missing31144_31148 : List (BitVec (edgeCount 12)) :=
  missing31144_31146 ++ missing31146_31148
abbrev records31144_31148 : List Blob :=
  records31144_31146 ++ records31146_31148
theorem aligned31144_31148 :
    AlignedValid 12 4 missing31144_31148 records31144_31148 :=
  aligned31144_31146.append aligned31146_31148

def missing31148_31149 : List (BitVec (edgeCount 12)) :=
  [missing31148]
abbrev records31148_31149 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31148]
theorem aligned31148_31149 :
    AlignedValid 12 4 missing31148_31149 records31148_31149 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31148
    maskCheck31148 AlignedValid.nil

def missing31149_31150 : List (BitVec (edgeCount 12)) :=
  [missing31149]
abbrev records31149_31150 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31149]
theorem aligned31149_31150 :
    AlignedValid 12 4 missing31149_31150 records31149_31150 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31149
    maskCheck31149 AlignedValid.nil

def missing31148_31150 : List (BitVec (edgeCount 12)) :=
  missing31148_31149 ++ missing31149_31150
abbrev records31148_31150 : List Blob :=
  records31148_31149 ++ records31149_31150
theorem aligned31148_31150 :
    AlignedValid 12 4 missing31148_31150 records31148_31150 :=
  aligned31148_31149.append aligned31149_31150

def missing31150_31151 : List (BitVec (edgeCount 12)) :=
  [missing31150]
abbrev records31150_31151 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31150]
theorem aligned31150_31151 :
    AlignedValid 12 4 missing31150_31151 records31150_31151 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31150
    maskCheck31150 AlignedValid.nil

def missing31151_31152 : List (BitVec (edgeCount 12)) :=
  [missing31151]
abbrev records31151_31152 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31151]
theorem aligned31151_31152 :
    AlignedValid 12 4 missing31151_31152 records31151_31152 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31151
    maskCheck31151 AlignedValid.nil

def missing31150_31152 : List (BitVec (edgeCount 12)) :=
  missing31150_31151 ++ missing31151_31152
abbrev records31150_31152 : List Blob :=
  records31150_31151 ++ records31151_31152
theorem aligned31150_31152 :
    AlignedValid 12 4 missing31150_31152 records31150_31152 :=
  aligned31150_31151.append aligned31151_31152

def missing31148_31152 : List (BitVec (edgeCount 12)) :=
  missing31148_31150 ++ missing31150_31152
abbrev records31148_31152 : List Blob :=
  records31148_31150 ++ records31150_31152
theorem aligned31148_31152 :
    AlignedValid 12 4 missing31148_31152 records31148_31152 :=
  aligned31148_31150.append aligned31150_31152

def missing31144_31152 : List (BitVec (edgeCount 12)) :=
  missing31144_31148 ++ missing31148_31152
abbrev records31144_31152 : List Blob :=
  records31144_31148 ++ records31148_31152
theorem aligned31144_31152 :
    AlignedValid 12 4 missing31144_31152 records31144_31152 :=
  aligned31144_31148.append aligned31148_31152

def missing31136_31152 : List (BitVec (edgeCount 12)) :=
  missing31136_31144 ++ missing31144_31152
abbrev records31136_31152 : List Blob :=
  records31136_31144 ++ records31144_31152
theorem aligned31136_31152 :
    AlignedValid 12 4 missing31136_31152 records31136_31152 :=
  aligned31136_31144.append aligned31144_31152

def missing31152_31153 : List (BitVec (edgeCount 12)) :=
  [missing31152]
abbrev records31152_31153 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31152]
theorem aligned31152_31153 :
    AlignedValid 12 4 missing31152_31153 records31152_31153 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31152
    maskCheck31152 AlignedValid.nil

def missing31153_31154 : List (BitVec (edgeCount 12)) :=
  [missing31153]
abbrev records31153_31154 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31153]
theorem aligned31153_31154 :
    AlignedValid 12 4 missing31153_31154 records31153_31154 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31153
    maskCheck31153 AlignedValid.nil

def missing31152_31154 : List (BitVec (edgeCount 12)) :=
  missing31152_31153 ++ missing31153_31154
abbrev records31152_31154 : List Blob :=
  records31152_31153 ++ records31153_31154
theorem aligned31152_31154 :
    AlignedValid 12 4 missing31152_31154 records31152_31154 :=
  aligned31152_31153.append aligned31153_31154

def missing31154_31155 : List (BitVec (edgeCount 12)) :=
  [missing31154]
abbrev records31154_31155 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31154]
theorem aligned31154_31155 :
    AlignedValid 12 4 missing31154_31155 records31154_31155 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31154
    maskCheck31154 AlignedValid.nil

def missing31155_31156 : List (BitVec (edgeCount 12)) :=
  [missing31155]
abbrev records31155_31156 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31155]
theorem aligned31155_31156 :
    AlignedValid 12 4 missing31155_31156 records31155_31156 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31155
    maskCheck31155 AlignedValid.nil

def missing31154_31156 : List (BitVec (edgeCount 12)) :=
  missing31154_31155 ++ missing31155_31156
abbrev records31154_31156 : List Blob :=
  records31154_31155 ++ records31155_31156
theorem aligned31154_31156 :
    AlignedValid 12 4 missing31154_31156 records31154_31156 :=
  aligned31154_31155.append aligned31155_31156

def missing31152_31156 : List (BitVec (edgeCount 12)) :=
  missing31152_31154 ++ missing31154_31156
abbrev records31152_31156 : List Blob :=
  records31152_31154 ++ records31154_31156
theorem aligned31152_31156 :
    AlignedValid 12 4 missing31152_31156 records31152_31156 :=
  aligned31152_31154.append aligned31154_31156

def missing31156_31157 : List (BitVec (edgeCount 12)) :=
  [missing31156]
abbrev records31156_31157 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31156]
theorem aligned31156_31157 :
    AlignedValid 12 4 missing31156_31157 records31156_31157 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31156
    maskCheck31156 AlignedValid.nil

def missing31157_31158 : List (BitVec (edgeCount 12)) :=
  [missing31157]
abbrev records31157_31158 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31157]
theorem aligned31157_31158 :
    AlignedValid 12 4 missing31157_31158 records31157_31158 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31157
    maskCheck31157 AlignedValid.nil

def missing31156_31158 : List (BitVec (edgeCount 12)) :=
  missing31156_31157 ++ missing31157_31158
abbrev records31156_31158 : List Blob :=
  records31156_31157 ++ records31157_31158
theorem aligned31156_31158 :
    AlignedValid 12 4 missing31156_31158 records31156_31158 :=
  aligned31156_31157.append aligned31157_31158

def missing31158_31159 : List (BitVec (edgeCount 12)) :=
  [missing31158]
abbrev records31158_31159 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31158]
theorem aligned31158_31159 :
    AlignedValid 12 4 missing31158_31159 records31158_31159 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31158
    maskCheck31158 AlignedValid.nil

def missing31159_31160 : List (BitVec (edgeCount 12)) :=
  [missing31159]
abbrev records31159_31160 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31159]
theorem aligned31159_31160 :
    AlignedValid 12 4 missing31159_31160 records31159_31160 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31159
    maskCheck31159 AlignedValid.nil

def missing31158_31160 : List (BitVec (edgeCount 12)) :=
  missing31158_31159 ++ missing31159_31160
abbrev records31158_31160 : List Blob :=
  records31158_31159 ++ records31159_31160
theorem aligned31158_31160 :
    AlignedValid 12 4 missing31158_31160 records31158_31160 :=
  aligned31158_31159.append aligned31159_31160

def missing31156_31160 : List (BitVec (edgeCount 12)) :=
  missing31156_31158 ++ missing31158_31160
abbrev records31156_31160 : List Blob :=
  records31156_31158 ++ records31158_31160
theorem aligned31156_31160 :
    AlignedValid 12 4 missing31156_31160 records31156_31160 :=
  aligned31156_31158.append aligned31158_31160

def missing31152_31160 : List (BitVec (edgeCount 12)) :=
  missing31152_31156 ++ missing31156_31160
abbrev records31152_31160 : List Blob :=
  records31152_31156 ++ records31156_31160
theorem aligned31152_31160 :
    AlignedValid 12 4 missing31152_31160 records31152_31160 :=
  aligned31152_31156.append aligned31156_31160

def missing31160_31161 : List (BitVec (edgeCount 12)) :=
  [missing31160]
abbrev records31160_31161 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31160]
theorem aligned31160_31161 :
    AlignedValid 12 4 missing31160_31161 records31160_31161 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31160
    maskCheck31160 AlignedValid.nil

def missing31161_31162 : List (BitVec (edgeCount 12)) :=
  [missing31161]
abbrev records31161_31162 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31161]
theorem aligned31161_31162 :
    AlignedValid 12 4 missing31161_31162 records31161_31162 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31161
    maskCheck31161 AlignedValid.nil

def missing31160_31162 : List (BitVec (edgeCount 12)) :=
  missing31160_31161 ++ missing31161_31162
abbrev records31160_31162 : List Blob :=
  records31160_31161 ++ records31161_31162
theorem aligned31160_31162 :
    AlignedValid 12 4 missing31160_31162 records31160_31162 :=
  aligned31160_31161.append aligned31161_31162

def missing31162_31163 : List (BitVec (edgeCount 12)) :=
  [missing31162]
abbrev records31162_31163 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31162]
theorem aligned31162_31163 :
    AlignedValid 12 4 missing31162_31163 records31162_31163 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31162
    maskCheck31162 AlignedValid.nil

def missing31163_31164 : List (BitVec (edgeCount 12)) :=
  [missing31163]
abbrev records31163_31164 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31163]
theorem aligned31163_31164 :
    AlignedValid 12 4 missing31163_31164 records31163_31164 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31163
    maskCheck31163 AlignedValid.nil

def missing31162_31164 : List (BitVec (edgeCount 12)) :=
  missing31162_31163 ++ missing31163_31164
abbrev records31162_31164 : List Blob :=
  records31162_31163 ++ records31163_31164
theorem aligned31162_31164 :
    AlignedValid 12 4 missing31162_31164 records31162_31164 :=
  aligned31162_31163.append aligned31163_31164

def missing31160_31164 : List (BitVec (edgeCount 12)) :=
  missing31160_31162 ++ missing31162_31164
abbrev records31160_31164 : List Blob :=
  records31160_31162 ++ records31162_31164
theorem aligned31160_31164 :
    AlignedValid 12 4 missing31160_31164 records31160_31164 :=
  aligned31160_31162.append aligned31162_31164

def missing31164_31165 : List (BitVec (edgeCount 12)) :=
  [missing31164]
abbrev records31164_31165 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31164]
theorem aligned31164_31165 :
    AlignedValid 12 4 missing31164_31165 records31164_31165 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31164
    maskCheck31164 AlignedValid.nil

def missing31165_31166 : List (BitVec (edgeCount 12)) :=
  [missing31165]
abbrev records31165_31166 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31165]
theorem aligned31165_31166 :
    AlignedValid 12 4 missing31165_31166 records31165_31166 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31165
    maskCheck31165 AlignedValid.nil

def missing31164_31166 : List (BitVec (edgeCount 12)) :=
  missing31164_31165 ++ missing31165_31166
abbrev records31164_31166 : List Blob :=
  records31164_31165 ++ records31165_31166
theorem aligned31164_31166 :
    AlignedValid 12 4 missing31164_31166 records31164_31166 :=
  aligned31164_31165.append aligned31165_31166

def missing31166_31167 : List (BitVec (edgeCount 12)) :=
  [missing31166]
abbrev records31166_31167 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31166]
theorem aligned31166_31167 :
    AlignedValid 12 4 missing31166_31167 records31166_31167 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31166
    maskCheck31166 AlignedValid.nil

def missing31167_31168 : List (BitVec (edgeCount 12)) :=
  [missing31167]
abbrev records31167_31168 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31167]
theorem aligned31167_31168 :
    AlignedValid 12 4 missing31167_31168 records31167_31168 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31167
    maskCheck31167 AlignedValid.nil

def missing31166_31168 : List (BitVec (edgeCount 12)) :=
  missing31166_31167 ++ missing31167_31168
abbrev records31166_31168 : List Blob :=
  records31166_31167 ++ records31167_31168
theorem aligned31166_31168 :
    AlignedValid 12 4 missing31166_31168 records31166_31168 :=
  aligned31166_31167.append aligned31167_31168

def missing31164_31168 : List (BitVec (edgeCount 12)) :=
  missing31164_31166 ++ missing31166_31168
abbrev records31164_31168 : List Blob :=
  records31164_31166 ++ records31166_31168
theorem aligned31164_31168 :
    AlignedValid 12 4 missing31164_31168 records31164_31168 :=
  aligned31164_31166.append aligned31166_31168

def missing31160_31168 : List (BitVec (edgeCount 12)) :=
  missing31160_31164 ++ missing31164_31168
abbrev records31160_31168 : List Blob :=
  records31160_31164 ++ records31164_31168
theorem aligned31160_31168 :
    AlignedValid 12 4 missing31160_31168 records31160_31168 :=
  aligned31160_31164.append aligned31164_31168

def missing31152_31168 : List (BitVec (edgeCount 12)) :=
  missing31152_31160 ++ missing31160_31168
abbrev records31152_31168 : List Blob :=
  records31152_31160 ++ records31160_31168
theorem aligned31152_31168 :
    AlignedValid 12 4 missing31152_31168 records31152_31168 :=
  aligned31152_31160.append aligned31160_31168

def missing31136_31168 : List (BitVec (edgeCount 12)) :=
  missing31136_31152 ++ missing31152_31168
abbrev records31136_31168 : List Blob :=
  records31136_31152 ++ records31152_31168
theorem aligned31136_31168 :
    AlignedValid 12 4 missing31136_31168 records31136_31168 :=
  aligned31136_31152.append aligned31152_31168

def missing31104_31168 : List (BitVec (edgeCount 12)) :=
  missing31104_31136 ++ missing31136_31168
abbrev records31104_31168 : List Blob :=
  records31104_31136 ++ records31136_31168
theorem aligned31104_31168 :
    AlignedValid 12 4 missing31104_31168 records31104_31168 :=
  aligned31104_31136.append aligned31136_31168

def missing31168_31169 : List (BitVec (edgeCount 12)) :=
  [missing31168]
abbrev records31168_31169 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31168]
theorem aligned31168_31169 :
    AlignedValid 12 4 missing31168_31169 records31168_31169 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31168
    maskCheck31168 AlignedValid.nil

def missing31169_31170 : List (BitVec (edgeCount 12)) :=
  [missing31169]
abbrev records31169_31170 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31169]
theorem aligned31169_31170 :
    AlignedValid 12 4 missing31169_31170 records31169_31170 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31169
    maskCheck31169 AlignedValid.nil

def missing31168_31170 : List (BitVec (edgeCount 12)) :=
  missing31168_31169 ++ missing31169_31170
abbrev records31168_31170 : List Blob :=
  records31168_31169 ++ records31169_31170
theorem aligned31168_31170 :
    AlignedValid 12 4 missing31168_31170 records31168_31170 :=
  aligned31168_31169.append aligned31169_31170

def missing31170_31171 : List (BitVec (edgeCount 12)) :=
  [missing31170]
abbrev records31170_31171 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31170]
theorem aligned31170_31171 :
    AlignedValid 12 4 missing31170_31171 records31170_31171 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31170
    maskCheck31170 AlignedValid.nil

def missing31171_31172 : List (BitVec (edgeCount 12)) :=
  [missing31171]
abbrev records31171_31172 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31171]
theorem aligned31171_31172 :
    AlignedValid 12 4 missing31171_31172 records31171_31172 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31171
    maskCheck31171 AlignedValid.nil

def missing31170_31172 : List (BitVec (edgeCount 12)) :=
  missing31170_31171 ++ missing31171_31172
abbrev records31170_31172 : List Blob :=
  records31170_31171 ++ records31171_31172
theorem aligned31170_31172 :
    AlignedValid 12 4 missing31170_31172 records31170_31172 :=
  aligned31170_31171.append aligned31171_31172

def missing31168_31172 : List (BitVec (edgeCount 12)) :=
  missing31168_31170 ++ missing31170_31172
abbrev records31168_31172 : List Blob :=
  records31168_31170 ++ records31170_31172
theorem aligned31168_31172 :
    AlignedValid 12 4 missing31168_31172 records31168_31172 :=
  aligned31168_31170.append aligned31170_31172

def missing31172_31173 : List (BitVec (edgeCount 12)) :=
  [missing31172]
abbrev records31172_31173 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31172]
theorem aligned31172_31173 :
    AlignedValid 12 4 missing31172_31173 records31172_31173 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31172
    maskCheck31172 AlignedValid.nil

def missing31173_31174 : List (BitVec (edgeCount 12)) :=
  [missing31173]
abbrev records31173_31174 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31173]
theorem aligned31173_31174 :
    AlignedValid 12 4 missing31173_31174 records31173_31174 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31173
    maskCheck31173 AlignedValid.nil

def missing31172_31174 : List (BitVec (edgeCount 12)) :=
  missing31172_31173 ++ missing31173_31174
abbrev records31172_31174 : List Blob :=
  records31172_31173 ++ records31173_31174
theorem aligned31172_31174 :
    AlignedValid 12 4 missing31172_31174 records31172_31174 :=
  aligned31172_31173.append aligned31173_31174

def missing31174_31175 : List (BitVec (edgeCount 12)) :=
  [missing31174]
abbrev records31174_31175 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31174]
theorem aligned31174_31175 :
    AlignedValid 12 4 missing31174_31175 records31174_31175 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31174
    maskCheck31174 AlignedValid.nil

def missing31175_31176 : List (BitVec (edgeCount 12)) :=
  [missing31175]
abbrev records31175_31176 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31175]
theorem aligned31175_31176 :
    AlignedValid 12 4 missing31175_31176 records31175_31176 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31175
    maskCheck31175 AlignedValid.nil

def missing31174_31176 : List (BitVec (edgeCount 12)) :=
  missing31174_31175 ++ missing31175_31176
abbrev records31174_31176 : List Blob :=
  records31174_31175 ++ records31175_31176
theorem aligned31174_31176 :
    AlignedValid 12 4 missing31174_31176 records31174_31176 :=
  aligned31174_31175.append aligned31175_31176

def missing31172_31176 : List (BitVec (edgeCount 12)) :=
  missing31172_31174 ++ missing31174_31176
abbrev records31172_31176 : List Blob :=
  records31172_31174 ++ records31174_31176
theorem aligned31172_31176 :
    AlignedValid 12 4 missing31172_31176 records31172_31176 :=
  aligned31172_31174.append aligned31174_31176

def missing31168_31176 : List (BitVec (edgeCount 12)) :=
  missing31168_31172 ++ missing31172_31176
abbrev records31168_31176 : List Blob :=
  records31168_31172 ++ records31172_31176
theorem aligned31168_31176 :
    AlignedValid 12 4 missing31168_31176 records31168_31176 :=
  aligned31168_31172.append aligned31172_31176

def missing31176_31177 : List (BitVec (edgeCount 12)) :=
  [missing31176]
abbrev records31176_31177 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31176]
theorem aligned31176_31177 :
    AlignedValid 12 4 missing31176_31177 records31176_31177 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31176
    maskCheck31176 AlignedValid.nil

def missing31177_31178 : List (BitVec (edgeCount 12)) :=
  [missing31177]
abbrev records31177_31178 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31177]
theorem aligned31177_31178 :
    AlignedValid 12 4 missing31177_31178 records31177_31178 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31177
    maskCheck31177 AlignedValid.nil

def missing31176_31178 : List (BitVec (edgeCount 12)) :=
  missing31176_31177 ++ missing31177_31178
abbrev records31176_31178 : List Blob :=
  records31176_31177 ++ records31177_31178
theorem aligned31176_31178 :
    AlignedValid 12 4 missing31176_31178 records31176_31178 :=
  aligned31176_31177.append aligned31177_31178

def missing31178_31179 : List (BitVec (edgeCount 12)) :=
  [missing31178]
abbrev records31178_31179 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31178]
theorem aligned31178_31179 :
    AlignedValid 12 4 missing31178_31179 records31178_31179 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31178
    maskCheck31178 AlignedValid.nil

def missing31179_31180 : List (BitVec (edgeCount 12)) :=
  [missing31179]
abbrev records31179_31180 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31179]
theorem aligned31179_31180 :
    AlignedValid 12 4 missing31179_31180 records31179_31180 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31179
    maskCheck31179 AlignedValid.nil

def missing31178_31180 : List (BitVec (edgeCount 12)) :=
  missing31178_31179 ++ missing31179_31180
abbrev records31178_31180 : List Blob :=
  records31178_31179 ++ records31179_31180
theorem aligned31178_31180 :
    AlignedValid 12 4 missing31178_31180 records31178_31180 :=
  aligned31178_31179.append aligned31179_31180

def missing31176_31180 : List (BitVec (edgeCount 12)) :=
  missing31176_31178 ++ missing31178_31180
abbrev records31176_31180 : List Blob :=
  records31176_31178 ++ records31178_31180
theorem aligned31176_31180 :
    AlignedValid 12 4 missing31176_31180 records31176_31180 :=
  aligned31176_31178.append aligned31178_31180

def missing31180_31181 : List (BitVec (edgeCount 12)) :=
  [missing31180]
abbrev records31180_31181 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31180]
theorem aligned31180_31181 :
    AlignedValid 12 4 missing31180_31181 records31180_31181 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31180
    maskCheck31180 AlignedValid.nil

def missing31181_31182 : List (BitVec (edgeCount 12)) :=
  [missing31181]
abbrev records31181_31182 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31181]
theorem aligned31181_31182 :
    AlignedValid 12 4 missing31181_31182 records31181_31182 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31181
    maskCheck31181 AlignedValid.nil

def missing31180_31182 : List (BitVec (edgeCount 12)) :=
  missing31180_31181 ++ missing31181_31182
abbrev records31180_31182 : List Blob :=
  records31180_31181 ++ records31181_31182
theorem aligned31180_31182 :
    AlignedValid 12 4 missing31180_31182 records31180_31182 :=
  aligned31180_31181.append aligned31181_31182

def missing31182_31183 : List (BitVec (edgeCount 12)) :=
  [missing31182]
abbrev records31182_31183 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31182]
theorem aligned31182_31183 :
    AlignedValid 12 4 missing31182_31183 records31182_31183 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31182
    maskCheck31182 AlignedValid.nil

def missing31183_31184 : List (BitVec (edgeCount 12)) :=
  [missing31183]
abbrev records31183_31184 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31183]
theorem aligned31183_31184 :
    AlignedValid 12 4 missing31183_31184 records31183_31184 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31183
    maskCheck31183 AlignedValid.nil

def missing31182_31184 : List (BitVec (edgeCount 12)) :=
  missing31182_31183 ++ missing31183_31184
abbrev records31182_31184 : List Blob :=
  records31182_31183 ++ records31183_31184
theorem aligned31182_31184 :
    AlignedValid 12 4 missing31182_31184 records31182_31184 :=
  aligned31182_31183.append aligned31183_31184

def missing31180_31184 : List (BitVec (edgeCount 12)) :=
  missing31180_31182 ++ missing31182_31184
abbrev records31180_31184 : List Blob :=
  records31180_31182 ++ records31182_31184
theorem aligned31180_31184 :
    AlignedValid 12 4 missing31180_31184 records31180_31184 :=
  aligned31180_31182.append aligned31182_31184

def missing31176_31184 : List (BitVec (edgeCount 12)) :=
  missing31176_31180 ++ missing31180_31184
abbrev records31176_31184 : List Blob :=
  records31176_31180 ++ records31180_31184
theorem aligned31176_31184 :
    AlignedValid 12 4 missing31176_31184 records31176_31184 :=
  aligned31176_31180.append aligned31180_31184

def missing31168_31184 : List (BitVec (edgeCount 12)) :=
  missing31168_31176 ++ missing31176_31184
abbrev records31168_31184 : List Blob :=
  records31168_31176 ++ records31176_31184
theorem aligned31168_31184 :
    AlignedValid 12 4 missing31168_31184 records31168_31184 :=
  aligned31168_31176.append aligned31176_31184

def missing31184_31185 : List (BitVec (edgeCount 12)) :=
  [missing31184]
abbrev records31184_31185 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31184]
theorem aligned31184_31185 :
    AlignedValid 12 4 missing31184_31185 records31184_31185 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31184
    maskCheck31184 AlignedValid.nil

def missing31185_31186 : List (BitVec (edgeCount 12)) :=
  [missing31185]
abbrev records31185_31186 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31185]
theorem aligned31185_31186 :
    AlignedValid 12 4 missing31185_31186 records31185_31186 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31185
    maskCheck31185 AlignedValid.nil

def missing31184_31186 : List (BitVec (edgeCount 12)) :=
  missing31184_31185 ++ missing31185_31186
abbrev records31184_31186 : List Blob :=
  records31184_31185 ++ records31185_31186
theorem aligned31184_31186 :
    AlignedValid 12 4 missing31184_31186 records31184_31186 :=
  aligned31184_31185.append aligned31185_31186

def missing31186_31187 : List (BitVec (edgeCount 12)) :=
  [missing31186]
abbrev records31186_31187 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31186]
theorem aligned31186_31187 :
    AlignedValid 12 4 missing31186_31187 records31186_31187 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31186
    maskCheck31186 AlignedValid.nil

def missing31187_31188 : List (BitVec (edgeCount 12)) :=
  [missing31187]
abbrev records31187_31188 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31187]
theorem aligned31187_31188 :
    AlignedValid 12 4 missing31187_31188 records31187_31188 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31187
    maskCheck31187 AlignedValid.nil

def missing31186_31188 : List (BitVec (edgeCount 12)) :=
  missing31186_31187 ++ missing31187_31188
abbrev records31186_31188 : List Blob :=
  records31186_31187 ++ records31187_31188
theorem aligned31186_31188 :
    AlignedValid 12 4 missing31186_31188 records31186_31188 :=
  aligned31186_31187.append aligned31187_31188

def missing31184_31188 : List (BitVec (edgeCount 12)) :=
  missing31184_31186 ++ missing31186_31188
abbrev records31184_31188 : List Blob :=
  records31184_31186 ++ records31186_31188
theorem aligned31184_31188 :
    AlignedValid 12 4 missing31184_31188 records31184_31188 :=
  aligned31184_31186.append aligned31186_31188

def missing31188_31189 : List (BitVec (edgeCount 12)) :=
  [missing31188]
abbrev records31188_31189 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31188]
theorem aligned31188_31189 :
    AlignedValid 12 4 missing31188_31189 records31188_31189 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31188
    maskCheck31188 AlignedValid.nil

def missing31189_31190 : List (BitVec (edgeCount 12)) :=
  [missing31189]
abbrev records31189_31190 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31189]
theorem aligned31189_31190 :
    AlignedValid 12 4 missing31189_31190 records31189_31190 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31189
    maskCheck31189 AlignedValid.nil

def missing31188_31190 : List (BitVec (edgeCount 12)) :=
  missing31188_31189 ++ missing31189_31190
abbrev records31188_31190 : List Blob :=
  records31188_31189 ++ records31189_31190
theorem aligned31188_31190 :
    AlignedValid 12 4 missing31188_31190 records31188_31190 :=
  aligned31188_31189.append aligned31189_31190

def missing31190_31191 : List (BitVec (edgeCount 12)) :=
  [missing31190]
abbrev records31190_31191 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31190]
theorem aligned31190_31191 :
    AlignedValid 12 4 missing31190_31191 records31190_31191 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31190
    maskCheck31190 AlignedValid.nil

def missing31191_31192 : List (BitVec (edgeCount 12)) :=
  [missing31191]
abbrev records31191_31192 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31191]
theorem aligned31191_31192 :
    AlignedValid 12 4 missing31191_31192 records31191_31192 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31191
    maskCheck31191 AlignedValid.nil

def missing31190_31192 : List (BitVec (edgeCount 12)) :=
  missing31190_31191 ++ missing31191_31192
abbrev records31190_31192 : List Blob :=
  records31190_31191 ++ records31191_31192
theorem aligned31190_31192 :
    AlignedValid 12 4 missing31190_31192 records31190_31192 :=
  aligned31190_31191.append aligned31191_31192

def missing31188_31192 : List (BitVec (edgeCount 12)) :=
  missing31188_31190 ++ missing31190_31192
abbrev records31188_31192 : List Blob :=
  records31188_31190 ++ records31190_31192
theorem aligned31188_31192 :
    AlignedValid 12 4 missing31188_31192 records31188_31192 :=
  aligned31188_31190.append aligned31190_31192

def missing31184_31192 : List (BitVec (edgeCount 12)) :=
  missing31184_31188 ++ missing31188_31192
abbrev records31184_31192 : List Blob :=
  records31184_31188 ++ records31188_31192
theorem aligned31184_31192 :
    AlignedValid 12 4 missing31184_31192 records31184_31192 :=
  aligned31184_31188.append aligned31188_31192

def missing31192_31193 : List (BitVec (edgeCount 12)) :=
  [missing31192]
abbrev records31192_31193 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31192]
theorem aligned31192_31193 :
    AlignedValid 12 4 missing31192_31193 records31192_31193 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31192
    maskCheck31192 AlignedValid.nil

def missing31193_31194 : List (BitVec (edgeCount 12)) :=
  [missing31193]
abbrev records31193_31194 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31193]
theorem aligned31193_31194 :
    AlignedValid 12 4 missing31193_31194 records31193_31194 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31193
    maskCheck31193 AlignedValid.nil

def missing31192_31194 : List (BitVec (edgeCount 12)) :=
  missing31192_31193 ++ missing31193_31194
abbrev records31192_31194 : List Blob :=
  records31192_31193 ++ records31193_31194
theorem aligned31192_31194 :
    AlignedValid 12 4 missing31192_31194 records31192_31194 :=
  aligned31192_31193.append aligned31193_31194

def missing31194_31195 : List (BitVec (edgeCount 12)) :=
  [missing31194]
abbrev records31194_31195 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31194]
theorem aligned31194_31195 :
    AlignedValid 12 4 missing31194_31195 records31194_31195 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31194
    maskCheck31194 AlignedValid.nil

def missing31195_31196 : List (BitVec (edgeCount 12)) :=
  [missing31195]
abbrev records31195_31196 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31195]
theorem aligned31195_31196 :
    AlignedValid 12 4 missing31195_31196 records31195_31196 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31195
    maskCheck31195 AlignedValid.nil

def missing31194_31196 : List (BitVec (edgeCount 12)) :=
  missing31194_31195 ++ missing31195_31196
abbrev records31194_31196 : List Blob :=
  records31194_31195 ++ records31195_31196
theorem aligned31194_31196 :
    AlignedValid 12 4 missing31194_31196 records31194_31196 :=
  aligned31194_31195.append aligned31195_31196

def missing31192_31196 : List (BitVec (edgeCount 12)) :=
  missing31192_31194 ++ missing31194_31196
abbrev records31192_31196 : List Blob :=
  records31192_31194 ++ records31194_31196
theorem aligned31192_31196 :
    AlignedValid 12 4 missing31192_31196 records31192_31196 :=
  aligned31192_31194.append aligned31194_31196

def missing31196_31197 : List (BitVec (edgeCount 12)) :=
  [missing31196]
abbrev records31196_31197 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31196]
theorem aligned31196_31197 :
    AlignedValid 12 4 missing31196_31197 records31196_31197 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31196
    maskCheck31196 AlignedValid.nil

def missing31197_31198 : List (BitVec (edgeCount 12)) :=
  [missing31197]
abbrev records31197_31198 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31197]
theorem aligned31197_31198 :
    AlignedValid 12 4 missing31197_31198 records31197_31198 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31197
    maskCheck31197 AlignedValid.nil

def missing31196_31198 : List (BitVec (edgeCount 12)) :=
  missing31196_31197 ++ missing31197_31198
abbrev records31196_31198 : List Blob :=
  records31196_31197 ++ records31197_31198
theorem aligned31196_31198 :
    AlignedValid 12 4 missing31196_31198 records31196_31198 :=
  aligned31196_31197.append aligned31197_31198

def missing31198_31199 : List (BitVec (edgeCount 12)) :=
  [missing31198]
abbrev records31198_31199 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31198]
theorem aligned31198_31199 :
    AlignedValid 12 4 missing31198_31199 records31198_31199 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31198
    maskCheck31198 AlignedValid.nil

def missing31199_31200 : List (BitVec (edgeCount 12)) :=
  [missing31199]
abbrev records31199_31200 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31199]
theorem aligned31199_31200 :
    AlignedValid 12 4 missing31199_31200 records31199_31200 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31199
    maskCheck31199 AlignedValid.nil

def missing31198_31200 : List (BitVec (edgeCount 12)) :=
  missing31198_31199 ++ missing31199_31200
abbrev records31198_31200 : List Blob :=
  records31198_31199 ++ records31199_31200
theorem aligned31198_31200 :
    AlignedValid 12 4 missing31198_31200 records31198_31200 :=
  aligned31198_31199.append aligned31199_31200

def missing31196_31200 : List (BitVec (edgeCount 12)) :=
  missing31196_31198 ++ missing31198_31200
abbrev records31196_31200 : List Blob :=
  records31196_31198 ++ records31198_31200
theorem aligned31196_31200 :
    AlignedValid 12 4 missing31196_31200 records31196_31200 :=
  aligned31196_31198.append aligned31198_31200

def missing31192_31200 : List (BitVec (edgeCount 12)) :=
  missing31192_31196 ++ missing31196_31200
abbrev records31192_31200 : List Blob :=
  records31192_31196 ++ records31196_31200
theorem aligned31192_31200 :
    AlignedValid 12 4 missing31192_31200 records31192_31200 :=
  aligned31192_31196.append aligned31196_31200

def missing31184_31200 : List (BitVec (edgeCount 12)) :=
  missing31184_31192 ++ missing31192_31200
abbrev records31184_31200 : List Blob :=
  records31184_31192 ++ records31192_31200
theorem aligned31184_31200 :
    AlignedValid 12 4 missing31184_31200 records31184_31200 :=
  aligned31184_31192.append aligned31192_31200

def missing31168_31200 : List (BitVec (edgeCount 12)) :=
  missing31168_31184 ++ missing31184_31200
abbrev records31168_31200 : List Blob :=
  records31168_31184 ++ records31184_31200
theorem aligned31168_31200 :
    AlignedValid 12 4 missing31168_31200 records31168_31200 :=
  aligned31168_31184.append aligned31184_31200

def missing31200_31201 : List (BitVec (edgeCount 12)) :=
  [missing31200]
abbrev records31200_31201 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31200]
theorem aligned31200_31201 :
    AlignedValid 12 4 missing31200_31201 records31200_31201 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31200
    maskCheck31200 AlignedValid.nil

def missing31201_31202 : List (BitVec (edgeCount 12)) :=
  [missing31201]
abbrev records31201_31202 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31201]
theorem aligned31201_31202 :
    AlignedValid 12 4 missing31201_31202 records31201_31202 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31201
    maskCheck31201 AlignedValid.nil

def missing31200_31202 : List (BitVec (edgeCount 12)) :=
  missing31200_31201 ++ missing31201_31202
abbrev records31200_31202 : List Blob :=
  records31200_31201 ++ records31201_31202
theorem aligned31200_31202 :
    AlignedValid 12 4 missing31200_31202 records31200_31202 :=
  aligned31200_31201.append aligned31201_31202

def missing31202_31203 : List (BitVec (edgeCount 12)) :=
  [missing31202]
abbrev records31202_31203 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31202]
theorem aligned31202_31203 :
    AlignedValid 12 4 missing31202_31203 records31202_31203 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31202
    maskCheck31202 AlignedValid.nil

def missing31203_31204 : List (BitVec (edgeCount 12)) :=
  [missing31203]
abbrev records31203_31204 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31203]
theorem aligned31203_31204 :
    AlignedValid 12 4 missing31203_31204 records31203_31204 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31203
    maskCheck31203 AlignedValid.nil

def missing31202_31204 : List (BitVec (edgeCount 12)) :=
  missing31202_31203 ++ missing31203_31204
abbrev records31202_31204 : List Blob :=
  records31202_31203 ++ records31203_31204
theorem aligned31202_31204 :
    AlignedValid 12 4 missing31202_31204 records31202_31204 :=
  aligned31202_31203.append aligned31203_31204

def missing31200_31204 : List (BitVec (edgeCount 12)) :=
  missing31200_31202 ++ missing31202_31204
abbrev records31200_31204 : List Blob :=
  records31200_31202 ++ records31202_31204
theorem aligned31200_31204 :
    AlignedValid 12 4 missing31200_31204 records31200_31204 :=
  aligned31200_31202.append aligned31202_31204

def missing31204_31205 : List (BitVec (edgeCount 12)) :=
  [missing31204]
abbrev records31204_31205 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31204]
theorem aligned31204_31205 :
    AlignedValid 12 4 missing31204_31205 records31204_31205 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31204
    maskCheck31204 AlignedValid.nil

def missing31205_31206 : List (BitVec (edgeCount 12)) :=
  [missing31205]
abbrev records31205_31206 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31205]
theorem aligned31205_31206 :
    AlignedValid 12 4 missing31205_31206 records31205_31206 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31205
    maskCheck31205 AlignedValid.nil

def missing31204_31206 : List (BitVec (edgeCount 12)) :=
  missing31204_31205 ++ missing31205_31206
abbrev records31204_31206 : List Blob :=
  records31204_31205 ++ records31205_31206
theorem aligned31204_31206 :
    AlignedValid 12 4 missing31204_31206 records31204_31206 :=
  aligned31204_31205.append aligned31205_31206

def missing31206_31207 : List (BitVec (edgeCount 12)) :=
  [missing31206]
abbrev records31206_31207 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31206]
theorem aligned31206_31207 :
    AlignedValid 12 4 missing31206_31207 records31206_31207 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31206
    maskCheck31206 AlignedValid.nil

def missing31207_31208 : List (BitVec (edgeCount 12)) :=
  [missing31207]
abbrev records31207_31208 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31207]
theorem aligned31207_31208 :
    AlignedValid 12 4 missing31207_31208 records31207_31208 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31207
    maskCheck31207 AlignedValid.nil

def missing31206_31208 : List (BitVec (edgeCount 12)) :=
  missing31206_31207 ++ missing31207_31208
abbrev records31206_31208 : List Blob :=
  records31206_31207 ++ records31207_31208
theorem aligned31206_31208 :
    AlignedValid 12 4 missing31206_31208 records31206_31208 :=
  aligned31206_31207.append aligned31207_31208

def missing31204_31208 : List (BitVec (edgeCount 12)) :=
  missing31204_31206 ++ missing31206_31208
abbrev records31204_31208 : List Blob :=
  records31204_31206 ++ records31206_31208
theorem aligned31204_31208 :
    AlignedValid 12 4 missing31204_31208 records31204_31208 :=
  aligned31204_31206.append aligned31206_31208

def missing31200_31208 : List (BitVec (edgeCount 12)) :=
  missing31200_31204 ++ missing31204_31208
abbrev records31200_31208 : List Blob :=
  records31200_31204 ++ records31204_31208
theorem aligned31200_31208 :
    AlignedValid 12 4 missing31200_31208 records31200_31208 :=
  aligned31200_31204.append aligned31204_31208

def missing31208_31209 : List (BitVec (edgeCount 12)) :=
  [missing31208]
abbrev records31208_31209 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31208]
theorem aligned31208_31209 :
    AlignedValid 12 4 missing31208_31209 records31208_31209 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31208
    maskCheck31208 AlignedValid.nil

def missing31209_31210 : List (BitVec (edgeCount 12)) :=
  [missing31209]
abbrev records31209_31210 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31209]
theorem aligned31209_31210 :
    AlignedValid 12 4 missing31209_31210 records31209_31210 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31209
    maskCheck31209 AlignedValid.nil

def missing31208_31210 : List (BitVec (edgeCount 12)) :=
  missing31208_31209 ++ missing31209_31210
abbrev records31208_31210 : List Blob :=
  records31208_31209 ++ records31209_31210
theorem aligned31208_31210 :
    AlignedValid 12 4 missing31208_31210 records31208_31210 :=
  aligned31208_31209.append aligned31209_31210

def missing31210_31211 : List (BitVec (edgeCount 12)) :=
  [missing31210]
abbrev records31210_31211 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31210]
theorem aligned31210_31211 :
    AlignedValid 12 4 missing31210_31211 records31210_31211 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31210
    maskCheck31210 AlignedValid.nil

def missing31211_31212 : List (BitVec (edgeCount 12)) :=
  [missing31211]
abbrev records31211_31212 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31211]
theorem aligned31211_31212 :
    AlignedValid 12 4 missing31211_31212 records31211_31212 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31211
    maskCheck31211 AlignedValid.nil

def missing31210_31212 : List (BitVec (edgeCount 12)) :=
  missing31210_31211 ++ missing31211_31212
abbrev records31210_31212 : List Blob :=
  records31210_31211 ++ records31211_31212
theorem aligned31210_31212 :
    AlignedValid 12 4 missing31210_31212 records31210_31212 :=
  aligned31210_31211.append aligned31211_31212

def missing31208_31212 : List (BitVec (edgeCount 12)) :=
  missing31208_31210 ++ missing31210_31212
abbrev records31208_31212 : List Blob :=
  records31208_31210 ++ records31210_31212
theorem aligned31208_31212 :
    AlignedValid 12 4 missing31208_31212 records31208_31212 :=
  aligned31208_31210.append aligned31210_31212

def missing31212_31213 : List (BitVec (edgeCount 12)) :=
  [missing31212]
abbrev records31212_31213 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31212]
theorem aligned31212_31213 :
    AlignedValid 12 4 missing31212_31213 records31212_31213 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31212
    maskCheck31212 AlignedValid.nil

def missing31213_31214 : List (BitVec (edgeCount 12)) :=
  [missing31213]
abbrev records31213_31214 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31213]
theorem aligned31213_31214 :
    AlignedValid 12 4 missing31213_31214 records31213_31214 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31213
    maskCheck31213 AlignedValid.nil

def missing31212_31214 : List (BitVec (edgeCount 12)) :=
  missing31212_31213 ++ missing31213_31214
abbrev records31212_31214 : List Blob :=
  records31212_31213 ++ records31213_31214
theorem aligned31212_31214 :
    AlignedValid 12 4 missing31212_31214 records31212_31214 :=
  aligned31212_31213.append aligned31213_31214

def missing31214_31215 : List (BitVec (edgeCount 12)) :=
  [missing31214]
abbrev records31214_31215 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31214]
theorem aligned31214_31215 :
    AlignedValid 12 4 missing31214_31215 records31214_31215 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31214
    maskCheck31214 AlignedValid.nil

def missing31215_31216 : List (BitVec (edgeCount 12)) :=
  [missing31215]
abbrev records31215_31216 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31215]
theorem aligned31215_31216 :
    AlignedValid 12 4 missing31215_31216 records31215_31216 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31215
    maskCheck31215 AlignedValid.nil

def missing31214_31216 : List (BitVec (edgeCount 12)) :=
  missing31214_31215 ++ missing31215_31216
abbrev records31214_31216 : List Blob :=
  records31214_31215 ++ records31215_31216
theorem aligned31214_31216 :
    AlignedValid 12 4 missing31214_31216 records31214_31216 :=
  aligned31214_31215.append aligned31215_31216

def missing31212_31216 : List (BitVec (edgeCount 12)) :=
  missing31212_31214 ++ missing31214_31216
abbrev records31212_31216 : List Blob :=
  records31212_31214 ++ records31214_31216
theorem aligned31212_31216 :
    AlignedValid 12 4 missing31212_31216 records31212_31216 :=
  aligned31212_31214.append aligned31214_31216

def missing31208_31216 : List (BitVec (edgeCount 12)) :=
  missing31208_31212 ++ missing31212_31216
abbrev records31208_31216 : List Blob :=
  records31208_31212 ++ records31212_31216
theorem aligned31208_31216 :
    AlignedValid 12 4 missing31208_31216 records31208_31216 :=
  aligned31208_31212.append aligned31212_31216

def missing31200_31216 : List (BitVec (edgeCount 12)) :=
  missing31200_31208 ++ missing31208_31216
abbrev records31200_31216 : List Blob :=
  records31200_31208 ++ records31208_31216
theorem aligned31200_31216 :
    AlignedValid 12 4 missing31200_31216 records31200_31216 :=
  aligned31200_31208.append aligned31208_31216

def missing31216_31217 : List (BitVec (edgeCount 12)) :=
  [missing31216]
abbrev records31216_31217 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31216]
theorem aligned31216_31217 :
    AlignedValid 12 4 missing31216_31217 records31216_31217 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31216
    maskCheck31216 AlignedValid.nil

def missing31217_31218 : List (BitVec (edgeCount 12)) :=
  [missing31217]
abbrev records31217_31218 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31217]
theorem aligned31217_31218 :
    AlignedValid 12 4 missing31217_31218 records31217_31218 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31217
    maskCheck31217 AlignedValid.nil

def missing31216_31218 : List (BitVec (edgeCount 12)) :=
  missing31216_31217 ++ missing31217_31218
abbrev records31216_31218 : List Blob :=
  records31216_31217 ++ records31217_31218
theorem aligned31216_31218 :
    AlignedValid 12 4 missing31216_31218 records31216_31218 :=
  aligned31216_31217.append aligned31217_31218

def missing31218_31219 : List (BitVec (edgeCount 12)) :=
  [missing31218]
abbrev records31218_31219 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31218]
theorem aligned31218_31219 :
    AlignedValid 12 4 missing31218_31219 records31218_31219 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31218
    maskCheck31218 AlignedValid.nil

def missing31219_31220 : List (BitVec (edgeCount 12)) :=
  [missing31219]
abbrev records31219_31220 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31219]
theorem aligned31219_31220 :
    AlignedValid 12 4 missing31219_31220 records31219_31220 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31219
    maskCheck31219 AlignedValid.nil

def missing31218_31220 : List (BitVec (edgeCount 12)) :=
  missing31218_31219 ++ missing31219_31220
abbrev records31218_31220 : List Blob :=
  records31218_31219 ++ records31219_31220
theorem aligned31218_31220 :
    AlignedValid 12 4 missing31218_31220 records31218_31220 :=
  aligned31218_31219.append aligned31219_31220

def missing31216_31220 : List (BitVec (edgeCount 12)) :=
  missing31216_31218 ++ missing31218_31220
abbrev records31216_31220 : List Blob :=
  records31216_31218 ++ records31218_31220
theorem aligned31216_31220 :
    AlignedValid 12 4 missing31216_31220 records31216_31220 :=
  aligned31216_31218.append aligned31218_31220

def missing31220_31221 : List (BitVec (edgeCount 12)) :=
  [missing31220]
abbrev records31220_31221 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31220]
theorem aligned31220_31221 :
    AlignedValid 12 4 missing31220_31221 records31220_31221 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31220
    maskCheck31220 AlignedValid.nil

def missing31221_31222 : List (BitVec (edgeCount 12)) :=
  [missing31221]
abbrev records31221_31222 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31221]
theorem aligned31221_31222 :
    AlignedValid 12 4 missing31221_31222 records31221_31222 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31221
    maskCheck31221 AlignedValid.nil

def missing31220_31222 : List (BitVec (edgeCount 12)) :=
  missing31220_31221 ++ missing31221_31222
abbrev records31220_31222 : List Blob :=
  records31220_31221 ++ records31221_31222
theorem aligned31220_31222 :
    AlignedValid 12 4 missing31220_31222 records31220_31222 :=
  aligned31220_31221.append aligned31221_31222

def missing31222_31223 : List (BitVec (edgeCount 12)) :=
  [missing31222]
abbrev records31222_31223 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31222]
theorem aligned31222_31223 :
    AlignedValid 12 4 missing31222_31223 records31222_31223 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31222
    maskCheck31222 AlignedValid.nil

def missing31223_31224 : List (BitVec (edgeCount 12)) :=
  [missing31223]
abbrev records31223_31224 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31223]
theorem aligned31223_31224 :
    AlignedValid 12 4 missing31223_31224 records31223_31224 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31223
    maskCheck31223 AlignedValid.nil

def missing31222_31224 : List (BitVec (edgeCount 12)) :=
  missing31222_31223 ++ missing31223_31224
abbrev records31222_31224 : List Blob :=
  records31222_31223 ++ records31223_31224
theorem aligned31222_31224 :
    AlignedValid 12 4 missing31222_31224 records31222_31224 :=
  aligned31222_31223.append aligned31223_31224

def missing31220_31224 : List (BitVec (edgeCount 12)) :=
  missing31220_31222 ++ missing31222_31224
abbrev records31220_31224 : List Blob :=
  records31220_31222 ++ records31222_31224
theorem aligned31220_31224 :
    AlignedValid 12 4 missing31220_31224 records31220_31224 :=
  aligned31220_31222.append aligned31222_31224

def missing31216_31224 : List (BitVec (edgeCount 12)) :=
  missing31216_31220 ++ missing31220_31224
abbrev records31216_31224 : List Blob :=
  records31216_31220 ++ records31220_31224
theorem aligned31216_31224 :
    AlignedValid 12 4 missing31216_31224 records31216_31224 :=
  aligned31216_31220.append aligned31220_31224

def missing31224_31225 : List (BitVec (edgeCount 12)) :=
  [missing31224]
abbrev records31224_31225 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31224]
theorem aligned31224_31225 :
    AlignedValid 12 4 missing31224_31225 records31224_31225 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31224
    maskCheck31224 AlignedValid.nil

def missing31225_31226 : List (BitVec (edgeCount 12)) :=
  [missing31225]
abbrev records31225_31226 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31225]
theorem aligned31225_31226 :
    AlignedValid 12 4 missing31225_31226 records31225_31226 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31225
    maskCheck31225 AlignedValid.nil

def missing31224_31226 : List (BitVec (edgeCount 12)) :=
  missing31224_31225 ++ missing31225_31226
abbrev records31224_31226 : List Blob :=
  records31224_31225 ++ records31225_31226
theorem aligned31224_31226 :
    AlignedValid 12 4 missing31224_31226 records31224_31226 :=
  aligned31224_31225.append aligned31225_31226

def missing31226_31227 : List (BitVec (edgeCount 12)) :=
  [missing31226]
abbrev records31226_31227 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31226]
theorem aligned31226_31227 :
    AlignedValid 12 4 missing31226_31227 records31226_31227 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31226
    maskCheck31226 AlignedValid.nil

def missing31227_31228 : List (BitVec (edgeCount 12)) :=
  [missing31227]
abbrev records31227_31228 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31227]
theorem aligned31227_31228 :
    AlignedValid 12 4 missing31227_31228 records31227_31228 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31227
    maskCheck31227 AlignedValid.nil

def missing31226_31228 : List (BitVec (edgeCount 12)) :=
  missing31226_31227 ++ missing31227_31228
abbrev records31226_31228 : List Blob :=
  records31226_31227 ++ records31227_31228
theorem aligned31226_31228 :
    AlignedValid 12 4 missing31226_31228 records31226_31228 :=
  aligned31226_31227.append aligned31227_31228

def missing31224_31228 : List (BitVec (edgeCount 12)) :=
  missing31224_31226 ++ missing31226_31228
abbrev records31224_31228 : List Blob :=
  records31224_31226 ++ records31226_31228
theorem aligned31224_31228 :
    AlignedValid 12 4 missing31224_31228 records31224_31228 :=
  aligned31224_31226.append aligned31226_31228

def missing31228_31229 : List (BitVec (edgeCount 12)) :=
  [missing31228]
abbrev records31228_31229 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31228]
theorem aligned31228_31229 :
    AlignedValid 12 4 missing31228_31229 records31228_31229 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31228
    maskCheck31228 AlignedValid.nil

def missing31229_31230 : List (BitVec (edgeCount 12)) :=
  [missing31229]
abbrev records31229_31230 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31229]
theorem aligned31229_31230 :
    AlignedValid 12 4 missing31229_31230 records31229_31230 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31229
    maskCheck31229 AlignedValid.nil

def missing31228_31230 : List (BitVec (edgeCount 12)) :=
  missing31228_31229 ++ missing31229_31230
abbrev records31228_31230 : List Blob :=
  records31228_31229 ++ records31229_31230
theorem aligned31228_31230 :
    AlignedValid 12 4 missing31228_31230 records31228_31230 :=
  aligned31228_31229.append aligned31229_31230

def missing31230_31231 : List (BitVec (edgeCount 12)) :=
  [missing31230]
abbrev records31230_31231 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31230]
theorem aligned31230_31231 :
    AlignedValid 12 4 missing31230_31231 records31230_31231 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31230
    maskCheck31230 AlignedValid.nil

def missing31231_31232 : List (BitVec (edgeCount 12)) :=
  [missing31231]
abbrev records31231_31232 : List Blob :=
  [StrongPackedBucketN12A4Shard243.record31231]
theorem aligned31231_31232 :
    AlignedValid 12 4 missing31231_31232 records31231_31232 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard243.check31231
    maskCheck31231 AlignedValid.nil

def missing31230_31232 : List (BitVec (edgeCount 12)) :=
  missing31230_31231 ++ missing31231_31232
abbrev records31230_31232 : List Blob :=
  records31230_31231 ++ records31231_31232
theorem aligned31230_31232 :
    AlignedValid 12 4 missing31230_31232 records31230_31232 :=
  aligned31230_31231.append aligned31231_31232

def missing31228_31232 : List (BitVec (edgeCount 12)) :=
  missing31228_31230 ++ missing31230_31232
abbrev records31228_31232 : List Blob :=
  records31228_31230 ++ records31230_31232
theorem aligned31228_31232 :
    AlignedValid 12 4 missing31228_31232 records31228_31232 :=
  aligned31228_31230.append aligned31230_31232

def missing31224_31232 : List (BitVec (edgeCount 12)) :=
  missing31224_31228 ++ missing31228_31232
abbrev records31224_31232 : List Blob :=
  records31224_31228 ++ records31228_31232
theorem aligned31224_31232 :
    AlignedValid 12 4 missing31224_31232 records31224_31232 :=
  aligned31224_31228.append aligned31228_31232

def missing31216_31232 : List (BitVec (edgeCount 12)) :=
  missing31216_31224 ++ missing31224_31232
abbrev records31216_31232 : List Blob :=
  records31216_31224 ++ records31224_31232
theorem aligned31216_31232 :
    AlignedValid 12 4 missing31216_31232 records31216_31232 :=
  aligned31216_31224.append aligned31224_31232

def missing31200_31232 : List (BitVec (edgeCount 12)) :=
  missing31200_31216 ++ missing31216_31232
abbrev records31200_31232 : List Blob :=
  records31200_31216 ++ records31216_31232
theorem aligned31200_31232 :
    AlignedValid 12 4 missing31200_31232 records31200_31232 :=
  aligned31200_31216.append aligned31216_31232

def missing31168_31232 : List (BitVec (edgeCount 12)) :=
  missing31168_31200 ++ missing31200_31232
abbrev records31168_31232 : List Blob :=
  records31168_31200 ++ records31200_31232
theorem aligned31168_31232 :
    AlignedValid 12 4 missing31168_31232 records31168_31232 :=
  aligned31168_31200.append aligned31200_31232

def missing31104_31232 : List (BitVec (edgeCount 12)) :=
  missing31104_31168 ++ missing31168_31232
abbrev records31104_31232 : List Blob :=
  records31104_31168 ++ records31168_31232
theorem aligned31104_31232 :
    AlignedValid 12 4 missing31104_31232 records31104_31232 :=
  aligned31104_31168.append aligned31168_31232

abbrev missing : List (BitVec (edgeCount 12)) := missing31104_31232
abbrev records : List Blob := records31104_31232
theorem aligned : AlignedValid 12 4 missing records := aligned31104_31232

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard243
