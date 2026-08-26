/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard235

/-! Decode-only alignment checks for n=12, a=4, records 30080--30207. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard235

open PackedBucketCertificate

def missing30080 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27743090148892475392
theorem maskCheck30080 :
    checkMaskFor missing30080 StrongPackedBucketN12A4Shard235.record30080 = true := by
  decide

def missing30081 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27815147742930403328
theorem maskCheck30081 :
    checkMaskFor missing30081 StrongPackedBucketN12A4Shard235.record30081 = true := by
  decide

def missing30082 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27959262931006259200
theorem maskCheck30082 :
    checkMaskFor missing30082 StrongPackedBucketN12A4Shard235.record30082 = true := by
  decide

def missing30083 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28823954059461394432
theorem maskCheck30083 :
    checkMaskFor missing30083 StrongPackedBucketN12A4Shard235.record30083 = true := by
  decide

def missing30084 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32282718573281935360
theorem maskCheck30084 :
    checkMaskFor missing30084 StrongPackedBucketN12A4Shard235.record30084 = true := by
  decide

def missing30085 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 253540235888033792
theorem maskCheck30085 :
    checkMaskFor missing30085 StrongPackedBucketN12A4Shard235.record30085 = true := by
  decide

def missing30086 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 397655423963889664
theorem maskCheck30086 :
    checkMaskFor missing30086 StrongPackedBucketN12A4Shard235.record30086 = true := by
  decide

def missing30087 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 505741815020781568
theorem maskCheck30087 :
    checkMaskFor missing30087 StrongPackedBucketN12A4Shard235.record30087 = true := by
  decide

def missing30088 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1262346552419024896
theorem maskCheck30088 :
    checkMaskFor missing30088 StrongPackedBucketN12A4Shard235.record30088 = true := by
  decide

def missing30089 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4793168660277493760
theorem maskCheck30089 :
    checkMaskFor missing30089 StrongPackedBucketN12A4Shard235.record30089 = true := by
  decide

def missing30090 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4829197457296457728
theorem maskCheck30090 :
    checkMaskFor missing30090 StrongPackedBucketN12A4Shard235.record30090 = true := by
  decide

def missing30091 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5477715803637809152
theorem maskCheck30091 :
    checkMaskFor missing30091 StrongPackedBucketN12A4Shard235.record30091 = true := by
  decide

def missing30092 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6054176555941232640
theorem maskCheck30092 :
    checkMaskFor missing30092 StrongPackedBucketN12A4Shard235.record30092 = true := by
  decide

def missing30093 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13872425509056413696
theorem maskCheck30093 :
    checkMaskFor missing30093 StrongPackedBucketN12A4Shard235.record30093 = true := by
  decide

def missing30094 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14124627088189161472
theorem maskCheck30094 :
    checkMaskFor missing30094 StrongPackedBucketN12A4Shard235.record30094 = true := by
  decide

def missing30095 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14989318216644296704
theorem maskCheck30095 :
    checkMaskFor missing30095 StrongPackedBucketN12A4Shard235.record30095 = true := by
  decide

def missing30096 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16142239721251143680
theorem maskCheck30096 :
    checkMaskFor missing30096 StrongPackedBucketN12A4Shard235.record30096 = true := by
  decide

def missing30097 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18556169121521729536
theorem maskCheck30097 :
    checkMaskFor missing30097 StrongPackedBucketN12A4Shard235.record30097 = true := by
  decide

def missing30098 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18664255512578621440
theorem maskCheck30098 :
    checkMaskFor missing30098 StrongPackedBucketN12A4Shard235.record30098 = true := by
  decide

def missing30099 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18772341903635513344
theorem maskCheck30099 :
    checkMaskFor missing30099 StrongPackedBucketN12A4Shard235.record30099 = true := by
  decide

def missing30100 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19312773858919972864
theorem maskCheck30100 :
    checkMaskFor missing30100 StrongPackedBucketN12A4Shard235.record30100 = true := by
  decide

def missing30101 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19637033032090648576
theorem maskCheck30101 :
    checkMaskFor missing30101 StrongPackedBucketN12A4Shard235.record30101 = true := by
  decide

def missing30102 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20789954536697495552
theorem maskCheck30102 :
    checkMaskFor missing30102 StrongPackedBucketN12A4Shard235.record30102 = true := by
  decide

def missing30103 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21042156115830243328
theorem maskCheck30103 :
    checkMaskFor missing30103 StrongPackedBucketN12A4Shard235.record30103 = true := by
  decide

def missing30104 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23095797545911189504
theorem maskCheck30104 :
    checkMaskFor missing30104 StrongPackedBucketN12A4Shard235.record30104 = true := by
  decide

def missing30105 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23203883936968081408
theorem maskCheck30105 :
    checkMaskFor missing30105 StrongPackedBucketN12A4Shard235.record30105 = true := by
  decide

def missing30106 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23347999125043937280
theorem maskCheck30106 :
    checkMaskFor missing30106 StrongPackedBucketN12A4Shard235.record30106 = true := by
  decide

def missing30107 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24212690253499072512
theorem maskCheck30107 :
    checkMaskFor missing30107 StrongPackedBucketN12A4Shard235.record30107 = true := by
  decide

def missing30108 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25365611758105919488
theorem maskCheck30108 :
    checkMaskFor missing30108 StrongPackedBucketN12A4Shard235.record30108 = true := by
  decide

def missing30109 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32283140785747001344
theorem maskCheck30109 :
    checkMaskFor missing30109 StrongPackedBucketN12A4Shard235.record30109 = true := by
  decide

def missing30110 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 253680973376389120
theorem maskCheck30110 :
    checkMaskFor missing30110 StrongPackedBucketN12A4Shard235.record30110 = true := by
  decide

def missing30111 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 397796161452244992
theorem maskCheck30111 :
    checkMaskFor missing30111 StrongPackedBucketN12A4Shard235.record30111 = true := by
  decide

def missing30112 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 469853755490172928
theorem maskCheck30112 :
    checkMaskFor missing30112 StrongPackedBucketN12A4Shard235.record30112 = true := by
  decide

def missing30113 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 686026537603956736
theorem maskCheck30113 :
    checkMaskFor missing30113 StrongPackedBucketN12A4Shard235.record30113 = true := by
  decide

def missing30114 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 902199319717740544
theorem maskCheck30114 :
    checkMaskFor missing30114 StrongPackedBucketN12A4Shard235.record30114 = true := by
  decide

def missing30115 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 938228116736704512
theorem maskCheck30115 :
    checkMaskFor missing30115 StrongPackedBucketN12A4Shard235.record30115 = true := by
  decide

def missing30116 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1262487289907380224
theorem maskCheck30116 :
    checkMaskFor missing30116 StrongPackedBucketN12A4Shard235.record30116 = true := by
  decide

def missing30117 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1874976839229767680
theorem maskCheck30117 :
    checkMaskFor missing30117 StrongPackedBucketN12A4Shard235.record30117 = true := by
  decide

def missing30118 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2415408794514227200
theorem maskCheck30118 :
    checkMaskFor missing30118 StrongPackedBucketN12A4Shard235.record30118 = true := by
  decide

def missing30119 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3027898343836614656
theorem maskCheck30119 :
    checkMaskFor missing30119 StrongPackedBucketN12A4Shard235.record30119 = true := by
  decide

def missing30120 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4793309397765849088
theorem maskCheck30120 :
    checkMaskFor missing30120 StrongPackedBucketN12A4Shard235.record30120 = true := by
  decide

def missing30121 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4937424585841704960
theorem maskCheck30121 :
    checkMaskFor missing30121 StrongPackedBucketN12A4Shard235.record30121 = true := by
  decide

def missing30122 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4973453382860668928
theorem maskCheck30122 :
    checkMaskFor missing30122 StrongPackedBucketN12A4Shard235.record30122 = true := by
  decide

def missing30123 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5333741353050308608
theorem maskCheck30123 :
    checkMaskFor missing30123 StrongPackedBucketN12A4Shard235.record30123 = true := by
  decide

def missing30124 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5477856541126164480
theorem maskCheck30124 :
    checkMaskFor missing30124 StrongPackedBucketN12A4Shard235.record30124 = true := by
  decide

def missing30125 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5910202105353732096
theorem maskCheck30125 :
    checkMaskFor missing30125 StrongPackedBucketN12A4Shard235.record30125 = true := by
  decide

def missing30126 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9332937822155309056
theorem maskCheck30126 :
    checkMaskFor missing30126 StrongPackedBucketN12A4Shard235.record30126 = true := by
  decide

def missing30127 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9549110604269092864
theorem maskCheck30127 :
    checkMaskFor missing30127 StrongPackedBucketN12A4Shard235.record30127 = true := by
  decide

def missing30128 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9585139401288056832
theorem maskCheck30128 :
    checkMaskFor missing30128 StrongPackedBucketN12A4Shard235.record30128 = true := by
  decide

def missing30129 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9945427371477696512
theorem maskCheck30129 :
    checkMaskFor missing30129 StrongPackedBucketN12A4Shard235.record30129 = true := by
  decide

def missing30130 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10089542559553552384
theorem maskCheck30130 :
    checkMaskFor missing30130 StrongPackedBucketN12A4Shard235.record30130 = true := by
  decide

def missing30131 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12107155192615534592
theorem maskCheck30131 :
    checkMaskFor missing30131 StrongPackedBucketN12A4Shard235.record30131 = true := by
  decide

def missing30132 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13872566246544769024
theorem maskCheck30132 :
    checkMaskFor missing30132 StrongPackedBucketN12A4Shard235.record30132 = true := by
  decide

def missing30133 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13980652637601660928
theorem maskCheck30133 :
    checkMaskFor missing30133 StrongPackedBucketN12A4Shard235.record30133 = true := by
  decide

def missing30134 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14124767825677516800
theorem maskCheck30134 :
    checkMaskFor missing30134 StrongPackedBucketN12A4Shard235.record30134 = true := by
  decide

def missing30135 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14412998201829228544
theorem maskCheck30135 :
    checkMaskFor missing30135 StrongPackedBucketN12A4Shard235.record30135 = true := by
  decide

def missing30136 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14989458954132652032
theorem maskCheck30136 :
    checkMaskFor missing30136 StrongPackedBucketN12A4Shard235.record30136 = true := by
  decide

def missing30137 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16142380458739499008
theorem maskCheck30137 :
    checkMaskFor missing30137 StrongPackedBucketN12A4Shard235.record30137 = true := by
  decide

def missing30138 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18556309859010084864
theorem maskCheck30138 :
    checkMaskFor missing30138 StrongPackedBucketN12A4Shard235.record30138 = true := by
  decide

def missing30139 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18628367453048012800
theorem maskCheck30139 :
    checkMaskFor missing30139 StrongPackedBucketN12A4Shard235.record30139 = true := by
  decide

def missing30140 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18664396250066976768
theorem maskCheck30140 :
    checkMaskFor missing30140 StrongPackedBucketN12A4Shard235.record30140 = true := by
  decide

def missing30141 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18772482641123868672
theorem maskCheck30141 :
    checkMaskFor missing30141 StrongPackedBucketN12A4Shard235.record30141 = true := by
  decide

def missing30142 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19060713017275580416
theorem maskCheck30142 :
    checkMaskFor missing30142 StrongPackedBucketN12A4Shard235.record30142 = true := by
  decide

def missing30143 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19168799408332472320
theorem maskCheck30143 :
    checkMaskFor missing30143 StrongPackedBucketN12A4Shard235.record30143 = true := by
  decide

def missing30144 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19637173769579003904
theorem maskCheck30144 :
    checkMaskFor missing30144 StrongPackedBucketN12A4Shard235.record30144 = true := by
  decide

def missing30145 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19745260160635895808
theorem maskCheck30145 :
    checkMaskFor missing30145 StrongPackedBucketN12A4Shard235.record30145 = true := by
  decide

def missing30146 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20177605724863463424
theorem maskCheck30146 :
    checkMaskFor missing30146 StrongPackedBucketN12A4Shard235.record30146 = true := by
  decide

def missing30147 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20790095274185850880
theorem maskCheck30147 :
    checkMaskFor missing30147 StrongPackedBucketN12A4Shard235.record30147 = true := by
  decide

def missing30148 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20898181665242742784
theorem maskCheck30148 :
    checkMaskFor missing30148 StrongPackedBucketN12A4Shard235.record30148 = true := by
  decide

def missing30149 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21330527229470310400
theorem maskCheck30149 :
    checkMaskFor missing30149 StrongPackedBucketN12A4Shard235.record30149 = true := by
  decide

def missing30150 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21906987981773733888
theorem maskCheck30150 :
    checkMaskFor missing30150 StrongPackedBucketN12A4Shard235.record30150 = true := by
  decide

def missing30151 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23095938283399544832
theorem maskCheck30151 :
    checkMaskFor missing30151 StrongPackedBucketN12A4Shard235.record30151 = true := by
  decide

def missing30152 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23131967080418508800
theorem maskCheck30152 :
    checkMaskFor missing30152 StrongPackedBucketN12A4Shard235.record30152 = true := by
  decide

def missing30153 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23204024674456436736
theorem maskCheck30153 :
    checkMaskFor missing30153 StrongPackedBucketN12A4Shard235.record30153 = true := by
  decide

def missing30154 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23348139862532292608
theorem maskCheck30154 :
    checkMaskFor missing30154 StrongPackedBucketN12A4Shard235.record30154 = true := by
  decide

def missing30155 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23636370238684004352
theorem maskCheck30155 :
    checkMaskFor missing30155 StrongPackedBucketN12A4Shard235.record30155 = true := by
  decide

def missing30156 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24212830990987427840
theorem maskCheck30156 :
    checkMaskFor missing30156 StrongPackedBucketN12A4Shard235.record30156 = true := by
  decide

def missing30157 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25365752495594274816
theorem maskCheck30157 :
    checkMaskFor missing30157 StrongPackedBucketN12A4Shard235.record30157 = true := by
  decide

def missing30158 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27707624301826932736
theorem maskCheck30158 :
    checkMaskFor missing30158 StrongPackedBucketN12A4Shard235.record30158 = true := by
  decide

def missing30159 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27743653098845896704
theorem maskCheck30159 :
    checkMaskFor missing30159 StrongPackedBucketN12A4Shard235.record30159 = true := by
  decide

def missing30160 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27815710692883824640
theorem maskCheck30160 :
    checkMaskFor missing30160 StrongPackedBucketN12A4Shard235.record30160 = true := by
  decide

def missing30161 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27959825880959680512
theorem maskCheck30161 :
    checkMaskFor missing30161 StrongPackedBucketN12A4Shard235.record30161 = true := by
  decide

def missing30162 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28248056257111392256
theorem maskCheck30162 :
    checkMaskFor missing30162 StrongPackedBucketN12A4Shard235.record30162 = true := by
  decide

def missing30163 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28824517009414815744
theorem maskCheck30163 :
    checkMaskFor missing30163 StrongPackedBucketN12A4Shard235.record30163 = true := by
  decide

def missing30164 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29977438514021662720
theorem maskCheck30164 :
    checkMaskFor missing30164 StrongPackedBucketN12A4Shard235.record30164 = true := by
  decide

def missing30165 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32283281523235356672
theorem maskCheck30165 :
    checkMaskFor missing30165 StrongPackedBucketN12A4Shard235.record30165 = true := by
  decide

def missing30166 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 254173554585632768
theorem maskCheck30166 :
    checkMaskFor missing30166 StrongPackedBucketN12A4Shard235.record30166 = true := by
  decide

def missing30167 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 398288742661488640
theorem maskCheck30167 :
    checkMaskFor missing30167 StrongPackedBucketN12A4Shard235.record30167 = true := by
  decide

def missing30168 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 902691900926984192
theorem maskCheck30168 :
    checkMaskFor missing30168 StrongPackedBucketN12A4Shard235.record30168 = true := by
  decide

def missing30169 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 938720697945948160
theorem maskCheck30169 :
    checkMaskFor missing30169 StrongPackedBucketN12A4Shard235.record30169 = true := by
  decide

def missing30170 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1371066262173515776
theorem maskCheck30170 :
    checkMaskFor missing30170 StrongPackedBucketN12A4Shard235.record30170 = true := by
  decide

def missing30171 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2019584608514867200
theorem maskCheck30171 :
    checkMaskFor missing30171 StrongPackedBucketN12A4Shard235.record30171 = true := by
  decide

def missing30172 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2523987766780362752
theorem maskCheck30172 :
    checkMaskFor missing30172 StrongPackedBucketN12A4Shard235.record30172 = true := by
  decide

def missing30173 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3172506113121714176
theorem maskCheck30173 :
    checkMaskFor missing30173 StrongPackedBucketN12A4Shard235.record30173 = true := by
  decide

def missing30174 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4793801978975092736
theorem maskCheck30174 :
    checkMaskFor missing30174 StrongPackedBucketN12A4Shard235.record30174 = true := by
  decide

def missing30175 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4829830775994056704
theorem maskCheck30175 :
    checkMaskFor missing30175 StrongPackedBucketN12A4Shard235.record30175 = true := by
  decide

def missing30176 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4937917167050948608
theorem maskCheck30176 :
    checkMaskFor missing30176 StrongPackedBucketN12A4Shard235.record30176 = true := by
  decide

def missing30177 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5478349122335408128
theorem maskCheck30177 :
    checkMaskFor missing30177 StrongPackedBucketN12A4Shard235.record30177 = true := by
  decide

def missing30178 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7063616191169822720
theorem maskCheck30178 :
    checkMaskFor missing30178 StrongPackedBucketN12A4Shard235.record30178 = true := by
  decide

def missing30179 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13873058827754012672
theorem maskCheck30179 :
    checkMaskFor missing30179 StrongPackedBucketN12A4Shard235.record30179 = true := by
  decide

def missing30180 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13909087624772976640
theorem maskCheck30180 :
    checkMaskFor missing30180 StrongPackedBucketN12A4Shard235.record30180 = true := by
  decide

def missing30181 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14125260406886760448
theorem maskCheck30181 :
    checkMaskFor missing30181 StrongPackedBucketN12A4Shard235.record30181 = true := by
  decide

def missing30182 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14989951535341895680
theorem maskCheck30182 :
    checkMaskFor missing30182 StrongPackedBucketN12A4Shard235.record30182 = true := by
  decide

def missing30183 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16142873039948742656
theorem maskCheck30183 :
    checkMaskFor missing30183 StrongPackedBucketN12A4Shard235.record30183 = true := by
  decide

def missing30184 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18556802440219328512
theorem maskCheck30184 :
    checkMaskFor missing30184 StrongPackedBucketN12A4Shard235.record30184 = true := by
  decide

def missing30185 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18664888831276220416
theorem maskCheck30185 :
    checkMaskFor missing30185 StrongPackedBucketN12A4Shard235.record30185 = true := by
  decide

def missing30186 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18772975222333112320
theorem maskCheck30186 :
    checkMaskFor missing30186 StrongPackedBucketN12A4Shard235.record30186 = true := by
  decide

def missing30187 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19313407177617571840
theorem maskCheck30187 :
    checkMaskFor missing30187 StrongPackedBucketN12A4Shard235.record30187 = true := by
  decide

def missing30188 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19637666350788247552
theorem maskCheck30188 :
    checkMaskFor missing30188 StrongPackedBucketN12A4Shard235.record30188 = true := by
  decide

def missing30189 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19673695147807211520
theorem maskCheck30189 :
    checkMaskFor missing30189 StrongPackedBucketN12A4Shard235.record30189 = true := by
  decide

def missing30190 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20790587855395094528
theorem maskCheck30190 :
    checkMaskFor missing30190 StrongPackedBucketN12A4Shard235.record30190 = true := by
  decide

def missing30191 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20826616652414058496
theorem maskCheck30191 :
    checkMaskFor missing30191 StrongPackedBucketN12A4Shard235.record30191 = true := by
  decide

def missing30192 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23096430864608788480
theorem maskCheck30192 :
    checkMaskFor missing30192 StrongPackedBucketN12A4Shard235.record30192 = true := by
  decide

def missing30193 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23132459661627752448
theorem maskCheck30193 :
    checkMaskFor missing30193 StrongPackedBucketN12A4Shard235.record30193 = true := by
  decide

def missing30194 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23204517255665680384
theorem maskCheck30194 :
    checkMaskFor missing30194 StrongPackedBucketN12A4Shard235.record30194 = true := by
  decide

def missing30195 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23348632443741536256
theorem maskCheck30195 :
    checkMaskFor missing30195 StrongPackedBucketN12A4Shard235.record30195 = true := by
  decide

def missing30196 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24213323572196671488
theorem maskCheck30196 :
    checkMaskFor missing30196 StrongPackedBucketN12A4Shard235.record30196 = true := by
  decide

def missing30197 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25366245076803518464
theorem maskCheck30197 :
    checkMaskFor missing30197 StrongPackedBucketN12A4Shard235.record30197 = true := by
  decide

def missing30198 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32283774104444600320
theorem maskCheck30198 :
    checkMaskFor missing30198 StrongPackedBucketN12A4Shard235.record30198 = true := by
  decide

def missing30199 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 255651298213363712
theorem maskCheck30199 :
    checkMaskFor missing30199 StrongPackedBucketN12A4Shard235.record30199 = true := by
  decide

def missing30200 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 399766486289219584
theorem maskCheck30200 :
    checkMaskFor missing30200 StrongPackedBucketN12A4Shard235.record30200 = true := by
  decide

def missing30201 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1012256035611607040
theorem maskCheck30201 :
    checkMaskFor missing30201 StrongPackedBucketN12A4Shard235.record30201 = true := by
  decide

def missing30202 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1264457614744354816
theorem maskCheck30202 :
    checkMaskFor missing30202 StrongPackedBucketN12A4Shard235.record30202 = true := by
  decide

def missing30203 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1588716787915030528
theorem maskCheck30203 :
    checkMaskFor missing30203 StrongPackedBucketN12A4Shard235.record30203 = true := by
  decide

def missing30204 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2021062352142598144
theorem maskCheck30204 :
    checkMaskFor missing30204 StrongPackedBucketN12A4Shard235.record30204 = true := by
  decide

def missing30205 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3606329420977012736
theorem maskCheck30205 :
    checkMaskFor missing30205 StrongPackedBucketN12A4Shard235.record30205 = true := by
  decide

def missing30206 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4795279722602823680
theorem maskCheck30206 :
    checkMaskFor missing30206 StrongPackedBucketN12A4Shard235.record30206 = true := by
  decide

def missing30207 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5047481301735571456
theorem maskCheck30207 :
    checkMaskFor missing30207 StrongPackedBucketN12A4Shard235.record30207 = true := by
  decide

def missing30080_30081 : List (BitVec (edgeCount 12)) :=
  [missing30080]
abbrev records30080_30081 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30080]
theorem aligned30080_30081 :
    AlignedValid 12 4 missing30080_30081 records30080_30081 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30080
    maskCheck30080 AlignedValid.nil

def missing30081_30082 : List (BitVec (edgeCount 12)) :=
  [missing30081]
abbrev records30081_30082 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30081]
theorem aligned30081_30082 :
    AlignedValid 12 4 missing30081_30082 records30081_30082 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30081
    maskCheck30081 AlignedValid.nil

def missing30080_30082 : List (BitVec (edgeCount 12)) :=
  missing30080_30081 ++ missing30081_30082
abbrev records30080_30082 : List Blob :=
  records30080_30081 ++ records30081_30082
theorem aligned30080_30082 :
    AlignedValid 12 4 missing30080_30082 records30080_30082 :=
  aligned30080_30081.append aligned30081_30082

def missing30082_30083 : List (BitVec (edgeCount 12)) :=
  [missing30082]
abbrev records30082_30083 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30082]
theorem aligned30082_30083 :
    AlignedValid 12 4 missing30082_30083 records30082_30083 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30082
    maskCheck30082 AlignedValid.nil

def missing30083_30084 : List (BitVec (edgeCount 12)) :=
  [missing30083]
abbrev records30083_30084 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30083]
theorem aligned30083_30084 :
    AlignedValid 12 4 missing30083_30084 records30083_30084 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30083
    maskCheck30083 AlignedValid.nil

def missing30082_30084 : List (BitVec (edgeCount 12)) :=
  missing30082_30083 ++ missing30083_30084
abbrev records30082_30084 : List Blob :=
  records30082_30083 ++ records30083_30084
theorem aligned30082_30084 :
    AlignedValid 12 4 missing30082_30084 records30082_30084 :=
  aligned30082_30083.append aligned30083_30084

def missing30080_30084 : List (BitVec (edgeCount 12)) :=
  missing30080_30082 ++ missing30082_30084
abbrev records30080_30084 : List Blob :=
  records30080_30082 ++ records30082_30084
theorem aligned30080_30084 :
    AlignedValid 12 4 missing30080_30084 records30080_30084 :=
  aligned30080_30082.append aligned30082_30084

def missing30084_30085 : List (BitVec (edgeCount 12)) :=
  [missing30084]
abbrev records30084_30085 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30084]
theorem aligned30084_30085 :
    AlignedValid 12 4 missing30084_30085 records30084_30085 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30084
    maskCheck30084 AlignedValid.nil

def missing30085_30086 : List (BitVec (edgeCount 12)) :=
  [missing30085]
abbrev records30085_30086 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30085]
theorem aligned30085_30086 :
    AlignedValid 12 4 missing30085_30086 records30085_30086 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30085
    maskCheck30085 AlignedValid.nil

def missing30084_30086 : List (BitVec (edgeCount 12)) :=
  missing30084_30085 ++ missing30085_30086
abbrev records30084_30086 : List Blob :=
  records30084_30085 ++ records30085_30086
theorem aligned30084_30086 :
    AlignedValid 12 4 missing30084_30086 records30084_30086 :=
  aligned30084_30085.append aligned30085_30086

def missing30086_30087 : List (BitVec (edgeCount 12)) :=
  [missing30086]
abbrev records30086_30087 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30086]
theorem aligned30086_30087 :
    AlignedValid 12 4 missing30086_30087 records30086_30087 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30086
    maskCheck30086 AlignedValid.nil

def missing30087_30088 : List (BitVec (edgeCount 12)) :=
  [missing30087]
abbrev records30087_30088 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30087]
theorem aligned30087_30088 :
    AlignedValid 12 4 missing30087_30088 records30087_30088 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30087
    maskCheck30087 AlignedValid.nil

def missing30086_30088 : List (BitVec (edgeCount 12)) :=
  missing30086_30087 ++ missing30087_30088
abbrev records30086_30088 : List Blob :=
  records30086_30087 ++ records30087_30088
theorem aligned30086_30088 :
    AlignedValid 12 4 missing30086_30088 records30086_30088 :=
  aligned30086_30087.append aligned30087_30088

def missing30084_30088 : List (BitVec (edgeCount 12)) :=
  missing30084_30086 ++ missing30086_30088
abbrev records30084_30088 : List Blob :=
  records30084_30086 ++ records30086_30088
theorem aligned30084_30088 :
    AlignedValid 12 4 missing30084_30088 records30084_30088 :=
  aligned30084_30086.append aligned30086_30088

def missing30080_30088 : List (BitVec (edgeCount 12)) :=
  missing30080_30084 ++ missing30084_30088
abbrev records30080_30088 : List Blob :=
  records30080_30084 ++ records30084_30088
theorem aligned30080_30088 :
    AlignedValid 12 4 missing30080_30088 records30080_30088 :=
  aligned30080_30084.append aligned30084_30088

def missing30088_30089 : List (BitVec (edgeCount 12)) :=
  [missing30088]
abbrev records30088_30089 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30088]
theorem aligned30088_30089 :
    AlignedValid 12 4 missing30088_30089 records30088_30089 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30088
    maskCheck30088 AlignedValid.nil

def missing30089_30090 : List (BitVec (edgeCount 12)) :=
  [missing30089]
abbrev records30089_30090 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30089]
theorem aligned30089_30090 :
    AlignedValid 12 4 missing30089_30090 records30089_30090 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30089
    maskCheck30089 AlignedValid.nil

def missing30088_30090 : List (BitVec (edgeCount 12)) :=
  missing30088_30089 ++ missing30089_30090
abbrev records30088_30090 : List Blob :=
  records30088_30089 ++ records30089_30090
theorem aligned30088_30090 :
    AlignedValid 12 4 missing30088_30090 records30088_30090 :=
  aligned30088_30089.append aligned30089_30090

def missing30090_30091 : List (BitVec (edgeCount 12)) :=
  [missing30090]
abbrev records30090_30091 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30090]
theorem aligned30090_30091 :
    AlignedValid 12 4 missing30090_30091 records30090_30091 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30090
    maskCheck30090 AlignedValid.nil

def missing30091_30092 : List (BitVec (edgeCount 12)) :=
  [missing30091]
abbrev records30091_30092 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30091]
theorem aligned30091_30092 :
    AlignedValid 12 4 missing30091_30092 records30091_30092 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30091
    maskCheck30091 AlignedValid.nil

def missing30090_30092 : List (BitVec (edgeCount 12)) :=
  missing30090_30091 ++ missing30091_30092
abbrev records30090_30092 : List Blob :=
  records30090_30091 ++ records30091_30092
theorem aligned30090_30092 :
    AlignedValid 12 4 missing30090_30092 records30090_30092 :=
  aligned30090_30091.append aligned30091_30092

def missing30088_30092 : List (BitVec (edgeCount 12)) :=
  missing30088_30090 ++ missing30090_30092
abbrev records30088_30092 : List Blob :=
  records30088_30090 ++ records30090_30092
theorem aligned30088_30092 :
    AlignedValid 12 4 missing30088_30092 records30088_30092 :=
  aligned30088_30090.append aligned30090_30092

def missing30092_30093 : List (BitVec (edgeCount 12)) :=
  [missing30092]
abbrev records30092_30093 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30092]
theorem aligned30092_30093 :
    AlignedValid 12 4 missing30092_30093 records30092_30093 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30092
    maskCheck30092 AlignedValid.nil

def missing30093_30094 : List (BitVec (edgeCount 12)) :=
  [missing30093]
abbrev records30093_30094 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30093]
theorem aligned30093_30094 :
    AlignedValid 12 4 missing30093_30094 records30093_30094 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30093
    maskCheck30093 AlignedValid.nil

def missing30092_30094 : List (BitVec (edgeCount 12)) :=
  missing30092_30093 ++ missing30093_30094
abbrev records30092_30094 : List Blob :=
  records30092_30093 ++ records30093_30094
theorem aligned30092_30094 :
    AlignedValid 12 4 missing30092_30094 records30092_30094 :=
  aligned30092_30093.append aligned30093_30094

def missing30094_30095 : List (BitVec (edgeCount 12)) :=
  [missing30094]
abbrev records30094_30095 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30094]
theorem aligned30094_30095 :
    AlignedValid 12 4 missing30094_30095 records30094_30095 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30094
    maskCheck30094 AlignedValid.nil

def missing30095_30096 : List (BitVec (edgeCount 12)) :=
  [missing30095]
abbrev records30095_30096 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30095]
theorem aligned30095_30096 :
    AlignedValid 12 4 missing30095_30096 records30095_30096 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30095
    maskCheck30095 AlignedValid.nil

def missing30094_30096 : List (BitVec (edgeCount 12)) :=
  missing30094_30095 ++ missing30095_30096
abbrev records30094_30096 : List Blob :=
  records30094_30095 ++ records30095_30096
theorem aligned30094_30096 :
    AlignedValid 12 4 missing30094_30096 records30094_30096 :=
  aligned30094_30095.append aligned30095_30096

def missing30092_30096 : List (BitVec (edgeCount 12)) :=
  missing30092_30094 ++ missing30094_30096
abbrev records30092_30096 : List Blob :=
  records30092_30094 ++ records30094_30096
theorem aligned30092_30096 :
    AlignedValid 12 4 missing30092_30096 records30092_30096 :=
  aligned30092_30094.append aligned30094_30096

def missing30088_30096 : List (BitVec (edgeCount 12)) :=
  missing30088_30092 ++ missing30092_30096
abbrev records30088_30096 : List Blob :=
  records30088_30092 ++ records30092_30096
theorem aligned30088_30096 :
    AlignedValid 12 4 missing30088_30096 records30088_30096 :=
  aligned30088_30092.append aligned30092_30096

def missing30080_30096 : List (BitVec (edgeCount 12)) :=
  missing30080_30088 ++ missing30088_30096
abbrev records30080_30096 : List Blob :=
  records30080_30088 ++ records30088_30096
theorem aligned30080_30096 :
    AlignedValid 12 4 missing30080_30096 records30080_30096 :=
  aligned30080_30088.append aligned30088_30096

def missing30096_30097 : List (BitVec (edgeCount 12)) :=
  [missing30096]
abbrev records30096_30097 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30096]
theorem aligned30096_30097 :
    AlignedValid 12 4 missing30096_30097 records30096_30097 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30096
    maskCheck30096 AlignedValid.nil

def missing30097_30098 : List (BitVec (edgeCount 12)) :=
  [missing30097]
abbrev records30097_30098 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30097]
theorem aligned30097_30098 :
    AlignedValid 12 4 missing30097_30098 records30097_30098 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30097
    maskCheck30097 AlignedValid.nil

def missing30096_30098 : List (BitVec (edgeCount 12)) :=
  missing30096_30097 ++ missing30097_30098
abbrev records30096_30098 : List Blob :=
  records30096_30097 ++ records30097_30098
theorem aligned30096_30098 :
    AlignedValid 12 4 missing30096_30098 records30096_30098 :=
  aligned30096_30097.append aligned30097_30098

def missing30098_30099 : List (BitVec (edgeCount 12)) :=
  [missing30098]
abbrev records30098_30099 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30098]
theorem aligned30098_30099 :
    AlignedValid 12 4 missing30098_30099 records30098_30099 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30098
    maskCheck30098 AlignedValid.nil

def missing30099_30100 : List (BitVec (edgeCount 12)) :=
  [missing30099]
abbrev records30099_30100 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30099]
theorem aligned30099_30100 :
    AlignedValid 12 4 missing30099_30100 records30099_30100 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30099
    maskCheck30099 AlignedValid.nil

def missing30098_30100 : List (BitVec (edgeCount 12)) :=
  missing30098_30099 ++ missing30099_30100
abbrev records30098_30100 : List Blob :=
  records30098_30099 ++ records30099_30100
theorem aligned30098_30100 :
    AlignedValid 12 4 missing30098_30100 records30098_30100 :=
  aligned30098_30099.append aligned30099_30100

def missing30096_30100 : List (BitVec (edgeCount 12)) :=
  missing30096_30098 ++ missing30098_30100
abbrev records30096_30100 : List Blob :=
  records30096_30098 ++ records30098_30100
theorem aligned30096_30100 :
    AlignedValid 12 4 missing30096_30100 records30096_30100 :=
  aligned30096_30098.append aligned30098_30100

def missing30100_30101 : List (BitVec (edgeCount 12)) :=
  [missing30100]
abbrev records30100_30101 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30100]
theorem aligned30100_30101 :
    AlignedValid 12 4 missing30100_30101 records30100_30101 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30100
    maskCheck30100 AlignedValid.nil

def missing30101_30102 : List (BitVec (edgeCount 12)) :=
  [missing30101]
abbrev records30101_30102 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30101]
theorem aligned30101_30102 :
    AlignedValid 12 4 missing30101_30102 records30101_30102 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30101
    maskCheck30101 AlignedValid.nil

def missing30100_30102 : List (BitVec (edgeCount 12)) :=
  missing30100_30101 ++ missing30101_30102
abbrev records30100_30102 : List Blob :=
  records30100_30101 ++ records30101_30102
theorem aligned30100_30102 :
    AlignedValid 12 4 missing30100_30102 records30100_30102 :=
  aligned30100_30101.append aligned30101_30102

def missing30102_30103 : List (BitVec (edgeCount 12)) :=
  [missing30102]
abbrev records30102_30103 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30102]
theorem aligned30102_30103 :
    AlignedValid 12 4 missing30102_30103 records30102_30103 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30102
    maskCheck30102 AlignedValid.nil

def missing30103_30104 : List (BitVec (edgeCount 12)) :=
  [missing30103]
abbrev records30103_30104 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30103]
theorem aligned30103_30104 :
    AlignedValid 12 4 missing30103_30104 records30103_30104 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30103
    maskCheck30103 AlignedValid.nil

def missing30102_30104 : List (BitVec (edgeCount 12)) :=
  missing30102_30103 ++ missing30103_30104
abbrev records30102_30104 : List Blob :=
  records30102_30103 ++ records30103_30104
theorem aligned30102_30104 :
    AlignedValid 12 4 missing30102_30104 records30102_30104 :=
  aligned30102_30103.append aligned30103_30104

def missing30100_30104 : List (BitVec (edgeCount 12)) :=
  missing30100_30102 ++ missing30102_30104
abbrev records30100_30104 : List Blob :=
  records30100_30102 ++ records30102_30104
theorem aligned30100_30104 :
    AlignedValid 12 4 missing30100_30104 records30100_30104 :=
  aligned30100_30102.append aligned30102_30104

def missing30096_30104 : List (BitVec (edgeCount 12)) :=
  missing30096_30100 ++ missing30100_30104
abbrev records30096_30104 : List Blob :=
  records30096_30100 ++ records30100_30104
theorem aligned30096_30104 :
    AlignedValid 12 4 missing30096_30104 records30096_30104 :=
  aligned30096_30100.append aligned30100_30104

def missing30104_30105 : List (BitVec (edgeCount 12)) :=
  [missing30104]
abbrev records30104_30105 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30104]
theorem aligned30104_30105 :
    AlignedValid 12 4 missing30104_30105 records30104_30105 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30104
    maskCheck30104 AlignedValid.nil

def missing30105_30106 : List (BitVec (edgeCount 12)) :=
  [missing30105]
abbrev records30105_30106 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30105]
theorem aligned30105_30106 :
    AlignedValid 12 4 missing30105_30106 records30105_30106 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30105
    maskCheck30105 AlignedValid.nil

def missing30104_30106 : List (BitVec (edgeCount 12)) :=
  missing30104_30105 ++ missing30105_30106
abbrev records30104_30106 : List Blob :=
  records30104_30105 ++ records30105_30106
theorem aligned30104_30106 :
    AlignedValid 12 4 missing30104_30106 records30104_30106 :=
  aligned30104_30105.append aligned30105_30106

def missing30106_30107 : List (BitVec (edgeCount 12)) :=
  [missing30106]
abbrev records30106_30107 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30106]
theorem aligned30106_30107 :
    AlignedValid 12 4 missing30106_30107 records30106_30107 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30106
    maskCheck30106 AlignedValid.nil

def missing30107_30108 : List (BitVec (edgeCount 12)) :=
  [missing30107]
abbrev records30107_30108 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30107]
theorem aligned30107_30108 :
    AlignedValid 12 4 missing30107_30108 records30107_30108 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30107
    maskCheck30107 AlignedValid.nil

def missing30106_30108 : List (BitVec (edgeCount 12)) :=
  missing30106_30107 ++ missing30107_30108
abbrev records30106_30108 : List Blob :=
  records30106_30107 ++ records30107_30108
theorem aligned30106_30108 :
    AlignedValid 12 4 missing30106_30108 records30106_30108 :=
  aligned30106_30107.append aligned30107_30108

def missing30104_30108 : List (BitVec (edgeCount 12)) :=
  missing30104_30106 ++ missing30106_30108
abbrev records30104_30108 : List Blob :=
  records30104_30106 ++ records30106_30108
theorem aligned30104_30108 :
    AlignedValid 12 4 missing30104_30108 records30104_30108 :=
  aligned30104_30106.append aligned30106_30108

def missing30108_30109 : List (BitVec (edgeCount 12)) :=
  [missing30108]
abbrev records30108_30109 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30108]
theorem aligned30108_30109 :
    AlignedValid 12 4 missing30108_30109 records30108_30109 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30108
    maskCheck30108 AlignedValid.nil

def missing30109_30110 : List (BitVec (edgeCount 12)) :=
  [missing30109]
abbrev records30109_30110 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30109]
theorem aligned30109_30110 :
    AlignedValid 12 4 missing30109_30110 records30109_30110 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30109
    maskCheck30109 AlignedValid.nil

def missing30108_30110 : List (BitVec (edgeCount 12)) :=
  missing30108_30109 ++ missing30109_30110
abbrev records30108_30110 : List Blob :=
  records30108_30109 ++ records30109_30110
theorem aligned30108_30110 :
    AlignedValid 12 4 missing30108_30110 records30108_30110 :=
  aligned30108_30109.append aligned30109_30110

def missing30110_30111 : List (BitVec (edgeCount 12)) :=
  [missing30110]
abbrev records30110_30111 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30110]
theorem aligned30110_30111 :
    AlignedValid 12 4 missing30110_30111 records30110_30111 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30110
    maskCheck30110 AlignedValid.nil

def missing30111_30112 : List (BitVec (edgeCount 12)) :=
  [missing30111]
abbrev records30111_30112 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30111]
theorem aligned30111_30112 :
    AlignedValid 12 4 missing30111_30112 records30111_30112 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30111
    maskCheck30111 AlignedValid.nil

def missing30110_30112 : List (BitVec (edgeCount 12)) :=
  missing30110_30111 ++ missing30111_30112
abbrev records30110_30112 : List Blob :=
  records30110_30111 ++ records30111_30112
theorem aligned30110_30112 :
    AlignedValid 12 4 missing30110_30112 records30110_30112 :=
  aligned30110_30111.append aligned30111_30112

def missing30108_30112 : List (BitVec (edgeCount 12)) :=
  missing30108_30110 ++ missing30110_30112
abbrev records30108_30112 : List Blob :=
  records30108_30110 ++ records30110_30112
theorem aligned30108_30112 :
    AlignedValid 12 4 missing30108_30112 records30108_30112 :=
  aligned30108_30110.append aligned30110_30112

def missing30104_30112 : List (BitVec (edgeCount 12)) :=
  missing30104_30108 ++ missing30108_30112
abbrev records30104_30112 : List Blob :=
  records30104_30108 ++ records30108_30112
theorem aligned30104_30112 :
    AlignedValid 12 4 missing30104_30112 records30104_30112 :=
  aligned30104_30108.append aligned30108_30112

def missing30096_30112 : List (BitVec (edgeCount 12)) :=
  missing30096_30104 ++ missing30104_30112
abbrev records30096_30112 : List Blob :=
  records30096_30104 ++ records30104_30112
theorem aligned30096_30112 :
    AlignedValid 12 4 missing30096_30112 records30096_30112 :=
  aligned30096_30104.append aligned30104_30112

def missing30080_30112 : List (BitVec (edgeCount 12)) :=
  missing30080_30096 ++ missing30096_30112
abbrev records30080_30112 : List Blob :=
  records30080_30096 ++ records30096_30112
theorem aligned30080_30112 :
    AlignedValid 12 4 missing30080_30112 records30080_30112 :=
  aligned30080_30096.append aligned30096_30112

def missing30112_30113 : List (BitVec (edgeCount 12)) :=
  [missing30112]
abbrev records30112_30113 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30112]
theorem aligned30112_30113 :
    AlignedValid 12 4 missing30112_30113 records30112_30113 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30112
    maskCheck30112 AlignedValid.nil

def missing30113_30114 : List (BitVec (edgeCount 12)) :=
  [missing30113]
abbrev records30113_30114 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30113]
theorem aligned30113_30114 :
    AlignedValid 12 4 missing30113_30114 records30113_30114 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30113
    maskCheck30113 AlignedValid.nil

def missing30112_30114 : List (BitVec (edgeCount 12)) :=
  missing30112_30113 ++ missing30113_30114
abbrev records30112_30114 : List Blob :=
  records30112_30113 ++ records30113_30114
theorem aligned30112_30114 :
    AlignedValid 12 4 missing30112_30114 records30112_30114 :=
  aligned30112_30113.append aligned30113_30114

def missing30114_30115 : List (BitVec (edgeCount 12)) :=
  [missing30114]
abbrev records30114_30115 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30114]
theorem aligned30114_30115 :
    AlignedValid 12 4 missing30114_30115 records30114_30115 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30114
    maskCheck30114 AlignedValid.nil

def missing30115_30116 : List (BitVec (edgeCount 12)) :=
  [missing30115]
abbrev records30115_30116 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30115]
theorem aligned30115_30116 :
    AlignedValid 12 4 missing30115_30116 records30115_30116 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30115
    maskCheck30115 AlignedValid.nil

def missing30114_30116 : List (BitVec (edgeCount 12)) :=
  missing30114_30115 ++ missing30115_30116
abbrev records30114_30116 : List Blob :=
  records30114_30115 ++ records30115_30116
theorem aligned30114_30116 :
    AlignedValid 12 4 missing30114_30116 records30114_30116 :=
  aligned30114_30115.append aligned30115_30116

def missing30112_30116 : List (BitVec (edgeCount 12)) :=
  missing30112_30114 ++ missing30114_30116
abbrev records30112_30116 : List Blob :=
  records30112_30114 ++ records30114_30116
theorem aligned30112_30116 :
    AlignedValid 12 4 missing30112_30116 records30112_30116 :=
  aligned30112_30114.append aligned30114_30116

def missing30116_30117 : List (BitVec (edgeCount 12)) :=
  [missing30116]
abbrev records30116_30117 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30116]
theorem aligned30116_30117 :
    AlignedValid 12 4 missing30116_30117 records30116_30117 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30116
    maskCheck30116 AlignedValid.nil

def missing30117_30118 : List (BitVec (edgeCount 12)) :=
  [missing30117]
abbrev records30117_30118 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30117]
theorem aligned30117_30118 :
    AlignedValid 12 4 missing30117_30118 records30117_30118 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30117
    maskCheck30117 AlignedValid.nil

def missing30116_30118 : List (BitVec (edgeCount 12)) :=
  missing30116_30117 ++ missing30117_30118
abbrev records30116_30118 : List Blob :=
  records30116_30117 ++ records30117_30118
theorem aligned30116_30118 :
    AlignedValid 12 4 missing30116_30118 records30116_30118 :=
  aligned30116_30117.append aligned30117_30118

def missing30118_30119 : List (BitVec (edgeCount 12)) :=
  [missing30118]
abbrev records30118_30119 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30118]
theorem aligned30118_30119 :
    AlignedValid 12 4 missing30118_30119 records30118_30119 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30118
    maskCheck30118 AlignedValid.nil

def missing30119_30120 : List (BitVec (edgeCount 12)) :=
  [missing30119]
abbrev records30119_30120 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30119]
theorem aligned30119_30120 :
    AlignedValid 12 4 missing30119_30120 records30119_30120 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30119
    maskCheck30119 AlignedValid.nil

def missing30118_30120 : List (BitVec (edgeCount 12)) :=
  missing30118_30119 ++ missing30119_30120
abbrev records30118_30120 : List Blob :=
  records30118_30119 ++ records30119_30120
theorem aligned30118_30120 :
    AlignedValid 12 4 missing30118_30120 records30118_30120 :=
  aligned30118_30119.append aligned30119_30120

def missing30116_30120 : List (BitVec (edgeCount 12)) :=
  missing30116_30118 ++ missing30118_30120
abbrev records30116_30120 : List Blob :=
  records30116_30118 ++ records30118_30120
theorem aligned30116_30120 :
    AlignedValid 12 4 missing30116_30120 records30116_30120 :=
  aligned30116_30118.append aligned30118_30120

def missing30112_30120 : List (BitVec (edgeCount 12)) :=
  missing30112_30116 ++ missing30116_30120
abbrev records30112_30120 : List Blob :=
  records30112_30116 ++ records30116_30120
theorem aligned30112_30120 :
    AlignedValid 12 4 missing30112_30120 records30112_30120 :=
  aligned30112_30116.append aligned30116_30120

def missing30120_30121 : List (BitVec (edgeCount 12)) :=
  [missing30120]
abbrev records30120_30121 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30120]
theorem aligned30120_30121 :
    AlignedValid 12 4 missing30120_30121 records30120_30121 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30120
    maskCheck30120 AlignedValid.nil

def missing30121_30122 : List (BitVec (edgeCount 12)) :=
  [missing30121]
abbrev records30121_30122 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30121]
theorem aligned30121_30122 :
    AlignedValid 12 4 missing30121_30122 records30121_30122 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30121
    maskCheck30121 AlignedValid.nil

def missing30120_30122 : List (BitVec (edgeCount 12)) :=
  missing30120_30121 ++ missing30121_30122
abbrev records30120_30122 : List Blob :=
  records30120_30121 ++ records30121_30122
theorem aligned30120_30122 :
    AlignedValid 12 4 missing30120_30122 records30120_30122 :=
  aligned30120_30121.append aligned30121_30122

def missing30122_30123 : List (BitVec (edgeCount 12)) :=
  [missing30122]
abbrev records30122_30123 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30122]
theorem aligned30122_30123 :
    AlignedValid 12 4 missing30122_30123 records30122_30123 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30122
    maskCheck30122 AlignedValid.nil

def missing30123_30124 : List (BitVec (edgeCount 12)) :=
  [missing30123]
abbrev records30123_30124 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30123]
theorem aligned30123_30124 :
    AlignedValid 12 4 missing30123_30124 records30123_30124 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30123
    maskCheck30123 AlignedValid.nil

def missing30122_30124 : List (BitVec (edgeCount 12)) :=
  missing30122_30123 ++ missing30123_30124
abbrev records30122_30124 : List Blob :=
  records30122_30123 ++ records30123_30124
theorem aligned30122_30124 :
    AlignedValid 12 4 missing30122_30124 records30122_30124 :=
  aligned30122_30123.append aligned30123_30124

def missing30120_30124 : List (BitVec (edgeCount 12)) :=
  missing30120_30122 ++ missing30122_30124
abbrev records30120_30124 : List Blob :=
  records30120_30122 ++ records30122_30124
theorem aligned30120_30124 :
    AlignedValid 12 4 missing30120_30124 records30120_30124 :=
  aligned30120_30122.append aligned30122_30124

def missing30124_30125 : List (BitVec (edgeCount 12)) :=
  [missing30124]
abbrev records30124_30125 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30124]
theorem aligned30124_30125 :
    AlignedValid 12 4 missing30124_30125 records30124_30125 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30124
    maskCheck30124 AlignedValid.nil

def missing30125_30126 : List (BitVec (edgeCount 12)) :=
  [missing30125]
abbrev records30125_30126 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30125]
theorem aligned30125_30126 :
    AlignedValid 12 4 missing30125_30126 records30125_30126 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30125
    maskCheck30125 AlignedValid.nil

def missing30124_30126 : List (BitVec (edgeCount 12)) :=
  missing30124_30125 ++ missing30125_30126
abbrev records30124_30126 : List Blob :=
  records30124_30125 ++ records30125_30126
theorem aligned30124_30126 :
    AlignedValid 12 4 missing30124_30126 records30124_30126 :=
  aligned30124_30125.append aligned30125_30126

def missing30126_30127 : List (BitVec (edgeCount 12)) :=
  [missing30126]
abbrev records30126_30127 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30126]
theorem aligned30126_30127 :
    AlignedValid 12 4 missing30126_30127 records30126_30127 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30126
    maskCheck30126 AlignedValid.nil

def missing30127_30128 : List (BitVec (edgeCount 12)) :=
  [missing30127]
abbrev records30127_30128 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30127]
theorem aligned30127_30128 :
    AlignedValid 12 4 missing30127_30128 records30127_30128 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30127
    maskCheck30127 AlignedValid.nil

def missing30126_30128 : List (BitVec (edgeCount 12)) :=
  missing30126_30127 ++ missing30127_30128
abbrev records30126_30128 : List Blob :=
  records30126_30127 ++ records30127_30128
theorem aligned30126_30128 :
    AlignedValid 12 4 missing30126_30128 records30126_30128 :=
  aligned30126_30127.append aligned30127_30128

def missing30124_30128 : List (BitVec (edgeCount 12)) :=
  missing30124_30126 ++ missing30126_30128
abbrev records30124_30128 : List Blob :=
  records30124_30126 ++ records30126_30128
theorem aligned30124_30128 :
    AlignedValid 12 4 missing30124_30128 records30124_30128 :=
  aligned30124_30126.append aligned30126_30128

def missing30120_30128 : List (BitVec (edgeCount 12)) :=
  missing30120_30124 ++ missing30124_30128
abbrev records30120_30128 : List Blob :=
  records30120_30124 ++ records30124_30128
theorem aligned30120_30128 :
    AlignedValid 12 4 missing30120_30128 records30120_30128 :=
  aligned30120_30124.append aligned30124_30128

def missing30112_30128 : List (BitVec (edgeCount 12)) :=
  missing30112_30120 ++ missing30120_30128
abbrev records30112_30128 : List Blob :=
  records30112_30120 ++ records30120_30128
theorem aligned30112_30128 :
    AlignedValid 12 4 missing30112_30128 records30112_30128 :=
  aligned30112_30120.append aligned30120_30128

def missing30128_30129 : List (BitVec (edgeCount 12)) :=
  [missing30128]
abbrev records30128_30129 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30128]
theorem aligned30128_30129 :
    AlignedValid 12 4 missing30128_30129 records30128_30129 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30128
    maskCheck30128 AlignedValid.nil

def missing30129_30130 : List (BitVec (edgeCount 12)) :=
  [missing30129]
abbrev records30129_30130 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30129]
theorem aligned30129_30130 :
    AlignedValid 12 4 missing30129_30130 records30129_30130 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30129
    maskCheck30129 AlignedValid.nil

def missing30128_30130 : List (BitVec (edgeCount 12)) :=
  missing30128_30129 ++ missing30129_30130
abbrev records30128_30130 : List Blob :=
  records30128_30129 ++ records30129_30130
theorem aligned30128_30130 :
    AlignedValid 12 4 missing30128_30130 records30128_30130 :=
  aligned30128_30129.append aligned30129_30130

def missing30130_30131 : List (BitVec (edgeCount 12)) :=
  [missing30130]
abbrev records30130_30131 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30130]
theorem aligned30130_30131 :
    AlignedValid 12 4 missing30130_30131 records30130_30131 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30130
    maskCheck30130 AlignedValid.nil

def missing30131_30132 : List (BitVec (edgeCount 12)) :=
  [missing30131]
abbrev records30131_30132 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30131]
theorem aligned30131_30132 :
    AlignedValid 12 4 missing30131_30132 records30131_30132 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30131
    maskCheck30131 AlignedValid.nil

def missing30130_30132 : List (BitVec (edgeCount 12)) :=
  missing30130_30131 ++ missing30131_30132
abbrev records30130_30132 : List Blob :=
  records30130_30131 ++ records30131_30132
theorem aligned30130_30132 :
    AlignedValid 12 4 missing30130_30132 records30130_30132 :=
  aligned30130_30131.append aligned30131_30132

def missing30128_30132 : List (BitVec (edgeCount 12)) :=
  missing30128_30130 ++ missing30130_30132
abbrev records30128_30132 : List Blob :=
  records30128_30130 ++ records30130_30132
theorem aligned30128_30132 :
    AlignedValid 12 4 missing30128_30132 records30128_30132 :=
  aligned30128_30130.append aligned30130_30132

def missing30132_30133 : List (BitVec (edgeCount 12)) :=
  [missing30132]
abbrev records30132_30133 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30132]
theorem aligned30132_30133 :
    AlignedValid 12 4 missing30132_30133 records30132_30133 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30132
    maskCheck30132 AlignedValid.nil

def missing30133_30134 : List (BitVec (edgeCount 12)) :=
  [missing30133]
abbrev records30133_30134 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30133]
theorem aligned30133_30134 :
    AlignedValid 12 4 missing30133_30134 records30133_30134 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30133
    maskCheck30133 AlignedValid.nil

def missing30132_30134 : List (BitVec (edgeCount 12)) :=
  missing30132_30133 ++ missing30133_30134
abbrev records30132_30134 : List Blob :=
  records30132_30133 ++ records30133_30134
theorem aligned30132_30134 :
    AlignedValid 12 4 missing30132_30134 records30132_30134 :=
  aligned30132_30133.append aligned30133_30134

def missing30134_30135 : List (BitVec (edgeCount 12)) :=
  [missing30134]
abbrev records30134_30135 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30134]
theorem aligned30134_30135 :
    AlignedValid 12 4 missing30134_30135 records30134_30135 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30134
    maskCheck30134 AlignedValid.nil

def missing30135_30136 : List (BitVec (edgeCount 12)) :=
  [missing30135]
abbrev records30135_30136 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30135]
theorem aligned30135_30136 :
    AlignedValid 12 4 missing30135_30136 records30135_30136 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30135
    maskCheck30135 AlignedValid.nil

def missing30134_30136 : List (BitVec (edgeCount 12)) :=
  missing30134_30135 ++ missing30135_30136
abbrev records30134_30136 : List Blob :=
  records30134_30135 ++ records30135_30136
theorem aligned30134_30136 :
    AlignedValid 12 4 missing30134_30136 records30134_30136 :=
  aligned30134_30135.append aligned30135_30136

def missing30132_30136 : List (BitVec (edgeCount 12)) :=
  missing30132_30134 ++ missing30134_30136
abbrev records30132_30136 : List Blob :=
  records30132_30134 ++ records30134_30136
theorem aligned30132_30136 :
    AlignedValid 12 4 missing30132_30136 records30132_30136 :=
  aligned30132_30134.append aligned30134_30136

def missing30128_30136 : List (BitVec (edgeCount 12)) :=
  missing30128_30132 ++ missing30132_30136
abbrev records30128_30136 : List Blob :=
  records30128_30132 ++ records30132_30136
theorem aligned30128_30136 :
    AlignedValid 12 4 missing30128_30136 records30128_30136 :=
  aligned30128_30132.append aligned30132_30136

def missing30136_30137 : List (BitVec (edgeCount 12)) :=
  [missing30136]
abbrev records30136_30137 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30136]
theorem aligned30136_30137 :
    AlignedValid 12 4 missing30136_30137 records30136_30137 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30136
    maskCheck30136 AlignedValid.nil

def missing30137_30138 : List (BitVec (edgeCount 12)) :=
  [missing30137]
abbrev records30137_30138 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30137]
theorem aligned30137_30138 :
    AlignedValid 12 4 missing30137_30138 records30137_30138 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30137
    maskCheck30137 AlignedValid.nil

def missing30136_30138 : List (BitVec (edgeCount 12)) :=
  missing30136_30137 ++ missing30137_30138
abbrev records30136_30138 : List Blob :=
  records30136_30137 ++ records30137_30138
theorem aligned30136_30138 :
    AlignedValid 12 4 missing30136_30138 records30136_30138 :=
  aligned30136_30137.append aligned30137_30138

def missing30138_30139 : List (BitVec (edgeCount 12)) :=
  [missing30138]
abbrev records30138_30139 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30138]
theorem aligned30138_30139 :
    AlignedValid 12 4 missing30138_30139 records30138_30139 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30138
    maskCheck30138 AlignedValid.nil

def missing30139_30140 : List (BitVec (edgeCount 12)) :=
  [missing30139]
abbrev records30139_30140 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30139]
theorem aligned30139_30140 :
    AlignedValid 12 4 missing30139_30140 records30139_30140 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30139
    maskCheck30139 AlignedValid.nil

def missing30138_30140 : List (BitVec (edgeCount 12)) :=
  missing30138_30139 ++ missing30139_30140
abbrev records30138_30140 : List Blob :=
  records30138_30139 ++ records30139_30140
theorem aligned30138_30140 :
    AlignedValid 12 4 missing30138_30140 records30138_30140 :=
  aligned30138_30139.append aligned30139_30140

def missing30136_30140 : List (BitVec (edgeCount 12)) :=
  missing30136_30138 ++ missing30138_30140
abbrev records30136_30140 : List Blob :=
  records30136_30138 ++ records30138_30140
theorem aligned30136_30140 :
    AlignedValid 12 4 missing30136_30140 records30136_30140 :=
  aligned30136_30138.append aligned30138_30140

def missing30140_30141 : List (BitVec (edgeCount 12)) :=
  [missing30140]
abbrev records30140_30141 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30140]
theorem aligned30140_30141 :
    AlignedValid 12 4 missing30140_30141 records30140_30141 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30140
    maskCheck30140 AlignedValid.nil

def missing30141_30142 : List (BitVec (edgeCount 12)) :=
  [missing30141]
abbrev records30141_30142 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30141]
theorem aligned30141_30142 :
    AlignedValid 12 4 missing30141_30142 records30141_30142 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30141
    maskCheck30141 AlignedValid.nil

def missing30140_30142 : List (BitVec (edgeCount 12)) :=
  missing30140_30141 ++ missing30141_30142
abbrev records30140_30142 : List Blob :=
  records30140_30141 ++ records30141_30142
theorem aligned30140_30142 :
    AlignedValid 12 4 missing30140_30142 records30140_30142 :=
  aligned30140_30141.append aligned30141_30142

def missing30142_30143 : List (BitVec (edgeCount 12)) :=
  [missing30142]
abbrev records30142_30143 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30142]
theorem aligned30142_30143 :
    AlignedValid 12 4 missing30142_30143 records30142_30143 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30142
    maskCheck30142 AlignedValid.nil

def missing30143_30144 : List (BitVec (edgeCount 12)) :=
  [missing30143]
abbrev records30143_30144 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30143]
theorem aligned30143_30144 :
    AlignedValid 12 4 missing30143_30144 records30143_30144 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30143
    maskCheck30143 AlignedValid.nil

def missing30142_30144 : List (BitVec (edgeCount 12)) :=
  missing30142_30143 ++ missing30143_30144
abbrev records30142_30144 : List Blob :=
  records30142_30143 ++ records30143_30144
theorem aligned30142_30144 :
    AlignedValid 12 4 missing30142_30144 records30142_30144 :=
  aligned30142_30143.append aligned30143_30144

def missing30140_30144 : List (BitVec (edgeCount 12)) :=
  missing30140_30142 ++ missing30142_30144
abbrev records30140_30144 : List Blob :=
  records30140_30142 ++ records30142_30144
theorem aligned30140_30144 :
    AlignedValid 12 4 missing30140_30144 records30140_30144 :=
  aligned30140_30142.append aligned30142_30144

def missing30136_30144 : List (BitVec (edgeCount 12)) :=
  missing30136_30140 ++ missing30140_30144
abbrev records30136_30144 : List Blob :=
  records30136_30140 ++ records30140_30144
theorem aligned30136_30144 :
    AlignedValid 12 4 missing30136_30144 records30136_30144 :=
  aligned30136_30140.append aligned30140_30144

def missing30128_30144 : List (BitVec (edgeCount 12)) :=
  missing30128_30136 ++ missing30136_30144
abbrev records30128_30144 : List Blob :=
  records30128_30136 ++ records30136_30144
theorem aligned30128_30144 :
    AlignedValid 12 4 missing30128_30144 records30128_30144 :=
  aligned30128_30136.append aligned30136_30144

def missing30112_30144 : List (BitVec (edgeCount 12)) :=
  missing30112_30128 ++ missing30128_30144
abbrev records30112_30144 : List Blob :=
  records30112_30128 ++ records30128_30144
theorem aligned30112_30144 :
    AlignedValid 12 4 missing30112_30144 records30112_30144 :=
  aligned30112_30128.append aligned30128_30144

def missing30080_30144 : List (BitVec (edgeCount 12)) :=
  missing30080_30112 ++ missing30112_30144
abbrev records30080_30144 : List Blob :=
  records30080_30112 ++ records30112_30144
theorem aligned30080_30144 :
    AlignedValid 12 4 missing30080_30144 records30080_30144 :=
  aligned30080_30112.append aligned30112_30144

def missing30144_30145 : List (BitVec (edgeCount 12)) :=
  [missing30144]
abbrev records30144_30145 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30144]
theorem aligned30144_30145 :
    AlignedValid 12 4 missing30144_30145 records30144_30145 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30144
    maskCheck30144 AlignedValid.nil

def missing30145_30146 : List (BitVec (edgeCount 12)) :=
  [missing30145]
abbrev records30145_30146 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30145]
theorem aligned30145_30146 :
    AlignedValid 12 4 missing30145_30146 records30145_30146 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30145
    maskCheck30145 AlignedValid.nil

def missing30144_30146 : List (BitVec (edgeCount 12)) :=
  missing30144_30145 ++ missing30145_30146
abbrev records30144_30146 : List Blob :=
  records30144_30145 ++ records30145_30146
theorem aligned30144_30146 :
    AlignedValid 12 4 missing30144_30146 records30144_30146 :=
  aligned30144_30145.append aligned30145_30146

def missing30146_30147 : List (BitVec (edgeCount 12)) :=
  [missing30146]
abbrev records30146_30147 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30146]
theorem aligned30146_30147 :
    AlignedValid 12 4 missing30146_30147 records30146_30147 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30146
    maskCheck30146 AlignedValid.nil

def missing30147_30148 : List (BitVec (edgeCount 12)) :=
  [missing30147]
abbrev records30147_30148 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30147]
theorem aligned30147_30148 :
    AlignedValid 12 4 missing30147_30148 records30147_30148 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30147
    maskCheck30147 AlignedValid.nil

def missing30146_30148 : List (BitVec (edgeCount 12)) :=
  missing30146_30147 ++ missing30147_30148
abbrev records30146_30148 : List Blob :=
  records30146_30147 ++ records30147_30148
theorem aligned30146_30148 :
    AlignedValid 12 4 missing30146_30148 records30146_30148 :=
  aligned30146_30147.append aligned30147_30148

def missing30144_30148 : List (BitVec (edgeCount 12)) :=
  missing30144_30146 ++ missing30146_30148
abbrev records30144_30148 : List Blob :=
  records30144_30146 ++ records30146_30148
theorem aligned30144_30148 :
    AlignedValid 12 4 missing30144_30148 records30144_30148 :=
  aligned30144_30146.append aligned30146_30148

def missing30148_30149 : List (BitVec (edgeCount 12)) :=
  [missing30148]
abbrev records30148_30149 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30148]
theorem aligned30148_30149 :
    AlignedValid 12 4 missing30148_30149 records30148_30149 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30148
    maskCheck30148 AlignedValid.nil

def missing30149_30150 : List (BitVec (edgeCount 12)) :=
  [missing30149]
abbrev records30149_30150 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30149]
theorem aligned30149_30150 :
    AlignedValid 12 4 missing30149_30150 records30149_30150 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30149
    maskCheck30149 AlignedValid.nil

def missing30148_30150 : List (BitVec (edgeCount 12)) :=
  missing30148_30149 ++ missing30149_30150
abbrev records30148_30150 : List Blob :=
  records30148_30149 ++ records30149_30150
theorem aligned30148_30150 :
    AlignedValid 12 4 missing30148_30150 records30148_30150 :=
  aligned30148_30149.append aligned30149_30150

def missing30150_30151 : List (BitVec (edgeCount 12)) :=
  [missing30150]
abbrev records30150_30151 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30150]
theorem aligned30150_30151 :
    AlignedValid 12 4 missing30150_30151 records30150_30151 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30150
    maskCheck30150 AlignedValid.nil

def missing30151_30152 : List (BitVec (edgeCount 12)) :=
  [missing30151]
abbrev records30151_30152 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30151]
theorem aligned30151_30152 :
    AlignedValid 12 4 missing30151_30152 records30151_30152 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30151
    maskCheck30151 AlignedValid.nil

def missing30150_30152 : List (BitVec (edgeCount 12)) :=
  missing30150_30151 ++ missing30151_30152
abbrev records30150_30152 : List Blob :=
  records30150_30151 ++ records30151_30152
theorem aligned30150_30152 :
    AlignedValid 12 4 missing30150_30152 records30150_30152 :=
  aligned30150_30151.append aligned30151_30152

def missing30148_30152 : List (BitVec (edgeCount 12)) :=
  missing30148_30150 ++ missing30150_30152
abbrev records30148_30152 : List Blob :=
  records30148_30150 ++ records30150_30152
theorem aligned30148_30152 :
    AlignedValid 12 4 missing30148_30152 records30148_30152 :=
  aligned30148_30150.append aligned30150_30152

def missing30144_30152 : List (BitVec (edgeCount 12)) :=
  missing30144_30148 ++ missing30148_30152
abbrev records30144_30152 : List Blob :=
  records30144_30148 ++ records30148_30152
theorem aligned30144_30152 :
    AlignedValid 12 4 missing30144_30152 records30144_30152 :=
  aligned30144_30148.append aligned30148_30152

def missing30152_30153 : List (BitVec (edgeCount 12)) :=
  [missing30152]
abbrev records30152_30153 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30152]
theorem aligned30152_30153 :
    AlignedValid 12 4 missing30152_30153 records30152_30153 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30152
    maskCheck30152 AlignedValid.nil

def missing30153_30154 : List (BitVec (edgeCount 12)) :=
  [missing30153]
abbrev records30153_30154 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30153]
theorem aligned30153_30154 :
    AlignedValid 12 4 missing30153_30154 records30153_30154 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30153
    maskCheck30153 AlignedValid.nil

def missing30152_30154 : List (BitVec (edgeCount 12)) :=
  missing30152_30153 ++ missing30153_30154
abbrev records30152_30154 : List Blob :=
  records30152_30153 ++ records30153_30154
theorem aligned30152_30154 :
    AlignedValid 12 4 missing30152_30154 records30152_30154 :=
  aligned30152_30153.append aligned30153_30154

def missing30154_30155 : List (BitVec (edgeCount 12)) :=
  [missing30154]
abbrev records30154_30155 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30154]
theorem aligned30154_30155 :
    AlignedValid 12 4 missing30154_30155 records30154_30155 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30154
    maskCheck30154 AlignedValid.nil

def missing30155_30156 : List (BitVec (edgeCount 12)) :=
  [missing30155]
abbrev records30155_30156 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30155]
theorem aligned30155_30156 :
    AlignedValid 12 4 missing30155_30156 records30155_30156 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30155
    maskCheck30155 AlignedValid.nil

def missing30154_30156 : List (BitVec (edgeCount 12)) :=
  missing30154_30155 ++ missing30155_30156
abbrev records30154_30156 : List Blob :=
  records30154_30155 ++ records30155_30156
theorem aligned30154_30156 :
    AlignedValid 12 4 missing30154_30156 records30154_30156 :=
  aligned30154_30155.append aligned30155_30156

def missing30152_30156 : List (BitVec (edgeCount 12)) :=
  missing30152_30154 ++ missing30154_30156
abbrev records30152_30156 : List Blob :=
  records30152_30154 ++ records30154_30156
theorem aligned30152_30156 :
    AlignedValid 12 4 missing30152_30156 records30152_30156 :=
  aligned30152_30154.append aligned30154_30156

def missing30156_30157 : List (BitVec (edgeCount 12)) :=
  [missing30156]
abbrev records30156_30157 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30156]
theorem aligned30156_30157 :
    AlignedValid 12 4 missing30156_30157 records30156_30157 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30156
    maskCheck30156 AlignedValid.nil

def missing30157_30158 : List (BitVec (edgeCount 12)) :=
  [missing30157]
abbrev records30157_30158 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30157]
theorem aligned30157_30158 :
    AlignedValid 12 4 missing30157_30158 records30157_30158 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30157
    maskCheck30157 AlignedValid.nil

def missing30156_30158 : List (BitVec (edgeCount 12)) :=
  missing30156_30157 ++ missing30157_30158
abbrev records30156_30158 : List Blob :=
  records30156_30157 ++ records30157_30158
theorem aligned30156_30158 :
    AlignedValid 12 4 missing30156_30158 records30156_30158 :=
  aligned30156_30157.append aligned30157_30158

def missing30158_30159 : List (BitVec (edgeCount 12)) :=
  [missing30158]
abbrev records30158_30159 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30158]
theorem aligned30158_30159 :
    AlignedValid 12 4 missing30158_30159 records30158_30159 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30158
    maskCheck30158 AlignedValid.nil

def missing30159_30160 : List (BitVec (edgeCount 12)) :=
  [missing30159]
abbrev records30159_30160 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30159]
theorem aligned30159_30160 :
    AlignedValid 12 4 missing30159_30160 records30159_30160 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30159
    maskCheck30159 AlignedValid.nil

def missing30158_30160 : List (BitVec (edgeCount 12)) :=
  missing30158_30159 ++ missing30159_30160
abbrev records30158_30160 : List Blob :=
  records30158_30159 ++ records30159_30160
theorem aligned30158_30160 :
    AlignedValid 12 4 missing30158_30160 records30158_30160 :=
  aligned30158_30159.append aligned30159_30160

def missing30156_30160 : List (BitVec (edgeCount 12)) :=
  missing30156_30158 ++ missing30158_30160
abbrev records30156_30160 : List Blob :=
  records30156_30158 ++ records30158_30160
theorem aligned30156_30160 :
    AlignedValid 12 4 missing30156_30160 records30156_30160 :=
  aligned30156_30158.append aligned30158_30160

def missing30152_30160 : List (BitVec (edgeCount 12)) :=
  missing30152_30156 ++ missing30156_30160
abbrev records30152_30160 : List Blob :=
  records30152_30156 ++ records30156_30160
theorem aligned30152_30160 :
    AlignedValid 12 4 missing30152_30160 records30152_30160 :=
  aligned30152_30156.append aligned30156_30160

def missing30144_30160 : List (BitVec (edgeCount 12)) :=
  missing30144_30152 ++ missing30152_30160
abbrev records30144_30160 : List Blob :=
  records30144_30152 ++ records30152_30160
theorem aligned30144_30160 :
    AlignedValid 12 4 missing30144_30160 records30144_30160 :=
  aligned30144_30152.append aligned30152_30160

def missing30160_30161 : List (BitVec (edgeCount 12)) :=
  [missing30160]
abbrev records30160_30161 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30160]
theorem aligned30160_30161 :
    AlignedValid 12 4 missing30160_30161 records30160_30161 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30160
    maskCheck30160 AlignedValid.nil

def missing30161_30162 : List (BitVec (edgeCount 12)) :=
  [missing30161]
abbrev records30161_30162 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30161]
theorem aligned30161_30162 :
    AlignedValid 12 4 missing30161_30162 records30161_30162 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30161
    maskCheck30161 AlignedValid.nil

def missing30160_30162 : List (BitVec (edgeCount 12)) :=
  missing30160_30161 ++ missing30161_30162
abbrev records30160_30162 : List Blob :=
  records30160_30161 ++ records30161_30162
theorem aligned30160_30162 :
    AlignedValid 12 4 missing30160_30162 records30160_30162 :=
  aligned30160_30161.append aligned30161_30162

def missing30162_30163 : List (BitVec (edgeCount 12)) :=
  [missing30162]
abbrev records30162_30163 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30162]
theorem aligned30162_30163 :
    AlignedValid 12 4 missing30162_30163 records30162_30163 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30162
    maskCheck30162 AlignedValid.nil

def missing30163_30164 : List (BitVec (edgeCount 12)) :=
  [missing30163]
abbrev records30163_30164 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30163]
theorem aligned30163_30164 :
    AlignedValid 12 4 missing30163_30164 records30163_30164 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30163
    maskCheck30163 AlignedValid.nil

def missing30162_30164 : List (BitVec (edgeCount 12)) :=
  missing30162_30163 ++ missing30163_30164
abbrev records30162_30164 : List Blob :=
  records30162_30163 ++ records30163_30164
theorem aligned30162_30164 :
    AlignedValid 12 4 missing30162_30164 records30162_30164 :=
  aligned30162_30163.append aligned30163_30164

def missing30160_30164 : List (BitVec (edgeCount 12)) :=
  missing30160_30162 ++ missing30162_30164
abbrev records30160_30164 : List Blob :=
  records30160_30162 ++ records30162_30164
theorem aligned30160_30164 :
    AlignedValid 12 4 missing30160_30164 records30160_30164 :=
  aligned30160_30162.append aligned30162_30164

def missing30164_30165 : List (BitVec (edgeCount 12)) :=
  [missing30164]
abbrev records30164_30165 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30164]
theorem aligned30164_30165 :
    AlignedValid 12 4 missing30164_30165 records30164_30165 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30164
    maskCheck30164 AlignedValid.nil

def missing30165_30166 : List (BitVec (edgeCount 12)) :=
  [missing30165]
abbrev records30165_30166 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30165]
theorem aligned30165_30166 :
    AlignedValid 12 4 missing30165_30166 records30165_30166 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30165
    maskCheck30165 AlignedValid.nil

def missing30164_30166 : List (BitVec (edgeCount 12)) :=
  missing30164_30165 ++ missing30165_30166
abbrev records30164_30166 : List Blob :=
  records30164_30165 ++ records30165_30166
theorem aligned30164_30166 :
    AlignedValid 12 4 missing30164_30166 records30164_30166 :=
  aligned30164_30165.append aligned30165_30166

def missing30166_30167 : List (BitVec (edgeCount 12)) :=
  [missing30166]
abbrev records30166_30167 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30166]
theorem aligned30166_30167 :
    AlignedValid 12 4 missing30166_30167 records30166_30167 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30166
    maskCheck30166 AlignedValid.nil

def missing30167_30168 : List (BitVec (edgeCount 12)) :=
  [missing30167]
abbrev records30167_30168 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30167]
theorem aligned30167_30168 :
    AlignedValid 12 4 missing30167_30168 records30167_30168 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30167
    maskCheck30167 AlignedValid.nil

def missing30166_30168 : List (BitVec (edgeCount 12)) :=
  missing30166_30167 ++ missing30167_30168
abbrev records30166_30168 : List Blob :=
  records30166_30167 ++ records30167_30168
theorem aligned30166_30168 :
    AlignedValid 12 4 missing30166_30168 records30166_30168 :=
  aligned30166_30167.append aligned30167_30168

def missing30164_30168 : List (BitVec (edgeCount 12)) :=
  missing30164_30166 ++ missing30166_30168
abbrev records30164_30168 : List Blob :=
  records30164_30166 ++ records30166_30168
theorem aligned30164_30168 :
    AlignedValid 12 4 missing30164_30168 records30164_30168 :=
  aligned30164_30166.append aligned30166_30168

def missing30160_30168 : List (BitVec (edgeCount 12)) :=
  missing30160_30164 ++ missing30164_30168
abbrev records30160_30168 : List Blob :=
  records30160_30164 ++ records30164_30168
theorem aligned30160_30168 :
    AlignedValid 12 4 missing30160_30168 records30160_30168 :=
  aligned30160_30164.append aligned30164_30168

def missing30168_30169 : List (BitVec (edgeCount 12)) :=
  [missing30168]
abbrev records30168_30169 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30168]
theorem aligned30168_30169 :
    AlignedValid 12 4 missing30168_30169 records30168_30169 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30168
    maskCheck30168 AlignedValid.nil

def missing30169_30170 : List (BitVec (edgeCount 12)) :=
  [missing30169]
abbrev records30169_30170 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30169]
theorem aligned30169_30170 :
    AlignedValid 12 4 missing30169_30170 records30169_30170 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30169
    maskCheck30169 AlignedValid.nil

def missing30168_30170 : List (BitVec (edgeCount 12)) :=
  missing30168_30169 ++ missing30169_30170
abbrev records30168_30170 : List Blob :=
  records30168_30169 ++ records30169_30170
theorem aligned30168_30170 :
    AlignedValid 12 4 missing30168_30170 records30168_30170 :=
  aligned30168_30169.append aligned30169_30170

def missing30170_30171 : List (BitVec (edgeCount 12)) :=
  [missing30170]
abbrev records30170_30171 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30170]
theorem aligned30170_30171 :
    AlignedValid 12 4 missing30170_30171 records30170_30171 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30170
    maskCheck30170 AlignedValid.nil

def missing30171_30172 : List (BitVec (edgeCount 12)) :=
  [missing30171]
abbrev records30171_30172 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30171]
theorem aligned30171_30172 :
    AlignedValid 12 4 missing30171_30172 records30171_30172 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30171
    maskCheck30171 AlignedValid.nil

def missing30170_30172 : List (BitVec (edgeCount 12)) :=
  missing30170_30171 ++ missing30171_30172
abbrev records30170_30172 : List Blob :=
  records30170_30171 ++ records30171_30172
theorem aligned30170_30172 :
    AlignedValid 12 4 missing30170_30172 records30170_30172 :=
  aligned30170_30171.append aligned30171_30172

def missing30168_30172 : List (BitVec (edgeCount 12)) :=
  missing30168_30170 ++ missing30170_30172
abbrev records30168_30172 : List Blob :=
  records30168_30170 ++ records30170_30172
theorem aligned30168_30172 :
    AlignedValid 12 4 missing30168_30172 records30168_30172 :=
  aligned30168_30170.append aligned30170_30172

def missing30172_30173 : List (BitVec (edgeCount 12)) :=
  [missing30172]
abbrev records30172_30173 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30172]
theorem aligned30172_30173 :
    AlignedValid 12 4 missing30172_30173 records30172_30173 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30172
    maskCheck30172 AlignedValid.nil

def missing30173_30174 : List (BitVec (edgeCount 12)) :=
  [missing30173]
abbrev records30173_30174 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30173]
theorem aligned30173_30174 :
    AlignedValid 12 4 missing30173_30174 records30173_30174 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30173
    maskCheck30173 AlignedValid.nil

def missing30172_30174 : List (BitVec (edgeCount 12)) :=
  missing30172_30173 ++ missing30173_30174
abbrev records30172_30174 : List Blob :=
  records30172_30173 ++ records30173_30174
theorem aligned30172_30174 :
    AlignedValid 12 4 missing30172_30174 records30172_30174 :=
  aligned30172_30173.append aligned30173_30174

def missing30174_30175 : List (BitVec (edgeCount 12)) :=
  [missing30174]
abbrev records30174_30175 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30174]
theorem aligned30174_30175 :
    AlignedValid 12 4 missing30174_30175 records30174_30175 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30174
    maskCheck30174 AlignedValid.nil

def missing30175_30176 : List (BitVec (edgeCount 12)) :=
  [missing30175]
abbrev records30175_30176 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30175]
theorem aligned30175_30176 :
    AlignedValid 12 4 missing30175_30176 records30175_30176 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30175
    maskCheck30175 AlignedValid.nil

def missing30174_30176 : List (BitVec (edgeCount 12)) :=
  missing30174_30175 ++ missing30175_30176
abbrev records30174_30176 : List Blob :=
  records30174_30175 ++ records30175_30176
theorem aligned30174_30176 :
    AlignedValid 12 4 missing30174_30176 records30174_30176 :=
  aligned30174_30175.append aligned30175_30176

def missing30172_30176 : List (BitVec (edgeCount 12)) :=
  missing30172_30174 ++ missing30174_30176
abbrev records30172_30176 : List Blob :=
  records30172_30174 ++ records30174_30176
theorem aligned30172_30176 :
    AlignedValid 12 4 missing30172_30176 records30172_30176 :=
  aligned30172_30174.append aligned30174_30176

def missing30168_30176 : List (BitVec (edgeCount 12)) :=
  missing30168_30172 ++ missing30172_30176
abbrev records30168_30176 : List Blob :=
  records30168_30172 ++ records30172_30176
theorem aligned30168_30176 :
    AlignedValid 12 4 missing30168_30176 records30168_30176 :=
  aligned30168_30172.append aligned30172_30176

def missing30160_30176 : List (BitVec (edgeCount 12)) :=
  missing30160_30168 ++ missing30168_30176
abbrev records30160_30176 : List Blob :=
  records30160_30168 ++ records30168_30176
theorem aligned30160_30176 :
    AlignedValid 12 4 missing30160_30176 records30160_30176 :=
  aligned30160_30168.append aligned30168_30176

def missing30144_30176 : List (BitVec (edgeCount 12)) :=
  missing30144_30160 ++ missing30160_30176
abbrev records30144_30176 : List Blob :=
  records30144_30160 ++ records30160_30176
theorem aligned30144_30176 :
    AlignedValid 12 4 missing30144_30176 records30144_30176 :=
  aligned30144_30160.append aligned30160_30176

def missing30176_30177 : List (BitVec (edgeCount 12)) :=
  [missing30176]
abbrev records30176_30177 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30176]
theorem aligned30176_30177 :
    AlignedValid 12 4 missing30176_30177 records30176_30177 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30176
    maskCheck30176 AlignedValid.nil

def missing30177_30178 : List (BitVec (edgeCount 12)) :=
  [missing30177]
abbrev records30177_30178 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30177]
theorem aligned30177_30178 :
    AlignedValid 12 4 missing30177_30178 records30177_30178 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30177
    maskCheck30177 AlignedValid.nil

def missing30176_30178 : List (BitVec (edgeCount 12)) :=
  missing30176_30177 ++ missing30177_30178
abbrev records30176_30178 : List Blob :=
  records30176_30177 ++ records30177_30178
theorem aligned30176_30178 :
    AlignedValid 12 4 missing30176_30178 records30176_30178 :=
  aligned30176_30177.append aligned30177_30178

def missing30178_30179 : List (BitVec (edgeCount 12)) :=
  [missing30178]
abbrev records30178_30179 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30178]
theorem aligned30178_30179 :
    AlignedValid 12 4 missing30178_30179 records30178_30179 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30178
    maskCheck30178 AlignedValid.nil

def missing30179_30180 : List (BitVec (edgeCount 12)) :=
  [missing30179]
abbrev records30179_30180 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30179]
theorem aligned30179_30180 :
    AlignedValid 12 4 missing30179_30180 records30179_30180 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30179
    maskCheck30179 AlignedValid.nil

def missing30178_30180 : List (BitVec (edgeCount 12)) :=
  missing30178_30179 ++ missing30179_30180
abbrev records30178_30180 : List Blob :=
  records30178_30179 ++ records30179_30180
theorem aligned30178_30180 :
    AlignedValid 12 4 missing30178_30180 records30178_30180 :=
  aligned30178_30179.append aligned30179_30180

def missing30176_30180 : List (BitVec (edgeCount 12)) :=
  missing30176_30178 ++ missing30178_30180
abbrev records30176_30180 : List Blob :=
  records30176_30178 ++ records30178_30180
theorem aligned30176_30180 :
    AlignedValid 12 4 missing30176_30180 records30176_30180 :=
  aligned30176_30178.append aligned30178_30180

def missing30180_30181 : List (BitVec (edgeCount 12)) :=
  [missing30180]
abbrev records30180_30181 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30180]
theorem aligned30180_30181 :
    AlignedValid 12 4 missing30180_30181 records30180_30181 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30180
    maskCheck30180 AlignedValid.nil

def missing30181_30182 : List (BitVec (edgeCount 12)) :=
  [missing30181]
abbrev records30181_30182 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30181]
theorem aligned30181_30182 :
    AlignedValid 12 4 missing30181_30182 records30181_30182 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30181
    maskCheck30181 AlignedValid.nil

def missing30180_30182 : List (BitVec (edgeCount 12)) :=
  missing30180_30181 ++ missing30181_30182
abbrev records30180_30182 : List Blob :=
  records30180_30181 ++ records30181_30182
theorem aligned30180_30182 :
    AlignedValid 12 4 missing30180_30182 records30180_30182 :=
  aligned30180_30181.append aligned30181_30182

def missing30182_30183 : List (BitVec (edgeCount 12)) :=
  [missing30182]
abbrev records30182_30183 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30182]
theorem aligned30182_30183 :
    AlignedValid 12 4 missing30182_30183 records30182_30183 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30182
    maskCheck30182 AlignedValid.nil

def missing30183_30184 : List (BitVec (edgeCount 12)) :=
  [missing30183]
abbrev records30183_30184 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30183]
theorem aligned30183_30184 :
    AlignedValid 12 4 missing30183_30184 records30183_30184 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30183
    maskCheck30183 AlignedValid.nil

def missing30182_30184 : List (BitVec (edgeCount 12)) :=
  missing30182_30183 ++ missing30183_30184
abbrev records30182_30184 : List Blob :=
  records30182_30183 ++ records30183_30184
theorem aligned30182_30184 :
    AlignedValid 12 4 missing30182_30184 records30182_30184 :=
  aligned30182_30183.append aligned30183_30184

def missing30180_30184 : List (BitVec (edgeCount 12)) :=
  missing30180_30182 ++ missing30182_30184
abbrev records30180_30184 : List Blob :=
  records30180_30182 ++ records30182_30184
theorem aligned30180_30184 :
    AlignedValid 12 4 missing30180_30184 records30180_30184 :=
  aligned30180_30182.append aligned30182_30184

def missing30176_30184 : List (BitVec (edgeCount 12)) :=
  missing30176_30180 ++ missing30180_30184
abbrev records30176_30184 : List Blob :=
  records30176_30180 ++ records30180_30184
theorem aligned30176_30184 :
    AlignedValid 12 4 missing30176_30184 records30176_30184 :=
  aligned30176_30180.append aligned30180_30184

def missing30184_30185 : List (BitVec (edgeCount 12)) :=
  [missing30184]
abbrev records30184_30185 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30184]
theorem aligned30184_30185 :
    AlignedValid 12 4 missing30184_30185 records30184_30185 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30184
    maskCheck30184 AlignedValid.nil

def missing30185_30186 : List (BitVec (edgeCount 12)) :=
  [missing30185]
abbrev records30185_30186 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30185]
theorem aligned30185_30186 :
    AlignedValid 12 4 missing30185_30186 records30185_30186 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30185
    maskCheck30185 AlignedValid.nil

def missing30184_30186 : List (BitVec (edgeCount 12)) :=
  missing30184_30185 ++ missing30185_30186
abbrev records30184_30186 : List Blob :=
  records30184_30185 ++ records30185_30186
theorem aligned30184_30186 :
    AlignedValid 12 4 missing30184_30186 records30184_30186 :=
  aligned30184_30185.append aligned30185_30186

def missing30186_30187 : List (BitVec (edgeCount 12)) :=
  [missing30186]
abbrev records30186_30187 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30186]
theorem aligned30186_30187 :
    AlignedValid 12 4 missing30186_30187 records30186_30187 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30186
    maskCheck30186 AlignedValid.nil

def missing30187_30188 : List (BitVec (edgeCount 12)) :=
  [missing30187]
abbrev records30187_30188 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30187]
theorem aligned30187_30188 :
    AlignedValid 12 4 missing30187_30188 records30187_30188 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30187
    maskCheck30187 AlignedValid.nil

def missing30186_30188 : List (BitVec (edgeCount 12)) :=
  missing30186_30187 ++ missing30187_30188
abbrev records30186_30188 : List Blob :=
  records30186_30187 ++ records30187_30188
theorem aligned30186_30188 :
    AlignedValid 12 4 missing30186_30188 records30186_30188 :=
  aligned30186_30187.append aligned30187_30188

def missing30184_30188 : List (BitVec (edgeCount 12)) :=
  missing30184_30186 ++ missing30186_30188
abbrev records30184_30188 : List Blob :=
  records30184_30186 ++ records30186_30188
theorem aligned30184_30188 :
    AlignedValid 12 4 missing30184_30188 records30184_30188 :=
  aligned30184_30186.append aligned30186_30188

def missing30188_30189 : List (BitVec (edgeCount 12)) :=
  [missing30188]
abbrev records30188_30189 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30188]
theorem aligned30188_30189 :
    AlignedValid 12 4 missing30188_30189 records30188_30189 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30188
    maskCheck30188 AlignedValid.nil

def missing30189_30190 : List (BitVec (edgeCount 12)) :=
  [missing30189]
abbrev records30189_30190 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30189]
theorem aligned30189_30190 :
    AlignedValid 12 4 missing30189_30190 records30189_30190 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30189
    maskCheck30189 AlignedValid.nil

def missing30188_30190 : List (BitVec (edgeCount 12)) :=
  missing30188_30189 ++ missing30189_30190
abbrev records30188_30190 : List Blob :=
  records30188_30189 ++ records30189_30190
theorem aligned30188_30190 :
    AlignedValid 12 4 missing30188_30190 records30188_30190 :=
  aligned30188_30189.append aligned30189_30190

def missing30190_30191 : List (BitVec (edgeCount 12)) :=
  [missing30190]
abbrev records30190_30191 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30190]
theorem aligned30190_30191 :
    AlignedValid 12 4 missing30190_30191 records30190_30191 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30190
    maskCheck30190 AlignedValid.nil

def missing30191_30192 : List (BitVec (edgeCount 12)) :=
  [missing30191]
abbrev records30191_30192 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30191]
theorem aligned30191_30192 :
    AlignedValid 12 4 missing30191_30192 records30191_30192 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30191
    maskCheck30191 AlignedValid.nil

def missing30190_30192 : List (BitVec (edgeCount 12)) :=
  missing30190_30191 ++ missing30191_30192
abbrev records30190_30192 : List Blob :=
  records30190_30191 ++ records30191_30192
theorem aligned30190_30192 :
    AlignedValid 12 4 missing30190_30192 records30190_30192 :=
  aligned30190_30191.append aligned30191_30192

def missing30188_30192 : List (BitVec (edgeCount 12)) :=
  missing30188_30190 ++ missing30190_30192
abbrev records30188_30192 : List Blob :=
  records30188_30190 ++ records30190_30192
theorem aligned30188_30192 :
    AlignedValid 12 4 missing30188_30192 records30188_30192 :=
  aligned30188_30190.append aligned30190_30192

def missing30184_30192 : List (BitVec (edgeCount 12)) :=
  missing30184_30188 ++ missing30188_30192
abbrev records30184_30192 : List Blob :=
  records30184_30188 ++ records30188_30192
theorem aligned30184_30192 :
    AlignedValid 12 4 missing30184_30192 records30184_30192 :=
  aligned30184_30188.append aligned30188_30192

def missing30176_30192 : List (BitVec (edgeCount 12)) :=
  missing30176_30184 ++ missing30184_30192
abbrev records30176_30192 : List Blob :=
  records30176_30184 ++ records30184_30192
theorem aligned30176_30192 :
    AlignedValid 12 4 missing30176_30192 records30176_30192 :=
  aligned30176_30184.append aligned30184_30192

def missing30192_30193 : List (BitVec (edgeCount 12)) :=
  [missing30192]
abbrev records30192_30193 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30192]
theorem aligned30192_30193 :
    AlignedValid 12 4 missing30192_30193 records30192_30193 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30192
    maskCheck30192 AlignedValid.nil

def missing30193_30194 : List (BitVec (edgeCount 12)) :=
  [missing30193]
abbrev records30193_30194 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30193]
theorem aligned30193_30194 :
    AlignedValid 12 4 missing30193_30194 records30193_30194 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30193
    maskCheck30193 AlignedValid.nil

def missing30192_30194 : List (BitVec (edgeCount 12)) :=
  missing30192_30193 ++ missing30193_30194
abbrev records30192_30194 : List Blob :=
  records30192_30193 ++ records30193_30194
theorem aligned30192_30194 :
    AlignedValid 12 4 missing30192_30194 records30192_30194 :=
  aligned30192_30193.append aligned30193_30194

def missing30194_30195 : List (BitVec (edgeCount 12)) :=
  [missing30194]
abbrev records30194_30195 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30194]
theorem aligned30194_30195 :
    AlignedValid 12 4 missing30194_30195 records30194_30195 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30194
    maskCheck30194 AlignedValid.nil

def missing30195_30196 : List (BitVec (edgeCount 12)) :=
  [missing30195]
abbrev records30195_30196 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30195]
theorem aligned30195_30196 :
    AlignedValid 12 4 missing30195_30196 records30195_30196 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30195
    maskCheck30195 AlignedValid.nil

def missing30194_30196 : List (BitVec (edgeCount 12)) :=
  missing30194_30195 ++ missing30195_30196
abbrev records30194_30196 : List Blob :=
  records30194_30195 ++ records30195_30196
theorem aligned30194_30196 :
    AlignedValid 12 4 missing30194_30196 records30194_30196 :=
  aligned30194_30195.append aligned30195_30196

def missing30192_30196 : List (BitVec (edgeCount 12)) :=
  missing30192_30194 ++ missing30194_30196
abbrev records30192_30196 : List Blob :=
  records30192_30194 ++ records30194_30196
theorem aligned30192_30196 :
    AlignedValid 12 4 missing30192_30196 records30192_30196 :=
  aligned30192_30194.append aligned30194_30196

def missing30196_30197 : List (BitVec (edgeCount 12)) :=
  [missing30196]
abbrev records30196_30197 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30196]
theorem aligned30196_30197 :
    AlignedValid 12 4 missing30196_30197 records30196_30197 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30196
    maskCheck30196 AlignedValid.nil

def missing30197_30198 : List (BitVec (edgeCount 12)) :=
  [missing30197]
abbrev records30197_30198 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30197]
theorem aligned30197_30198 :
    AlignedValid 12 4 missing30197_30198 records30197_30198 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30197
    maskCheck30197 AlignedValid.nil

def missing30196_30198 : List (BitVec (edgeCount 12)) :=
  missing30196_30197 ++ missing30197_30198
abbrev records30196_30198 : List Blob :=
  records30196_30197 ++ records30197_30198
theorem aligned30196_30198 :
    AlignedValid 12 4 missing30196_30198 records30196_30198 :=
  aligned30196_30197.append aligned30197_30198

def missing30198_30199 : List (BitVec (edgeCount 12)) :=
  [missing30198]
abbrev records30198_30199 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30198]
theorem aligned30198_30199 :
    AlignedValid 12 4 missing30198_30199 records30198_30199 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30198
    maskCheck30198 AlignedValid.nil

def missing30199_30200 : List (BitVec (edgeCount 12)) :=
  [missing30199]
abbrev records30199_30200 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30199]
theorem aligned30199_30200 :
    AlignedValid 12 4 missing30199_30200 records30199_30200 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30199
    maskCheck30199 AlignedValid.nil

def missing30198_30200 : List (BitVec (edgeCount 12)) :=
  missing30198_30199 ++ missing30199_30200
abbrev records30198_30200 : List Blob :=
  records30198_30199 ++ records30199_30200
theorem aligned30198_30200 :
    AlignedValid 12 4 missing30198_30200 records30198_30200 :=
  aligned30198_30199.append aligned30199_30200

def missing30196_30200 : List (BitVec (edgeCount 12)) :=
  missing30196_30198 ++ missing30198_30200
abbrev records30196_30200 : List Blob :=
  records30196_30198 ++ records30198_30200
theorem aligned30196_30200 :
    AlignedValid 12 4 missing30196_30200 records30196_30200 :=
  aligned30196_30198.append aligned30198_30200

def missing30192_30200 : List (BitVec (edgeCount 12)) :=
  missing30192_30196 ++ missing30196_30200
abbrev records30192_30200 : List Blob :=
  records30192_30196 ++ records30196_30200
theorem aligned30192_30200 :
    AlignedValid 12 4 missing30192_30200 records30192_30200 :=
  aligned30192_30196.append aligned30196_30200

def missing30200_30201 : List (BitVec (edgeCount 12)) :=
  [missing30200]
abbrev records30200_30201 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30200]
theorem aligned30200_30201 :
    AlignedValid 12 4 missing30200_30201 records30200_30201 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30200
    maskCheck30200 AlignedValid.nil

def missing30201_30202 : List (BitVec (edgeCount 12)) :=
  [missing30201]
abbrev records30201_30202 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30201]
theorem aligned30201_30202 :
    AlignedValid 12 4 missing30201_30202 records30201_30202 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30201
    maskCheck30201 AlignedValid.nil

def missing30200_30202 : List (BitVec (edgeCount 12)) :=
  missing30200_30201 ++ missing30201_30202
abbrev records30200_30202 : List Blob :=
  records30200_30201 ++ records30201_30202
theorem aligned30200_30202 :
    AlignedValid 12 4 missing30200_30202 records30200_30202 :=
  aligned30200_30201.append aligned30201_30202

def missing30202_30203 : List (BitVec (edgeCount 12)) :=
  [missing30202]
abbrev records30202_30203 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30202]
theorem aligned30202_30203 :
    AlignedValid 12 4 missing30202_30203 records30202_30203 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30202
    maskCheck30202 AlignedValid.nil

def missing30203_30204 : List (BitVec (edgeCount 12)) :=
  [missing30203]
abbrev records30203_30204 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30203]
theorem aligned30203_30204 :
    AlignedValid 12 4 missing30203_30204 records30203_30204 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30203
    maskCheck30203 AlignedValid.nil

def missing30202_30204 : List (BitVec (edgeCount 12)) :=
  missing30202_30203 ++ missing30203_30204
abbrev records30202_30204 : List Blob :=
  records30202_30203 ++ records30203_30204
theorem aligned30202_30204 :
    AlignedValid 12 4 missing30202_30204 records30202_30204 :=
  aligned30202_30203.append aligned30203_30204

def missing30200_30204 : List (BitVec (edgeCount 12)) :=
  missing30200_30202 ++ missing30202_30204
abbrev records30200_30204 : List Blob :=
  records30200_30202 ++ records30202_30204
theorem aligned30200_30204 :
    AlignedValid 12 4 missing30200_30204 records30200_30204 :=
  aligned30200_30202.append aligned30202_30204

def missing30204_30205 : List (BitVec (edgeCount 12)) :=
  [missing30204]
abbrev records30204_30205 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30204]
theorem aligned30204_30205 :
    AlignedValid 12 4 missing30204_30205 records30204_30205 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30204
    maskCheck30204 AlignedValid.nil

def missing30205_30206 : List (BitVec (edgeCount 12)) :=
  [missing30205]
abbrev records30205_30206 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30205]
theorem aligned30205_30206 :
    AlignedValid 12 4 missing30205_30206 records30205_30206 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30205
    maskCheck30205 AlignedValid.nil

def missing30204_30206 : List (BitVec (edgeCount 12)) :=
  missing30204_30205 ++ missing30205_30206
abbrev records30204_30206 : List Blob :=
  records30204_30205 ++ records30205_30206
theorem aligned30204_30206 :
    AlignedValid 12 4 missing30204_30206 records30204_30206 :=
  aligned30204_30205.append aligned30205_30206

def missing30206_30207 : List (BitVec (edgeCount 12)) :=
  [missing30206]
abbrev records30206_30207 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30206]
theorem aligned30206_30207 :
    AlignedValid 12 4 missing30206_30207 records30206_30207 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30206
    maskCheck30206 AlignedValid.nil

def missing30207_30208 : List (BitVec (edgeCount 12)) :=
  [missing30207]
abbrev records30207_30208 : List Blob :=
  [StrongPackedBucketN12A4Shard235.record30207]
theorem aligned30207_30208 :
    AlignedValid 12 4 missing30207_30208 records30207_30208 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard235.check30207
    maskCheck30207 AlignedValid.nil

def missing30206_30208 : List (BitVec (edgeCount 12)) :=
  missing30206_30207 ++ missing30207_30208
abbrev records30206_30208 : List Blob :=
  records30206_30207 ++ records30207_30208
theorem aligned30206_30208 :
    AlignedValid 12 4 missing30206_30208 records30206_30208 :=
  aligned30206_30207.append aligned30207_30208

def missing30204_30208 : List (BitVec (edgeCount 12)) :=
  missing30204_30206 ++ missing30206_30208
abbrev records30204_30208 : List Blob :=
  records30204_30206 ++ records30206_30208
theorem aligned30204_30208 :
    AlignedValid 12 4 missing30204_30208 records30204_30208 :=
  aligned30204_30206.append aligned30206_30208

def missing30200_30208 : List (BitVec (edgeCount 12)) :=
  missing30200_30204 ++ missing30204_30208
abbrev records30200_30208 : List Blob :=
  records30200_30204 ++ records30204_30208
theorem aligned30200_30208 :
    AlignedValid 12 4 missing30200_30208 records30200_30208 :=
  aligned30200_30204.append aligned30204_30208

def missing30192_30208 : List (BitVec (edgeCount 12)) :=
  missing30192_30200 ++ missing30200_30208
abbrev records30192_30208 : List Blob :=
  records30192_30200 ++ records30200_30208
theorem aligned30192_30208 :
    AlignedValid 12 4 missing30192_30208 records30192_30208 :=
  aligned30192_30200.append aligned30200_30208

def missing30176_30208 : List (BitVec (edgeCount 12)) :=
  missing30176_30192 ++ missing30192_30208
abbrev records30176_30208 : List Blob :=
  records30176_30192 ++ records30192_30208
theorem aligned30176_30208 :
    AlignedValid 12 4 missing30176_30208 records30176_30208 :=
  aligned30176_30192.append aligned30192_30208

def missing30144_30208 : List (BitVec (edgeCount 12)) :=
  missing30144_30176 ++ missing30176_30208
abbrev records30144_30208 : List Blob :=
  records30144_30176 ++ records30176_30208
theorem aligned30144_30208 :
    AlignedValid 12 4 missing30144_30208 records30144_30208 :=
  aligned30144_30176.append aligned30176_30208

def missing30080_30208 : List (BitVec (edgeCount 12)) :=
  missing30080_30144 ++ missing30144_30208
abbrev records30080_30208 : List Blob :=
  records30080_30144 ++ records30144_30208
theorem aligned30080_30208 :
    AlignedValid 12 4 missing30080_30208 records30080_30208 :=
  aligned30080_30144.append aligned30144_30208

abbrev missing : List (BitVec (edgeCount 12)) := missing30080_30208
abbrev records : List Blob := records30080_30208
theorem aligned : AlignedValid 12 4 missing records := aligned30080_30208

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard235
