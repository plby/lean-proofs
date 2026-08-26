/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Shard032

/-! Decode-only alignment checks for n=12, a=2, records 4096--4190. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A2AlignedShard032

open PackedBucketCertificate

def missing4096 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 937105034057908224
theorem maskCheck4096 :
    checkMaskFor missing4096 StrongPackedBucketN12A2Shard032.record4096 = true := by
  decide

def missing4097 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1009162628095836160
theorem maskCheck4097 :
    checkMaskFor missing4097 StrongPackedBucketN12A2Shard032.record4097 = true := by
  decide

def missing4098 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1873853756550971392
theorem maskCheck4098 :
    checkMaskFor missing4098 StrongPackedBucketN12A2Shard032.record4098 = true := by
  decide

def missing4099 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2017968944626827264
theorem maskCheck4099 :
    checkMaskFor missing4099 StrongPackedBucketN12A2Shard032.record4099 = true := by
  decide

def missing4100 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2414285711835430912
theorem maskCheck4100 :
    checkMaskFor missing4100 StrongPackedBucketN12A2Shard032.record4100 = true := by
  decide

def missing4101 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2486343305873358848
theorem maskCheck4101 :
    checkMaskFor missing4101 StrongPackedBucketN12A2Shard032.record4101 = true := by
  decide

def missing4102 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2630458493949214720
theorem maskCheck4102 :
    checkMaskFor missing4102 StrongPackedBucketN12A2Shard032.record4102 = true := by
  decide

def missing4103 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4720128721049124864
theorem maskCheck4103 :
    checkMaskFor missing4103 StrongPackedBucketN12A2Shard032.record4103 = true := by
  decide

def missing4104 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4828215112106016768
theorem maskCheck4104 :
    checkMaskFor missing4104 StrongPackedBucketN12A2Shard032.record4104 = true := by
  decide

def missing4105 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4972330300181872640
theorem maskCheck4105 :
    checkMaskFor missing4105 StrongPackedBucketN12A2Shard032.record4105 = true := by
  decide

def missing4106 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5044387894219800576
theorem maskCheck4106 :
    checkMaskFor missing4106 StrongPackedBucketN12A2Shard032.record4106 = true := by
  decide

def missing4107 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5476733458447368192
theorem maskCheck4107 :
    checkMaskFor missing4107 StrongPackedBucketN12A2Shard032.record4107 = true := by
  decide

def missing4108 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9403872333514440704
theorem maskCheck4108 :
    checkMaskFor missing4108 StrongPackedBucketN12A2Shard032.record4108 = true := by
  decide

def missing4109 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9439901130533404672
theorem maskCheck4109 :
    checkMaskFor missing4109 StrongPackedBucketN12A2Shard032.record4109 = true := by
  decide

def missing4110 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9656073912647188480
theorem maskCheck4110 :
    checkMaskFor missing4110 StrongPackedBucketN12A2Shard032.record4110 = true := by
  decide

def missing4111 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9944304288798900224
theorem maskCheck4111 :
    checkMaskFor missing4111 StrongPackedBucketN12A2Shard032.record4111 = true := by
  decide

def missing4112 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20788972191507054592
theorem maskCheck4112 :
    checkMaskFor missing4112 StrongPackedBucketN12A2Shard032.record4112 = true := by
  decide

def missing4113 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37001930850040840192
theorem maskCheck4113 :
    checkMaskFor missing4113 StrongPackedBucketN12A2Shard032.record4113 = true := by
  decide

def missing4114 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37110017241097732096
theorem maskCheck4114 :
    checkMaskFor missing4114 StrongPackedBucketN12A2Shard032.record4114 = true := by
  decide

def missing4115 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37254132429173587968
theorem maskCheck4115 :
    checkMaskFor missing4115 StrongPackedBucketN12A2Shard032.record4115 = true := by
  decide

def missing4116 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37542362805325299712
theorem maskCheck4116 :
    checkMaskFor missing4116 StrongPackedBucketN12A2Shard032.record4116 = true := by
  decide

def missing4117 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 505252051039584256
theorem maskCheck4117 :
    checkMaskFor missing4117 StrongPackedBucketN12A2Shard032.record4117 = true := by
  decide

def missing4118 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 937597615267151872
theorem maskCheck4118 :
    checkMaskFor missing4118 StrongPackedBucketN12A2Shard032.record4118 = true := by
  decide

def missing4119 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1369943179494719488
theorem maskCheck4119 :
    checkMaskFor missing4119 StrongPackedBucketN12A2Shard032.record4119 = true := by
  decide

def missing4120 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1514058367570575360
theorem maskCheck4120 :
    checkMaskFor missing4120 StrongPackedBucketN12A2Shard032.record4120 = true := by
  decide

def missing4121 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2018461525836070912
theorem maskCheck4121 :
    checkMaskFor missing4121 StrongPackedBucketN12A2Shard032.record4121 = true := by
  decide

def missing4122 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2414778293044674560
theorem maskCheck4122 :
    checkMaskFor missing4122 StrongPackedBucketN12A2Shard032.record4122 = true := by
  decide

def missing4123 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2630951075158458368
theorem maskCheck4123 :
    checkMaskFor missing4123 StrongPackedBucketN12A2Shard032.record4123 = true := by
  decide

def missing4124 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3495642203613593600
theorem maskCheck4124 :
    checkMaskFor missing4124 StrongPackedBucketN12A2Shard032.record4124 = true := by
  decide

def missing4125 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4720621302258368512
theorem maskCheck4125 :
    checkMaskFor missing4125 StrongPackedBucketN12A2Shard032.record4125 = true := by
  decide

def missing4126 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4828707693315260416
theorem maskCheck4126 :
    checkMaskFor missing4126 StrongPackedBucketN12A2Shard032.record4126 = true := by
  decide

def missing4127 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4972822881391116288
theorem maskCheck4127 :
    checkMaskFor missing4127 StrongPackedBucketN12A2Shard032.record4127 = true := by
  decide

def missing4128 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5837514009846251520
theorem maskCheck4128 :
    checkMaskFor missing4128 StrongPackedBucketN12A2Shard032.record4128 = true := by
  decide

def missing4129 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20789464772716298240
theorem maskCheck4129 :
    checkMaskFor missing4129 StrongPackedBucketN12A2Shard032.record4129 = true := by
  decide

def missing4130 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37002423431250083840
theorem maskCheck4130 :
    checkMaskFor missing4130 StrongPackedBucketN12A2Shard032.record4130 = true := by
  decide

def missing4131 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37110509822306975744
theorem maskCheck4131 :
    checkMaskFor missing4131 StrongPackedBucketN12A2Shard032.record4131 = true := by
  decide

def missing4132 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37218596213363867648
theorem maskCheck4132 :
    checkMaskFor missing4132 StrongPackedBucketN12A2Shard032.record4132 = true := by
  decide

def missing4133 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37254625010382831616
theorem maskCheck4133 :
    checkMaskFor missing4133 StrongPackedBucketN12A2Shard032.record4133 = true := by
  decide

def missing4134 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37759028168648327168
theorem maskCheck4134 :
    checkMaskFor missing4134 StrongPackedBucketN12A2Shard032.record4134 = true := by
  decide

def missing4135 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38083287341819002880
theorem maskCheck4135 :
    checkMaskFor missing4135 StrongPackedBucketN12A2Shard032.record4135 = true := by
  decide

def missing4136 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38119316138837966848
theorem maskCheck4136 :
    checkMaskFor missing4136 StrongPackedBucketN12A2Shard032.record4136 = true := by
  decide

def missing4137 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38335488920951750656
theorem maskCheck4137 :
    checkMaskFor missing4137 StrongPackedBucketN12A2Shard032.record4137 = true := by
  decide

def missing4138 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39236208846425849856
theorem maskCheck4138 :
    checkMaskFor missing4138 StrongPackedBucketN12A2Shard032.record4138 = true := by
  decide

def missing4139 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41578080652658507776
theorem maskCheck4139 :
    checkMaskFor missing4139 StrongPackedBucketN12A2Shard032.record4139 = true := by
  decide

def missing4140 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 256780015348252672
theorem maskCheck4140 :
    checkMaskFor missing4140 StrongPackedBucketN12A2Shard032.record4140 = true := by
  decide

def missing4141 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 400895203424108544
theorem maskCheck4141 :
    checkMaskFor missing4141 StrongPackedBucketN12A2Shard032.record4141 = true := by
  decide

def missing4142 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1013384752746496000
theorem maskCheck4142 :
    checkMaskFor missing4142 StrongPackedBucketN12A2Shard032.record4142 = true := by
  decide

def missing4143 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2022191069277487104
theorem maskCheck4143 :
    checkMaskFor missing4143 StrongPackedBucketN12A2Shard032.record4143 = true := by
  decide

def missing4144 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2418507836486090752
theorem maskCheck4144 :
    checkMaskFor missing4144 StrongPackedBucketN12A2Shard032.record4144 = true := by
  decide

def missing4145 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2490565430524018688
theorem maskCheck4145 :
    checkMaskFor missing4145 StrongPackedBucketN12A2Shard032.record4145 = true := by
  decide

def missing4146 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9408094458165100544
theorem maskCheck4146 :
    checkMaskFor missing4146 StrongPackedBucketN12A2Shard032.record4146 = true := by
  decide

def missing4147 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9660296037297848320
theorem maskCheck4147 :
    checkMaskFor missing4147 StrongPackedBucketN12A2Shard032.record4147 = true := by
  decide

def missing4148 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20793194316157714432
theorem maskCheck4148 :
    checkMaskFor missing4148 StrongPackedBucketN12A2Shard032.record4148 = true := by
  decide

def missing4149 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2883008137500065792
theorem maskCheck4149 :
    checkMaskFor missing4149 StrongPackedBucketN12A2Shard032.record4149 = true := by
  decide

def missing4150 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1731071795311706112
theorem maskCheck4150 :
    checkMaskFor missing4150 StrongPackedBucketN12A2Shard032.record4150 = true := by
  decide

def missing4151 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2451647735690985472
theorem maskCheck4151 :
    checkMaskFor missing4151 StrongPackedBucketN12A2Shard032.record4151 = true := by
  decide

def missing4152 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 649363597251608576
theorem maskCheck4152 :
    checkMaskFor missing4152 StrongPackedBucketN12A2Shard032.record4152 = true := by
  decide

def missing4153 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2883149012427374592
theorem maskCheck4153 :
    checkMaskFor missing4153 StrongPackedBucketN12A2Shard032.record4153 = true := by
  decide

def missing4154 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 361977646030028800
theorem maskCheck4154 :
    checkMaskFor missing4154 StrongPackedBucketN12A2Shard032.record4154 = true := by
  decide

def missing4155 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 650208022181740544
theorem maskCheck4155 :
    checkMaskFor missing4155 StrongPackedBucketN12A2Shard032.record4155 = true := by
  decide

def missing4156 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2595763061205794816
theorem maskCheck4156 :
    checkMaskFor missing4156 StrongPackedBucketN12A2Shard032.record4156 = true := by
  decide

def missing4157 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4900272912570810368
theorem maskCheck4157 :
    checkMaskFor missing4157 StrongPackedBucketN12A2Shard032.record4157 = true := by
  decide

def missing4158 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 361137069390594048
theorem maskCheck4158 :
    checkMaskFor missing4158 StrongPackedBucketN12A2Shard032.record4158 = true := by
  decide

def missing4159 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 865540227656089600
theorem maskCheck4159 :
    checkMaskFor missing4159 StrongPackedBucketN12A2Shard032.record4159 = true := by
  decide

def missing4160 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 649117308526034944
theorem maskCheck4160 :
    checkMaskFor missing4160 StrongPackedBucketN12A2Shard032.record4160 = true := by
  decide

def missing4161 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 109776068776329216
theorem maskCheck4161 :
    checkMaskFor missing4161 StrongPackedBucketN12A2Shard032.record4161 = true := by
  decide

def missing4162 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 614179227041824768
theorem maskCheck4162 :
    checkMaskFor missing4162 StrongPackedBucketN12A2Shard032.record4162 = true := by
  decide

def missing4163 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1731071934629707776
theorem maskCheck4163 :
    checkMaskFor missing4163 StrongPackedBucketN12A2Shard032.record4163 = true := by
  decide

def missing4164 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 108932193602011136
theorem maskCheck4164 :
    checkMaskFor missing4164 StrongPackedBucketN12A2Shard032.record4164 = true := by
  decide

def missing4165 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 361450432083558400
theorem maskCheck4165 :
    checkMaskFor missing4165 StrongPackedBucketN12A2Shard032.record4165 = true := by
  decide

def missing4166 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 865853590349053952
theorem maskCheck4166 :
    checkMaskFor missing4166 StrongPackedBucketN12A2Shard032.record4166 = true := by
  decide

def missing4167 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 109495143555432448
theorem maskCheck4167 :
    checkMaskFor missing4167 StrongPackedBucketN12A2Shard032.record4167 = true := by
  decide

def missing4168 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 613898301820928000
theorem maskCheck4168 :
    checkMaskFor missing4168 StrongPackedBucketN12A2Shard032.record4168 = true := by
  decide

def missing4169 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1730791009408811008
theorem maskCheck4169 :
    checkMaskFor missing4169 StrongPackedBucketN12A2Shard032.record4169 = true := by
  decide

def missing4170 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4900339036813557760
theorem maskCheck4170 :
    checkMaskFor missing4170 StrongPackedBucketN12A2Shard032.record4170 = true := by
  decide

def missing4171 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 865535983154659328
theorem maskCheck4171 :
    checkMaskFor missing4171 StrongPackedBucketN12A2Shard032.record4171 = true := by
  decide

def missing4172 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4756646061202767872
theorem maskCheck4172 :
    checkMaskFor missing4172 StrongPackedBucketN12A2Shard032.record4172 = true := by
  decide

def missing4173 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 360992499717668864
theorem maskCheck4173 :
    checkMaskFor missing4173 StrongPackedBucketN12A2Shard032.record4173 = true := by
  decide

def missing4174 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 865395657983164416
theorem maskCheck4174 :
    checkMaskFor missing4174 StrongPackedBucketN12A2Shard032.record4174 = true := by
  decide

def missing4175 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 217862474060300288
theorem maskCheck4175 :
    checkMaskFor missing4175 StrongPackedBucketN12A2Shard032.record4175 = true := by
  decide

def missing4176 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 434035256174084096
theorem maskCheck4176 :
    checkMaskFor missing4176 StrongPackedBucketN12A2Shard032.record4176 = true := by
  decide

def missing4177 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4685433304411832320
theorem maskCheck4177 :
    checkMaskFor missing4177 StrongPackedBucketN12A2Shard032.record4177 = true := by
  decide

def missing4178 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 432776727677140992
theorem maskCheck4178 :
    checkMaskFor missing4178 StrongPackedBucketN12A2Shard032.record4178 = true := by
  decide

def missing4179 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 505565344211993600
theorem maskCheck4179 :
    checkMaskFor missing4179 StrongPackedBucketN12A2Shard032.record4179 = true := by
  decide

def missing4180 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1262170081610236928
theorem maskCheck4180 :
    checkMaskFor missing4180 StrongPackedBucketN12A2Shard032.record4180 = true := by
  decide

def missing4181 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2415091586217083904
theorem maskCheck4181 :
    checkMaskFor missing4181 StrongPackedBucketN12A2Shard032.record4181 = true := by
  decide

def missing4182 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2523177977273975808
theorem maskCheck4182 :
    checkMaskFor missing4182 StrongPackedBucketN12A2Shard032.record4182 = true := by
  decide

def missing4183 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38083600634991412224
theorem maskCheck4183 :
    checkMaskFor missing4183 StrongPackedBucketN12A2Shard032.record4183 = true := by
  decide

def missing4184 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 217862802361091072
theorem maskCheck4184 :
    checkMaskFor missing4184 StrongPackedBucketN12A2Shard032.record4184 = true := by
  decide

def missing4185 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 432981152823837696
theorem maskCheck4185 :
    checkMaskFor missing4185 StrongPackedBucketN12A2Shard032.record4185 = true := by
  decide

def missing4186 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 721211528975549440
theorem maskCheck4186 :
    checkMaskFor missing4186 StrongPackedBucketN12A2Shard032.record4186 = true := by
  decide

def missing4187 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2882939350113387520
theorem maskCheck4187 :
    checkMaskFor missing4187 StrongPackedBucketN12A2Shard032.record4187 = true := by
  decide

def missing4188 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4756436795099513856
theorem maskCheck4188 :
    checkMaskFor missing4188 StrongPackedBucketN12A2Shard032.record4188 = true := by
  decide

def missing4189 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 434670002684101632
theorem maskCheck4189 :
    checkMaskFor missing4189 StrongPackedBucketN12A2Shard032.record4189 = true := by
  decide

def missing4190 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4758125644959777792
theorem maskCheck4190 :
    checkMaskFor missing4190 StrongPackedBucketN12A2Shard032.record4190 = true := by
  decide

def missing4096_4097 : List (BitVec (edgeCount 12)) :=
  [missing4096]
abbrev records4096_4097 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4096]
theorem aligned4096_4097 :
    AlignedValid 12 2 missing4096_4097 records4096_4097 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4096
    maskCheck4096 AlignedValid.nil

def missing4097_4098 : List (BitVec (edgeCount 12)) :=
  [missing4097]
abbrev records4097_4098 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4097]
theorem aligned4097_4098 :
    AlignedValid 12 2 missing4097_4098 records4097_4098 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4097
    maskCheck4097 AlignedValid.nil

def missing4096_4098 : List (BitVec (edgeCount 12)) :=
  missing4096_4097 ++ missing4097_4098
abbrev records4096_4098 : List Blob :=
  records4096_4097 ++ records4097_4098
theorem aligned4096_4098 :
    AlignedValid 12 2 missing4096_4098 records4096_4098 :=
  aligned4096_4097.append aligned4097_4098

def missing4098_4099 : List (BitVec (edgeCount 12)) :=
  [missing4098]
abbrev records4098_4099 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4098]
theorem aligned4098_4099 :
    AlignedValid 12 2 missing4098_4099 records4098_4099 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4098
    maskCheck4098 AlignedValid.nil

def missing4099_4100 : List (BitVec (edgeCount 12)) :=
  [missing4099]
abbrev records4099_4100 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4099]
theorem aligned4099_4100 :
    AlignedValid 12 2 missing4099_4100 records4099_4100 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4099
    maskCheck4099 AlignedValid.nil

def missing4100_4101 : List (BitVec (edgeCount 12)) :=
  [missing4100]
abbrev records4100_4101 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4100]
theorem aligned4100_4101 :
    AlignedValid 12 2 missing4100_4101 records4100_4101 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4100
    maskCheck4100 AlignedValid.nil

def missing4099_4101 : List (BitVec (edgeCount 12)) :=
  missing4099_4100 ++ missing4100_4101
abbrev records4099_4101 : List Blob :=
  records4099_4100 ++ records4100_4101
theorem aligned4099_4101 :
    AlignedValid 12 2 missing4099_4101 records4099_4101 :=
  aligned4099_4100.append aligned4100_4101

def missing4098_4101 : List (BitVec (edgeCount 12)) :=
  missing4098_4099 ++ missing4099_4101
abbrev records4098_4101 : List Blob :=
  records4098_4099 ++ records4099_4101
theorem aligned4098_4101 :
    AlignedValid 12 2 missing4098_4101 records4098_4101 :=
  aligned4098_4099.append aligned4099_4101

def missing4096_4101 : List (BitVec (edgeCount 12)) :=
  missing4096_4098 ++ missing4098_4101
abbrev records4096_4101 : List Blob :=
  records4096_4098 ++ records4098_4101
theorem aligned4096_4101 :
    AlignedValid 12 2 missing4096_4101 records4096_4101 :=
  aligned4096_4098.append aligned4098_4101

def missing4101_4102 : List (BitVec (edgeCount 12)) :=
  [missing4101]
abbrev records4101_4102 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4101]
theorem aligned4101_4102 :
    AlignedValid 12 2 missing4101_4102 records4101_4102 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4101
    maskCheck4101 AlignedValid.nil

def missing4102_4103 : List (BitVec (edgeCount 12)) :=
  [missing4102]
abbrev records4102_4103 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4102]
theorem aligned4102_4103 :
    AlignedValid 12 2 missing4102_4103 records4102_4103 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4102
    maskCheck4102 AlignedValid.nil

def missing4103_4104 : List (BitVec (edgeCount 12)) :=
  [missing4103]
abbrev records4103_4104 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4103]
theorem aligned4103_4104 :
    AlignedValid 12 2 missing4103_4104 records4103_4104 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4103
    maskCheck4103 AlignedValid.nil

def missing4102_4104 : List (BitVec (edgeCount 12)) :=
  missing4102_4103 ++ missing4103_4104
abbrev records4102_4104 : List Blob :=
  records4102_4103 ++ records4103_4104
theorem aligned4102_4104 :
    AlignedValid 12 2 missing4102_4104 records4102_4104 :=
  aligned4102_4103.append aligned4103_4104

def missing4101_4104 : List (BitVec (edgeCount 12)) :=
  missing4101_4102 ++ missing4102_4104
abbrev records4101_4104 : List Blob :=
  records4101_4102 ++ records4102_4104
theorem aligned4101_4104 :
    AlignedValid 12 2 missing4101_4104 records4101_4104 :=
  aligned4101_4102.append aligned4102_4104

def missing4104_4105 : List (BitVec (edgeCount 12)) :=
  [missing4104]
abbrev records4104_4105 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4104]
theorem aligned4104_4105 :
    AlignedValid 12 2 missing4104_4105 records4104_4105 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4104
    maskCheck4104 AlignedValid.nil

def missing4105_4106 : List (BitVec (edgeCount 12)) :=
  [missing4105]
abbrev records4105_4106 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4105]
theorem aligned4105_4106 :
    AlignedValid 12 2 missing4105_4106 records4105_4106 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4105
    maskCheck4105 AlignedValid.nil

def missing4106_4107 : List (BitVec (edgeCount 12)) :=
  [missing4106]
abbrev records4106_4107 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4106]
theorem aligned4106_4107 :
    AlignedValid 12 2 missing4106_4107 records4106_4107 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4106
    maskCheck4106 AlignedValid.nil

def missing4105_4107 : List (BitVec (edgeCount 12)) :=
  missing4105_4106 ++ missing4106_4107
abbrev records4105_4107 : List Blob :=
  records4105_4106 ++ records4106_4107
theorem aligned4105_4107 :
    AlignedValid 12 2 missing4105_4107 records4105_4107 :=
  aligned4105_4106.append aligned4106_4107

def missing4104_4107 : List (BitVec (edgeCount 12)) :=
  missing4104_4105 ++ missing4105_4107
abbrev records4104_4107 : List Blob :=
  records4104_4105 ++ records4105_4107
theorem aligned4104_4107 :
    AlignedValid 12 2 missing4104_4107 records4104_4107 :=
  aligned4104_4105.append aligned4105_4107

def missing4101_4107 : List (BitVec (edgeCount 12)) :=
  missing4101_4104 ++ missing4104_4107
abbrev records4101_4107 : List Blob :=
  records4101_4104 ++ records4104_4107
theorem aligned4101_4107 :
    AlignedValid 12 2 missing4101_4107 records4101_4107 :=
  aligned4101_4104.append aligned4104_4107

def missing4096_4107 : List (BitVec (edgeCount 12)) :=
  missing4096_4101 ++ missing4101_4107
abbrev records4096_4107 : List Blob :=
  records4096_4101 ++ records4101_4107
theorem aligned4096_4107 :
    AlignedValid 12 2 missing4096_4107 records4096_4107 :=
  aligned4096_4101.append aligned4101_4107

def missing4107_4108 : List (BitVec (edgeCount 12)) :=
  [missing4107]
abbrev records4107_4108 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4107]
theorem aligned4107_4108 :
    AlignedValid 12 2 missing4107_4108 records4107_4108 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4107
    maskCheck4107 AlignedValid.nil

def missing4108_4109 : List (BitVec (edgeCount 12)) :=
  [missing4108]
abbrev records4108_4109 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4108]
theorem aligned4108_4109 :
    AlignedValid 12 2 missing4108_4109 records4108_4109 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4108
    maskCheck4108 AlignedValid.nil

def missing4109_4110 : List (BitVec (edgeCount 12)) :=
  [missing4109]
abbrev records4109_4110 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4109]
theorem aligned4109_4110 :
    AlignedValid 12 2 missing4109_4110 records4109_4110 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4109
    maskCheck4109 AlignedValid.nil

def missing4108_4110 : List (BitVec (edgeCount 12)) :=
  missing4108_4109 ++ missing4109_4110
abbrev records4108_4110 : List Blob :=
  records4108_4109 ++ records4109_4110
theorem aligned4108_4110 :
    AlignedValid 12 2 missing4108_4110 records4108_4110 :=
  aligned4108_4109.append aligned4109_4110

def missing4107_4110 : List (BitVec (edgeCount 12)) :=
  missing4107_4108 ++ missing4108_4110
abbrev records4107_4110 : List Blob :=
  records4107_4108 ++ records4108_4110
theorem aligned4107_4110 :
    AlignedValid 12 2 missing4107_4110 records4107_4110 :=
  aligned4107_4108.append aligned4108_4110

def missing4110_4111 : List (BitVec (edgeCount 12)) :=
  [missing4110]
abbrev records4110_4111 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4110]
theorem aligned4110_4111 :
    AlignedValid 12 2 missing4110_4111 records4110_4111 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4110
    maskCheck4110 AlignedValid.nil

def missing4111_4112 : List (BitVec (edgeCount 12)) :=
  [missing4111]
abbrev records4111_4112 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4111]
theorem aligned4111_4112 :
    AlignedValid 12 2 missing4111_4112 records4111_4112 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4111
    maskCheck4111 AlignedValid.nil

def missing4112_4113 : List (BitVec (edgeCount 12)) :=
  [missing4112]
abbrev records4112_4113 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4112]
theorem aligned4112_4113 :
    AlignedValid 12 2 missing4112_4113 records4112_4113 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4112
    maskCheck4112 AlignedValid.nil

def missing4111_4113 : List (BitVec (edgeCount 12)) :=
  missing4111_4112 ++ missing4112_4113
abbrev records4111_4113 : List Blob :=
  records4111_4112 ++ records4112_4113
theorem aligned4111_4113 :
    AlignedValid 12 2 missing4111_4113 records4111_4113 :=
  aligned4111_4112.append aligned4112_4113

def missing4110_4113 : List (BitVec (edgeCount 12)) :=
  missing4110_4111 ++ missing4111_4113
abbrev records4110_4113 : List Blob :=
  records4110_4111 ++ records4111_4113
theorem aligned4110_4113 :
    AlignedValid 12 2 missing4110_4113 records4110_4113 :=
  aligned4110_4111.append aligned4111_4113

def missing4107_4113 : List (BitVec (edgeCount 12)) :=
  missing4107_4110 ++ missing4110_4113
abbrev records4107_4113 : List Blob :=
  records4107_4110 ++ records4110_4113
theorem aligned4107_4113 :
    AlignedValid 12 2 missing4107_4113 records4107_4113 :=
  aligned4107_4110.append aligned4110_4113

def missing4113_4114 : List (BitVec (edgeCount 12)) :=
  [missing4113]
abbrev records4113_4114 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4113]
theorem aligned4113_4114 :
    AlignedValid 12 2 missing4113_4114 records4113_4114 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4113
    maskCheck4113 AlignedValid.nil

def missing4114_4115 : List (BitVec (edgeCount 12)) :=
  [missing4114]
abbrev records4114_4115 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4114]
theorem aligned4114_4115 :
    AlignedValid 12 2 missing4114_4115 records4114_4115 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4114
    maskCheck4114 AlignedValid.nil

def missing4115_4116 : List (BitVec (edgeCount 12)) :=
  [missing4115]
abbrev records4115_4116 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4115]
theorem aligned4115_4116 :
    AlignedValid 12 2 missing4115_4116 records4115_4116 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4115
    maskCheck4115 AlignedValid.nil

def missing4114_4116 : List (BitVec (edgeCount 12)) :=
  missing4114_4115 ++ missing4115_4116
abbrev records4114_4116 : List Blob :=
  records4114_4115 ++ records4115_4116
theorem aligned4114_4116 :
    AlignedValid 12 2 missing4114_4116 records4114_4116 :=
  aligned4114_4115.append aligned4115_4116

def missing4113_4116 : List (BitVec (edgeCount 12)) :=
  missing4113_4114 ++ missing4114_4116
abbrev records4113_4116 : List Blob :=
  records4113_4114 ++ records4114_4116
theorem aligned4113_4116 :
    AlignedValid 12 2 missing4113_4116 records4113_4116 :=
  aligned4113_4114.append aligned4114_4116

def missing4116_4117 : List (BitVec (edgeCount 12)) :=
  [missing4116]
abbrev records4116_4117 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4116]
theorem aligned4116_4117 :
    AlignedValid 12 2 missing4116_4117 records4116_4117 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4116
    maskCheck4116 AlignedValid.nil

def missing4117_4118 : List (BitVec (edgeCount 12)) :=
  [missing4117]
abbrev records4117_4118 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4117]
theorem aligned4117_4118 :
    AlignedValid 12 2 missing4117_4118 records4117_4118 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4117
    maskCheck4117 AlignedValid.nil

def missing4118_4119 : List (BitVec (edgeCount 12)) :=
  [missing4118]
abbrev records4118_4119 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4118]
theorem aligned4118_4119 :
    AlignedValid 12 2 missing4118_4119 records4118_4119 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4118
    maskCheck4118 AlignedValid.nil

def missing4117_4119 : List (BitVec (edgeCount 12)) :=
  missing4117_4118 ++ missing4118_4119
abbrev records4117_4119 : List Blob :=
  records4117_4118 ++ records4118_4119
theorem aligned4117_4119 :
    AlignedValid 12 2 missing4117_4119 records4117_4119 :=
  aligned4117_4118.append aligned4118_4119

def missing4116_4119 : List (BitVec (edgeCount 12)) :=
  missing4116_4117 ++ missing4117_4119
abbrev records4116_4119 : List Blob :=
  records4116_4117 ++ records4117_4119
theorem aligned4116_4119 :
    AlignedValid 12 2 missing4116_4119 records4116_4119 :=
  aligned4116_4117.append aligned4117_4119

def missing4113_4119 : List (BitVec (edgeCount 12)) :=
  missing4113_4116 ++ missing4116_4119
abbrev records4113_4119 : List Blob :=
  records4113_4116 ++ records4116_4119
theorem aligned4113_4119 :
    AlignedValid 12 2 missing4113_4119 records4113_4119 :=
  aligned4113_4116.append aligned4116_4119

def missing4107_4119 : List (BitVec (edgeCount 12)) :=
  missing4107_4113 ++ missing4113_4119
abbrev records4107_4119 : List Blob :=
  records4107_4113 ++ records4113_4119
theorem aligned4107_4119 :
    AlignedValid 12 2 missing4107_4119 records4107_4119 :=
  aligned4107_4113.append aligned4113_4119

def missing4096_4119 : List (BitVec (edgeCount 12)) :=
  missing4096_4107 ++ missing4107_4119
abbrev records4096_4119 : List Blob :=
  records4096_4107 ++ records4107_4119
theorem aligned4096_4119 :
    AlignedValid 12 2 missing4096_4119 records4096_4119 :=
  aligned4096_4107.append aligned4107_4119

def missing4119_4120 : List (BitVec (edgeCount 12)) :=
  [missing4119]
abbrev records4119_4120 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4119]
theorem aligned4119_4120 :
    AlignedValid 12 2 missing4119_4120 records4119_4120 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4119
    maskCheck4119 AlignedValid.nil

def missing4120_4121 : List (BitVec (edgeCount 12)) :=
  [missing4120]
abbrev records4120_4121 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4120]
theorem aligned4120_4121 :
    AlignedValid 12 2 missing4120_4121 records4120_4121 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4120
    maskCheck4120 AlignedValid.nil

def missing4121_4122 : List (BitVec (edgeCount 12)) :=
  [missing4121]
abbrev records4121_4122 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4121]
theorem aligned4121_4122 :
    AlignedValid 12 2 missing4121_4122 records4121_4122 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4121
    maskCheck4121 AlignedValid.nil

def missing4120_4122 : List (BitVec (edgeCount 12)) :=
  missing4120_4121 ++ missing4121_4122
abbrev records4120_4122 : List Blob :=
  records4120_4121 ++ records4121_4122
theorem aligned4120_4122 :
    AlignedValid 12 2 missing4120_4122 records4120_4122 :=
  aligned4120_4121.append aligned4121_4122

def missing4119_4122 : List (BitVec (edgeCount 12)) :=
  missing4119_4120 ++ missing4120_4122
abbrev records4119_4122 : List Blob :=
  records4119_4120 ++ records4120_4122
theorem aligned4119_4122 :
    AlignedValid 12 2 missing4119_4122 records4119_4122 :=
  aligned4119_4120.append aligned4120_4122

def missing4122_4123 : List (BitVec (edgeCount 12)) :=
  [missing4122]
abbrev records4122_4123 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4122]
theorem aligned4122_4123 :
    AlignedValid 12 2 missing4122_4123 records4122_4123 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4122
    maskCheck4122 AlignedValid.nil

def missing4123_4124 : List (BitVec (edgeCount 12)) :=
  [missing4123]
abbrev records4123_4124 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4123]
theorem aligned4123_4124 :
    AlignedValid 12 2 missing4123_4124 records4123_4124 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4123
    maskCheck4123 AlignedValid.nil

def missing4124_4125 : List (BitVec (edgeCount 12)) :=
  [missing4124]
abbrev records4124_4125 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4124]
theorem aligned4124_4125 :
    AlignedValid 12 2 missing4124_4125 records4124_4125 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4124
    maskCheck4124 AlignedValid.nil

def missing4123_4125 : List (BitVec (edgeCount 12)) :=
  missing4123_4124 ++ missing4124_4125
abbrev records4123_4125 : List Blob :=
  records4123_4124 ++ records4124_4125
theorem aligned4123_4125 :
    AlignedValid 12 2 missing4123_4125 records4123_4125 :=
  aligned4123_4124.append aligned4124_4125

def missing4122_4125 : List (BitVec (edgeCount 12)) :=
  missing4122_4123 ++ missing4123_4125
abbrev records4122_4125 : List Blob :=
  records4122_4123 ++ records4123_4125
theorem aligned4122_4125 :
    AlignedValid 12 2 missing4122_4125 records4122_4125 :=
  aligned4122_4123.append aligned4123_4125

def missing4119_4125 : List (BitVec (edgeCount 12)) :=
  missing4119_4122 ++ missing4122_4125
abbrev records4119_4125 : List Blob :=
  records4119_4122 ++ records4122_4125
theorem aligned4119_4125 :
    AlignedValid 12 2 missing4119_4125 records4119_4125 :=
  aligned4119_4122.append aligned4122_4125

def missing4125_4126 : List (BitVec (edgeCount 12)) :=
  [missing4125]
abbrev records4125_4126 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4125]
theorem aligned4125_4126 :
    AlignedValid 12 2 missing4125_4126 records4125_4126 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4125
    maskCheck4125 AlignedValid.nil

def missing4126_4127 : List (BitVec (edgeCount 12)) :=
  [missing4126]
abbrev records4126_4127 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4126]
theorem aligned4126_4127 :
    AlignedValid 12 2 missing4126_4127 records4126_4127 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4126
    maskCheck4126 AlignedValid.nil

def missing4127_4128 : List (BitVec (edgeCount 12)) :=
  [missing4127]
abbrev records4127_4128 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4127]
theorem aligned4127_4128 :
    AlignedValid 12 2 missing4127_4128 records4127_4128 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4127
    maskCheck4127 AlignedValid.nil

def missing4126_4128 : List (BitVec (edgeCount 12)) :=
  missing4126_4127 ++ missing4127_4128
abbrev records4126_4128 : List Blob :=
  records4126_4127 ++ records4127_4128
theorem aligned4126_4128 :
    AlignedValid 12 2 missing4126_4128 records4126_4128 :=
  aligned4126_4127.append aligned4127_4128

def missing4125_4128 : List (BitVec (edgeCount 12)) :=
  missing4125_4126 ++ missing4126_4128
abbrev records4125_4128 : List Blob :=
  records4125_4126 ++ records4126_4128
theorem aligned4125_4128 :
    AlignedValid 12 2 missing4125_4128 records4125_4128 :=
  aligned4125_4126.append aligned4126_4128

def missing4128_4129 : List (BitVec (edgeCount 12)) :=
  [missing4128]
abbrev records4128_4129 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4128]
theorem aligned4128_4129 :
    AlignedValid 12 2 missing4128_4129 records4128_4129 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4128
    maskCheck4128 AlignedValid.nil

def missing4129_4130 : List (BitVec (edgeCount 12)) :=
  [missing4129]
abbrev records4129_4130 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4129]
theorem aligned4129_4130 :
    AlignedValid 12 2 missing4129_4130 records4129_4130 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4129
    maskCheck4129 AlignedValid.nil

def missing4130_4131 : List (BitVec (edgeCount 12)) :=
  [missing4130]
abbrev records4130_4131 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4130]
theorem aligned4130_4131 :
    AlignedValid 12 2 missing4130_4131 records4130_4131 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4130
    maskCheck4130 AlignedValid.nil

def missing4129_4131 : List (BitVec (edgeCount 12)) :=
  missing4129_4130 ++ missing4130_4131
abbrev records4129_4131 : List Blob :=
  records4129_4130 ++ records4130_4131
theorem aligned4129_4131 :
    AlignedValid 12 2 missing4129_4131 records4129_4131 :=
  aligned4129_4130.append aligned4130_4131

def missing4128_4131 : List (BitVec (edgeCount 12)) :=
  missing4128_4129 ++ missing4129_4131
abbrev records4128_4131 : List Blob :=
  records4128_4129 ++ records4129_4131
theorem aligned4128_4131 :
    AlignedValid 12 2 missing4128_4131 records4128_4131 :=
  aligned4128_4129.append aligned4129_4131

def missing4125_4131 : List (BitVec (edgeCount 12)) :=
  missing4125_4128 ++ missing4128_4131
abbrev records4125_4131 : List Blob :=
  records4125_4128 ++ records4128_4131
theorem aligned4125_4131 :
    AlignedValid 12 2 missing4125_4131 records4125_4131 :=
  aligned4125_4128.append aligned4128_4131

def missing4119_4131 : List (BitVec (edgeCount 12)) :=
  missing4119_4125 ++ missing4125_4131
abbrev records4119_4131 : List Blob :=
  records4119_4125 ++ records4125_4131
theorem aligned4119_4131 :
    AlignedValid 12 2 missing4119_4131 records4119_4131 :=
  aligned4119_4125.append aligned4125_4131

def missing4131_4132 : List (BitVec (edgeCount 12)) :=
  [missing4131]
abbrev records4131_4132 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4131]
theorem aligned4131_4132 :
    AlignedValid 12 2 missing4131_4132 records4131_4132 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4131
    maskCheck4131 AlignedValid.nil

def missing4132_4133 : List (BitVec (edgeCount 12)) :=
  [missing4132]
abbrev records4132_4133 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4132]
theorem aligned4132_4133 :
    AlignedValid 12 2 missing4132_4133 records4132_4133 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4132
    maskCheck4132 AlignedValid.nil

def missing4133_4134 : List (BitVec (edgeCount 12)) :=
  [missing4133]
abbrev records4133_4134 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4133]
theorem aligned4133_4134 :
    AlignedValid 12 2 missing4133_4134 records4133_4134 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4133
    maskCheck4133 AlignedValid.nil

def missing4132_4134 : List (BitVec (edgeCount 12)) :=
  missing4132_4133 ++ missing4133_4134
abbrev records4132_4134 : List Blob :=
  records4132_4133 ++ records4133_4134
theorem aligned4132_4134 :
    AlignedValid 12 2 missing4132_4134 records4132_4134 :=
  aligned4132_4133.append aligned4133_4134

def missing4131_4134 : List (BitVec (edgeCount 12)) :=
  missing4131_4132 ++ missing4132_4134
abbrev records4131_4134 : List Blob :=
  records4131_4132 ++ records4132_4134
theorem aligned4131_4134 :
    AlignedValid 12 2 missing4131_4134 records4131_4134 :=
  aligned4131_4132.append aligned4132_4134

def missing4134_4135 : List (BitVec (edgeCount 12)) :=
  [missing4134]
abbrev records4134_4135 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4134]
theorem aligned4134_4135 :
    AlignedValid 12 2 missing4134_4135 records4134_4135 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4134
    maskCheck4134 AlignedValid.nil

def missing4135_4136 : List (BitVec (edgeCount 12)) :=
  [missing4135]
abbrev records4135_4136 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4135]
theorem aligned4135_4136 :
    AlignedValid 12 2 missing4135_4136 records4135_4136 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4135
    maskCheck4135 AlignedValid.nil

def missing4136_4137 : List (BitVec (edgeCount 12)) :=
  [missing4136]
abbrev records4136_4137 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4136]
theorem aligned4136_4137 :
    AlignedValid 12 2 missing4136_4137 records4136_4137 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4136
    maskCheck4136 AlignedValid.nil

def missing4135_4137 : List (BitVec (edgeCount 12)) :=
  missing4135_4136 ++ missing4136_4137
abbrev records4135_4137 : List Blob :=
  records4135_4136 ++ records4136_4137
theorem aligned4135_4137 :
    AlignedValid 12 2 missing4135_4137 records4135_4137 :=
  aligned4135_4136.append aligned4136_4137

def missing4134_4137 : List (BitVec (edgeCount 12)) :=
  missing4134_4135 ++ missing4135_4137
abbrev records4134_4137 : List Blob :=
  records4134_4135 ++ records4135_4137
theorem aligned4134_4137 :
    AlignedValid 12 2 missing4134_4137 records4134_4137 :=
  aligned4134_4135.append aligned4135_4137

def missing4131_4137 : List (BitVec (edgeCount 12)) :=
  missing4131_4134 ++ missing4134_4137
abbrev records4131_4137 : List Blob :=
  records4131_4134 ++ records4134_4137
theorem aligned4131_4137 :
    AlignedValid 12 2 missing4131_4137 records4131_4137 :=
  aligned4131_4134.append aligned4134_4137

def missing4137_4138 : List (BitVec (edgeCount 12)) :=
  [missing4137]
abbrev records4137_4138 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4137]
theorem aligned4137_4138 :
    AlignedValid 12 2 missing4137_4138 records4137_4138 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4137
    maskCheck4137 AlignedValid.nil

def missing4138_4139 : List (BitVec (edgeCount 12)) :=
  [missing4138]
abbrev records4138_4139 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4138]
theorem aligned4138_4139 :
    AlignedValid 12 2 missing4138_4139 records4138_4139 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4138
    maskCheck4138 AlignedValid.nil

def missing4139_4140 : List (BitVec (edgeCount 12)) :=
  [missing4139]
abbrev records4139_4140 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4139]
theorem aligned4139_4140 :
    AlignedValid 12 2 missing4139_4140 records4139_4140 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4139
    maskCheck4139 AlignedValid.nil

def missing4138_4140 : List (BitVec (edgeCount 12)) :=
  missing4138_4139 ++ missing4139_4140
abbrev records4138_4140 : List Blob :=
  records4138_4139 ++ records4139_4140
theorem aligned4138_4140 :
    AlignedValid 12 2 missing4138_4140 records4138_4140 :=
  aligned4138_4139.append aligned4139_4140

def missing4137_4140 : List (BitVec (edgeCount 12)) :=
  missing4137_4138 ++ missing4138_4140
abbrev records4137_4140 : List Blob :=
  records4137_4138 ++ records4138_4140
theorem aligned4137_4140 :
    AlignedValid 12 2 missing4137_4140 records4137_4140 :=
  aligned4137_4138.append aligned4138_4140

def missing4140_4141 : List (BitVec (edgeCount 12)) :=
  [missing4140]
abbrev records4140_4141 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4140]
theorem aligned4140_4141 :
    AlignedValid 12 2 missing4140_4141 records4140_4141 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4140
    maskCheck4140 AlignedValid.nil

def missing4141_4142 : List (BitVec (edgeCount 12)) :=
  [missing4141]
abbrev records4141_4142 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4141]
theorem aligned4141_4142 :
    AlignedValid 12 2 missing4141_4142 records4141_4142 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4141
    maskCheck4141 AlignedValid.nil

def missing4142_4143 : List (BitVec (edgeCount 12)) :=
  [missing4142]
abbrev records4142_4143 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4142]
theorem aligned4142_4143 :
    AlignedValid 12 2 missing4142_4143 records4142_4143 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4142
    maskCheck4142 AlignedValid.nil

def missing4141_4143 : List (BitVec (edgeCount 12)) :=
  missing4141_4142 ++ missing4142_4143
abbrev records4141_4143 : List Blob :=
  records4141_4142 ++ records4142_4143
theorem aligned4141_4143 :
    AlignedValid 12 2 missing4141_4143 records4141_4143 :=
  aligned4141_4142.append aligned4142_4143

def missing4140_4143 : List (BitVec (edgeCount 12)) :=
  missing4140_4141 ++ missing4141_4143
abbrev records4140_4143 : List Blob :=
  records4140_4141 ++ records4141_4143
theorem aligned4140_4143 :
    AlignedValid 12 2 missing4140_4143 records4140_4143 :=
  aligned4140_4141.append aligned4141_4143

def missing4137_4143 : List (BitVec (edgeCount 12)) :=
  missing4137_4140 ++ missing4140_4143
abbrev records4137_4143 : List Blob :=
  records4137_4140 ++ records4140_4143
theorem aligned4137_4143 :
    AlignedValid 12 2 missing4137_4143 records4137_4143 :=
  aligned4137_4140.append aligned4140_4143

def missing4131_4143 : List (BitVec (edgeCount 12)) :=
  missing4131_4137 ++ missing4137_4143
abbrev records4131_4143 : List Blob :=
  records4131_4137 ++ records4137_4143
theorem aligned4131_4143 :
    AlignedValid 12 2 missing4131_4143 records4131_4143 :=
  aligned4131_4137.append aligned4137_4143

def missing4119_4143 : List (BitVec (edgeCount 12)) :=
  missing4119_4131 ++ missing4131_4143
abbrev records4119_4143 : List Blob :=
  records4119_4131 ++ records4131_4143
theorem aligned4119_4143 :
    AlignedValid 12 2 missing4119_4143 records4119_4143 :=
  aligned4119_4131.append aligned4131_4143

def missing4096_4143 : List (BitVec (edgeCount 12)) :=
  missing4096_4119 ++ missing4119_4143
abbrev records4096_4143 : List Blob :=
  records4096_4119 ++ records4119_4143
theorem aligned4096_4143 :
    AlignedValid 12 2 missing4096_4143 records4096_4143 :=
  aligned4096_4119.append aligned4119_4143

def missing4143_4144 : List (BitVec (edgeCount 12)) :=
  [missing4143]
abbrev records4143_4144 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4143]
theorem aligned4143_4144 :
    AlignedValid 12 2 missing4143_4144 records4143_4144 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4143
    maskCheck4143 AlignedValid.nil

def missing4144_4145 : List (BitVec (edgeCount 12)) :=
  [missing4144]
abbrev records4144_4145 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4144]
theorem aligned4144_4145 :
    AlignedValid 12 2 missing4144_4145 records4144_4145 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4144
    maskCheck4144 AlignedValid.nil

def missing4145_4146 : List (BitVec (edgeCount 12)) :=
  [missing4145]
abbrev records4145_4146 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4145]
theorem aligned4145_4146 :
    AlignedValid 12 2 missing4145_4146 records4145_4146 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4145
    maskCheck4145 AlignedValid.nil

def missing4144_4146 : List (BitVec (edgeCount 12)) :=
  missing4144_4145 ++ missing4145_4146
abbrev records4144_4146 : List Blob :=
  records4144_4145 ++ records4145_4146
theorem aligned4144_4146 :
    AlignedValid 12 2 missing4144_4146 records4144_4146 :=
  aligned4144_4145.append aligned4145_4146

def missing4143_4146 : List (BitVec (edgeCount 12)) :=
  missing4143_4144 ++ missing4144_4146
abbrev records4143_4146 : List Blob :=
  records4143_4144 ++ records4144_4146
theorem aligned4143_4146 :
    AlignedValid 12 2 missing4143_4146 records4143_4146 :=
  aligned4143_4144.append aligned4144_4146

def missing4146_4147 : List (BitVec (edgeCount 12)) :=
  [missing4146]
abbrev records4146_4147 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4146]
theorem aligned4146_4147 :
    AlignedValid 12 2 missing4146_4147 records4146_4147 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4146
    maskCheck4146 AlignedValid.nil

def missing4147_4148 : List (BitVec (edgeCount 12)) :=
  [missing4147]
abbrev records4147_4148 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4147]
theorem aligned4147_4148 :
    AlignedValid 12 2 missing4147_4148 records4147_4148 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4147
    maskCheck4147 AlignedValid.nil

def missing4148_4149 : List (BitVec (edgeCount 12)) :=
  [missing4148]
abbrev records4148_4149 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4148]
theorem aligned4148_4149 :
    AlignedValid 12 2 missing4148_4149 records4148_4149 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4148
    maskCheck4148 AlignedValid.nil

def missing4147_4149 : List (BitVec (edgeCount 12)) :=
  missing4147_4148 ++ missing4148_4149
abbrev records4147_4149 : List Blob :=
  records4147_4148 ++ records4148_4149
theorem aligned4147_4149 :
    AlignedValid 12 2 missing4147_4149 records4147_4149 :=
  aligned4147_4148.append aligned4148_4149

def missing4146_4149 : List (BitVec (edgeCount 12)) :=
  missing4146_4147 ++ missing4147_4149
abbrev records4146_4149 : List Blob :=
  records4146_4147 ++ records4147_4149
theorem aligned4146_4149 :
    AlignedValid 12 2 missing4146_4149 records4146_4149 :=
  aligned4146_4147.append aligned4147_4149

def missing4143_4149 : List (BitVec (edgeCount 12)) :=
  missing4143_4146 ++ missing4146_4149
abbrev records4143_4149 : List Blob :=
  records4143_4146 ++ records4146_4149
theorem aligned4143_4149 :
    AlignedValid 12 2 missing4143_4149 records4143_4149 :=
  aligned4143_4146.append aligned4146_4149

def missing4149_4150 : List (BitVec (edgeCount 12)) :=
  [missing4149]
abbrev records4149_4150 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4149]
theorem aligned4149_4150 :
    AlignedValid 12 2 missing4149_4150 records4149_4150 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4149
    maskCheck4149 AlignedValid.nil

def missing4150_4151 : List (BitVec (edgeCount 12)) :=
  [missing4150]
abbrev records4150_4151 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4150]
theorem aligned4150_4151 :
    AlignedValid 12 2 missing4150_4151 records4150_4151 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4150
    maskCheck4150 AlignedValid.nil

def missing4151_4152 : List (BitVec (edgeCount 12)) :=
  [missing4151]
abbrev records4151_4152 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4151]
theorem aligned4151_4152 :
    AlignedValid 12 2 missing4151_4152 records4151_4152 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4151
    maskCheck4151 AlignedValid.nil

def missing4150_4152 : List (BitVec (edgeCount 12)) :=
  missing4150_4151 ++ missing4151_4152
abbrev records4150_4152 : List Blob :=
  records4150_4151 ++ records4151_4152
theorem aligned4150_4152 :
    AlignedValid 12 2 missing4150_4152 records4150_4152 :=
  aligned4150_4151.append aligned4151_4152

def missing4149_4152 : List (BitVec (edgeCount 12)) :=
  missing4149_4150 ++ missing4150_4152
abbrev records4149_4152 : List Blob :=
  records4149_4150 ++ records4150_4152
theorem aligned4149_4152 :
    AlignedValid 12 2 missing4149_4152 records4149_4152 :=
  aligned4149_4150.append aligned4150_4152

def missing4152_4153 : List (BitVec (edgeCount 12)) :=
  [missing4152]
abbrev records4152_4153 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4152]
theorem aligned4152_4153 :
    AlignedValid 12 2 missing4152_4153 records4152_4153 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4152
    maskCheck4152 AlignedValid.nil

def missing4153_4154 : List (BitVec (edgeCount 12)) :=
  [missing4153]
abbrev records4153_4154 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4153]
theorem aligned4153_4154 :
    AlignedValid 12 2 missing4153_4154 records4153_4154 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4153
    maskCheck4153 AlignedValid.nil

def missing4154_4155 : List (BitVec (edgeCount 12)) :=
  [missing4154]
abbrev records4154_4155 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4154]
theorem aligned4154_4155 :
    AlignedValid 12 2 missing4154_4155 records4154_4155 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4154
    maskCheck4154 AlignedValid.nil

def missing4153_4155 : List (BitVec (edgeCount 12)) :=
  missing4153_4154 ++ missing4154_4155
abbrev records4153_4155 : List Blob :=
  records4153_4154 ++ records4154_4155
theorem aligned4153_4155 :
    AlignedValid 12 2 missing4153_4155 records4153_4155 :=
  aligned4153_4154.append aligned4154_4155

def missing4152_4155 : List (BitVec (edgeCount 12)) :=
  missing4152_4153 ++ missing4153_4155
abbrev records4152_4155 : List Blob :=
  records4152_4153 ++ records4153_4155
theorem aligned4152_4155 :
    AlignedValid 12 2 missing4152_4155 records4152_4155 :=
  aligned4152_4153.append aligned4153_4155

def missing4149_4155 : List (BitVec (edgeCount 12)) :=
  missing4149_4152 ++ missing4152_4155
abbrev records4149_4155 : List Blob :=
  records4149_4152 ++ records4152_4155
theorem aligned4149_4155 :
    AlignedValid 12 2 missing4149_4155 records4149_4155 :=
  aligned4149_4152.append aligned4152_4155

def missing4143_4155 : List (BitVec (edgeCount 12)) :=
  missing4143_4149 ++ missing4149_4155
abbrev records4143_4155 : List Blob :=
  records4143_4149 ++ records4149_4155
theorem aligned4143_4155 :
    AlignedValid 12 2 missing4143_4155 records4143_4155 :=
  aligned4143_4149.append aligned4149_4155

def missing4155_4156 : List (BitVec (edgeCount 12)) :=
  [missing4155]
abbrev records4155_4156 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4155]
theorem aligned4155_4156 :
    AlignedValid 12 2 missing4155_4156 records4155_4156 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4155
    maskCheck4155 AlignedValid.nil

def missing4156_4157 : List (BitVec (edgeCount 12)) :=
  [missing4156]
abbrev records4156_4157 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4156]
theorem aligned4156_4157 :
    AlignedValid 12 2 missing4156_4157 records4156_4157 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4156
    maskCheck4156 AlignedValid.nil

def missing4157_4158 : List (BitVec (edgeCount 12)) :=
  [missing4157]
abbrev records4157_4158 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4157]
theorem aligned4157_4158 :
    AlignedValid 12 2 missing4157_4158 records4157_4158 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4157
    maskCheck4157 AlignedValid.nil

def missing4156_4158 : List (BitVec (edgeCount 12)) :=
  missing4156_4157 ++ missing4157_4158
abbrev records4156_4158 : List Blob :=
  records4156_4157 ++ records4157_4158
theorem aligned4156_4158 :
    AlignedValid 12 2 missing4156_4158 records4156_4158 :=
  aligned4156_4157.append aligned4157_4158

def missing4155_4158 : List (BitVec (edgeCount 12)) :=
  missing4155_4156 ++ missing4156_4158
abbrev records4155_4158 : List Blob :=
  records4155_4156 ++ records4156_4158
theorem aligned4155_4158 :
    AlignedValid 12 2 missing4155_4158 records4155_4158 :=
  aligned4155_4156.append aligned4156_4158

def missing4158_4159 : List (BitVec (edgeCount 12)) :=
  [missing4158]
abbrev records4158_4159 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4158]
theorem aligned4158_4159 :
    AlignedValid 12 2 missing4158_4159 records4158_4159 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4158
    maskCheck4158 AlignedValid.nil

def missing4159_4160 : List (BitVec (edgeCount 12)) :=
  [missing4159]
abbrev records4159_4160 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4159]
theorem aligned4159_4160 :
    AlignedValid 12 2 missing4159_4160 records4159_4160 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4159
    maskCheck4159 AlignedValid.nil

def missing4160_4161 : List (BitVec (edgeCount 12)) :=
  [missing4160]
abbrev records4160_4161 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4160]
theorem aligned4160_4161 :
    AlignedValid 12 2 missing4160_4161 records4160_4161 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4160
    maskCheck4160 AlignedValid.nil

def missing4159_4161 : List (BitVec (edgeCount 12)) :=
  missing4159_4160 ++ missing4160_4161
abbrev records4159_4161 : List Blob :=
  records4159_4160 ++ records4160_4161
theorem aligned4159_4161 :
    AlignedValid 12 2 missing4159_4161 records4159_4161 :=
  aligned4159_4160.append aligned4160_4161

def missing4158_4161 : List (BitVec (edgeCount 12)) :=
  missing4158_4159 ++ missing4159_4161
abbrev records4158_4161 : List Blob :=
  records4158_4159 ++ records4159_4161
theorem aligned4158_4161 :
    AlignedValid 12 2 missing4158_4161 records4158_4161 :=
  aligned4158_4159.append aligned4159_4161

def missing4155_4161 : List (BitVec (edgeCount 12)) :=
  missing4155_4158 ++ missing4158_4161
abbrev records4155_4161 : List Blob :=
  records4155_4158 ++ records4158_4161
theorem aligned4155_4161 :
    AlignedValid 12 2 missing4155_4161 records4155_4161 :=
  aligned4155_4158.append aligned4158_4161

def missing4161_4162 : List (BitVec (edgeCount 12)) :=
  [missing4161]
abbrev records4161_4162 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4161]
theorem aligned4161_4162 :
    AlignedValid 12 2 missing4161_4162 records4161_4162 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4161
    maskCheck4161 AlignedValid.nil

def missing4162_4163 : List (BitVec (edgeCount 12)) :=
  [missing4162]
abbrev records4162_4163 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4162]
theorem aligned4162_4163 :
    AlignedValid 12 2 missing4162_4163 records4162_4163 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4162
    maskCheck4162 AlignedValid.nil

def missing4163_4164 : List (BitVec (edgeCount 12)) :=
  [missing4163]
abbrev records4163_4164 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4163]
theorem aligned4163_4164 :
    AlignedValid 12 2 missing4163_4164 records4163_4164 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4163
    maskCheck4163 AlignedValid.nil

def missing4162_4164 : List (BitVec (edgeCount 12)) :=
  missing4162_4163 ++ missing4163_4164
abbrev records4162_4164 : List Blob :=
  records4162_4163 ++ records4163_4164
theorem aligned4162_4164 :
    AlignedValid 12 2 missing4162_4164 records4162_4164 :=
  aligned4162_4163.append aligned4163_4164

def missing4161_4164 : List (BitVec (edgeCount 12)) :=
  missing4161_4162 ++ missing4162_4164
abbrev records4161_4164 : List Blob :=
  records4161_4162 ++ records4162_4164
theorem aligned4161_4164 :
    AlignedValid 12 2 missing4161_4164 records4161_4164 :=
  aligned4161_4162.append aligned4162_4164

def missing4164_4165 : List (BitVec (edgeCount 12)) :=
  [missing4164]
abbrev records4164_4165 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4164]
theorem aligned4164_4165 :
    AlignedValid 12 2 missing4164_4165 records4164_4165 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4164
    maskCheck4164 AlignedValid.nil

def missing4165_4166 : List (BitVec (edgeCount 12)) :=
  [missing4165]
abbrev records4165_4166 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4165]
theorem aligned4165_4166 :
    AlignedValid 12 2 missing4165_4166 records4165_4166 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4165
    maskCheck4165 AlignedValid.nil

def missing4166_4167 : List (BitVec (edgeCount 12)) :=
  [missing4166]
abbrev records4166_4167 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4166]
theorem aligned4166_4167 :
    AlignedValid 12 2 missing4166_4167 records4166_4167 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4166
    maskCheck4166 AlignedValid.nil

def missing4165_4167 : List (BitVec (edgeCount 12)) :=
  missing4165_4166 ++ missing4166_4167
abbrev records4165_4167 : List Blob :=
  records4165_4166 ++ records4166_4167
theorem aligned4165_4167 :
    AlignedValid 12 2 missing4165_4167 records4165_4167 :=
  aligned4165_4166.append aligned4166_4167

def missing4164_4167 : List (BitVec (edgeCount 12)) :=
  missing4164_4165 ++ missing4165_4167
abbrev records4164_4167 : List Blob :=
  records4164_4165 ++ records4165_4167
theorem aligned4164_4167 :
    AlignedValid 12 2 missing4164_4167 records4164_4167 :=
  aligned4164_4165.append aligned4165_4167

def missing4161_4167 : List (BitVec (edgeCount 12)) :=
  missing4161_4164 ++ missing4164_4167
abbrev records4161_4167 : List Blob :=
  records4161_4164 ++ records4164_4167
theorem aligned4161_4167 :
    AlignedValid 12 2 missing4161_4167 records4161_4167 :=
  aligned4161_4164.append aligned4164_4167

def missing4155_4167 : List (BitVec (edgeCount 12)) :=
  missing4155_4161 ++ missing4161_4167
abbrev records4155_4167 : List Blob :=
  records4155_4161 ++ records4161_4167
theorem aligned4155_4167 :
    AlignedValid 12 2 missing4155_4167 records4155_4167 :=
  aligned4155_4161.append aligned4161_4167

def missing4143_4167 : List (BitVec (edgeCount 12)) :=
  missing4143_4155 ++ missing4155_4167
abbrev records4143_4167 : List Blob :=
  records4143_4155 ++ records4155_4167
theorem aligned4143_4167 :
    AlignedValid 12 2 missing4143_4167 records4143_4167 :=
  aligned4143_4155.append aligned4155_4167

def missing4167_4168 : List (BitVec (edgeCount 12)) :=
  [missing4167]
abbrev records4167_4168 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4167]
theorem aligned4167_4168 :
    AlignedValid 12 2 missing4167_4168 records4167_4168 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4167
    maskCheck4167 AlignedValid.nil

def missing4168_4169 : List (BitVec (edgeCount 12)) :=
  [missing4168]
abbrev records4168_4169 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4168]
theorem aligned4168_4169 :
    AlignedValid 12 2 missing4168_4169 records4168_4169 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4168
    maskCheck4168 AlignedValid.nil

def missing4169_4170 : List (BitVec (edgeCount 12)) :=
  [missing4169]
abbrev records4169_4170 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4169]
theorem aligned4169_4170 :
    AlignedValid 12 2 missing4169_4170 records4169_4170 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4169
    maskCheck4169 AlignedValid.nil

def missing4168_4170 : List (BitVec (edgeCount 12)) :=
  missing4168_4169 ++ missing4169_4170
abbrev records4168_4170 : List Blob :=
  records4168_4169 ++ records4169_4170
theorem aligned4168_4170 :
    AlignedValid 12 2 missing4168_4170 records4168_4170 :=
  aligned4168_4169.append aligned4169_4170

def missing4167_4170 : List (BitVec (edgeCount 12)) :=
  missing4167_4168 ++ missing4168_4170
abbrev records4167_4170 : List Blob :=
  records4167_4168 ++ records4168_4170
theorem aligned4167_4170 :
    AlignedValid 12 2 missing4167_4170 records4167_4170 :=
  aligned4167_4168.append aligned4168_4170

def missing4170_4171 : List (BitVec (edgeCount 12)) :=
  [missing4170]
abbrev records4170_4171 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4170]
theorem aligned4170_4171 :
    AlignedValid 12 2 missing4170_4171 records4170_4171 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4170
    maskCheck4170 AlignedValid.nil

def missing4171_4172 : List (BitVec (edgeCount 12)) :=
  [missing4171]
abbrev records4171_4172 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4171]
theorem aligned4171_4172 :
    AlignedValid 12 2 missing4171_4172 records4171_4172 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4171
    maskCheck4171 AlignedValid.nil

def missing4172_4173 : List (BitVec (edgeCount 12)) :=
  [missing4172]
abbrev records4172_4173 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4172]
theorem aligned4172_4173 :
    AlignedValid 12 2 missing4172_4173 records4172_4173 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4172
    maskCheck4172 AlignedValid.nil

def missing4171_4173 : List (BitVec (edgeCount 12)) :=
  missing4171_4172 ++ missing4172_4173
abbrev records4171_4173 : List Blob :=
  records4171_4172 ++ records4172_4173
theorem aligned4171_4173 :
    AlignedValid 12 2 missing4171_4173 records4171_4173 :=
  aligned4171_4172.append aligned4172_4173

def missing4170_4173 : List (BitVec (edgeCount 12)) :=
  missing4170_4171 ++ missing4171_4173
abbrev records4170_4173 : List Blob :=
  records4170_4171 ++ records4171_4173
theorem aligned4170_4173 :
    AlignedValid 12 2 missing4170_4173 records4170_4173 :=
  aligned4170_4171.append aligned4171_4173

def missing4167_4173 : List (BitVec (edgeCount 12)) :=
  missing4167_4170 ++ missing4170_4173
abbrev records4167_4173 : List Blob :=
  records4167_4170 ++ records4170_4173
theorem aligned4167_4173 :
    AlignedValid 12 2 missing4167_4173 records4167_4173 :=
  aligned4167_4170.append aligned4170_4173

def missing4173_4174 : List (BitVec (edgeCount 12)) :=
  [missing4173]
abbrev records4173_4174 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4173]
theorem aligned4173_4174 :
    AlignedValid 12 2 missing4173_4174 records4173_4174 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4173
    maskCheck4173 AlignedValid.nil

def missing4174_4175 : List (BitVec (edgeCount 12)) :=
  [missing4174]
abbrev records4174_4175 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4174]
theorem aligned4174_4175 :
    AlignedValid 12 2 missing4174_4175 records4174_4175 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4174
    maskCheck4174 AlignedValid.nil

def missing4175_4176 : List (BitVec (edgeCount 12)) :=
  [missing4175]
abbrev records4175_4176 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4175]
theorem aligned4175_4176 :
    AlignedValid 12 2 missing4175_4176 records4175_4176 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4175
    maskCheck4175 AlignedValid.nil

def missing4174_4176 : List (BitVec (edgeCount 12)) :=
  missing4174_4175 ++ missing4175_4176
abbrev records4174_4176 : List Blob :=
  records4174_4175 ++ records4175_4176
theorem aligned4174_4176 :
    AlignedValid 12 2 missing4174_4176 records4174_4176 :=
  aligned4174_4175.append aligned4175_4176

def missing4173_4176 : List (BitVec (edgeCount 12)) :=
  missing4173_4174 ++ missing4174_4176
abbrev records4173_4176 : List Blob :=
  records4173_4174 ++ records4174_4176
theorem aligned4173_4176 :
    AlignedValid 12 2 missing4173_4176 records4173_4176 :=
  aligned4173_4174.append aligned4174_4176

def missing4176_4177 : List (BitVec (edgeCount 12)) :=
  [missing4176]
abbrev records4176_4177 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4176]
theorem aligned4176_4177 :
    AlignedValid 12 2 missing4176_4177 records4176_4177 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4176
    maskCheck4176 AlignedValid.nil

def missing4177_4178 : List (BitVec (edgeCount 12)) :=
  [missing4177]
abbrev records4177_4178 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4177]
theorem aligned4177_4178 :
    AlignedValid 12 2 missing4177_4178 records4177_4178 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4177
    maskCheck4177 AlignedValid.nil

def missing4178_4179 : List (BitVec (edgeCount 12)) :=
  [missing4178]
abbrev records4178_4179 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4178]
theorem aligned4178_4179 :
    AlignedValid 12 2 missing4178_4179 records4178_4179 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4178
    maskCheck4178 AlignedValid.nil

def missing4177_4179 : List (BitVec (edgeCount 12)) :=
  missing4177_4178 ++ missing4178_4179
abbrev records4177_4179 : List Blob :=
  records4177_4178 ++ records4178_4179
theorem aligned4177_4179 :
    AlignedValid 12 2 missing4177_4179 records4177_4179 :=
  aligned4177_4178.append aligned4178_4179

def missing4176_4179 : List (BitVec (edgeCount 12)) :=
  missing4176_4177 ++ missing4177_4179
abbrev records4176_4179 : List Blob :=
  records4176_4177 ++ records4177_4179
theorem aligned4176_4179 :
    AlignedValid 12 2 missing4176_4179 records4176_4179 :=
  aligned4176_4177.append aligned4177_4179

def missing4173_4179 : List (BitVec (edgeCount 12)) :=
  missing4173_4176 ++ missing4176_4179
abbrev records4173_4179 : List Blob :=
  records4173_4176 ++ records4176_4179
theorem aligned4173_4179 :
    AlignedValid 12 2 missing4173_4179 records4173_4179 :=
  aligned4173_4176.append aligned4176_4179

def missing4167_4179 : List (BitVec (edgeCount 12)) :=
  missing4167_4173 ++ missing4173_4179
abbrev records4167_4179 : List Blob :=
  records4167_4173 ++ records4173_4179
theorem aligned4167_4179 :
    AlignedValid 12 2 missing4167_4179 records4167_4179 :=
  aligned4167_4173.append aligned4173_4179

def missing4179_4180 : List (BitVec (edgeCount 12)) :=
  [missing4179]
abbrev records4179_4180 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4179]
theorem aligned4179_4180 :
    AlignedValid 12 2 missing4179_4180 records4179_4180 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4179
    maskCheck4179 AlignedValid.nil

def missing4180_4181 : List (BitVec (edgeCount 12)) :=
  [missing4180]
abbrev records4180_4181 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4180]
theorem aligned4180_4181 :
    AlignedValid 12 2 missing4180_4181 records4180_4181 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4180
    maskCheck4180 AlignedValid.nil

def missing4181_4182 : List (BitVec (edgeCount 12)) :=
  [missing4181]
abbrev records4181_4182 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4181]
theorem aligned4181_4182 :
    AlignedValid 12 2 missing4181_4182 records4181_4182 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4181
    maskCheck4181 AlignedValid.nil

def missing4180_4182 : List (BitVec (edgeCount 12)) :=
  missing4180_4181 ++ missing4181_4182
abbrev records4180_4182 : List Blob :=
  records4180_4181 ++ records4181_4182
theorem aligned4180_4182 :
    AlignedValid 12 2 missing4180_4182 records4180_4182 :=
  aligned4180_4181.append aligned4181_4182

def missing4179_4182 : List (BitVec (edgeCount 12)) :=
  missing4179_4180 ++ missing4180_4182
abbrev records4179_4182 : List Blob :=
  records4179_4180 ++ records4180_4182
theorem aligned4179_4182 :
    AlignedValid 12 2 missing4179_4182 records4179_4182 :=
  aligned4179_4180.append aligned4180_4182

def missing4182_4183 : List (BitVec (edgeCount 12)) :=
  [missing4182]
abbrev records4182_4183 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4182]
theorem aligned4182_4183 :
    AlignedValid 12 2 missing4182_4183 records4182_4183 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4182
    maskCheck4182 AlignedValid.nil

def missing4183_4184 : List (BitVec (edgeCount 12)) :=
  [missing4183]
abbrev records4183_4184 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4183]
theorem aligned4183_4184 :
    AlignedValid 12 2 missing4183_4184 records4183_4184 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4183
    maskCheck4183 AlignedValid.nil

def missing4184_4185 : List (BitVec (edgeCount 12)) :=
  [missing4184]
abbrev records4184_4185 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4184]
theorem aligned4184_4185 :
    AlignedValid 12 2 missing4184_4185 records4184_4185 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4184
    maskCheck4184 AlignedValid.nil

def missing4183_4185 : List (BitVec (edgeCount 12)) :=
  missing4183_4184 ++ missing4184_4185
abbrev records4183_4185 : List Blob :=
  records4183_4184 ++ records4184_4185
theorem aligned4183_4185 :
    AlignedValid 12 2 missing4183_4185 records4183_4185 :=
  aligned4183_4184.append aligned4184_4185

def missing4182_4185 : List (BitVec (edgeCount 12)) :=
  missing4182_4183 ++ missing4183_4185
abbrev records4182_4185 : List Blob :=
  records4182_4183 ++ records4183_4185
theorem aligned4182_4185 :
    AlignedValid 12 2 missing4182_4185 records4182_4185 :=
  aligned4182_4183.append aligned4183_4185

def missing4179_4185 : List (BitVec (edgeCount 12)) :=
  missing4179_4182 ++ missing4182_4185
abbrev records4179_4185 : List Blob :=
  records4179_4182 ++ records4182_4185
theorem aligned4179_4185 :
    AlignedValid 12 2 missing4179_4185 records4179_4185 :=
  aligned4179_4182.append aligned4182_4185

def missing4185_4186 : List (BitVec (edgeCount 12)) :=
  [missing4185]
abbrev records4185_4186 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4185]
theorem aligned4185_4186 :
    AlignedValid 12 2 missing4185_4186 records4185_4186 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4185
    maskCheck4185 AlignedValid.nil

def missing4186_4187 : List (BitVec (edgeCount 12)) :=
  [missing4186]
abbrev records4186_4187 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4186]
theorem aligned4186_4187 :
    AlignedValid 12 2 missing4186_4187 records4186_4187 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4186
    maskCheck4186 AlignedValid.nil

def missing4187_4188 : List (BitVec (edgeCount 12)) :=
  [missing4187]
abbrev records4187_4188 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4187]
theorem aligned4187_4188 :
    AlignedValid 12 2 missing4187_4188 records4187_4188 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4187
    maskCheck4187 AlignedValid.nil

def missing4186_4188 : List (BitVec (edgeCount 12)) :=
  missing4186_4187 ++ missing4187_4188
abbrev records4186_4188 : List Blob :=
  records4186_4187 ++ records4187_4188
theorem aligned4186_4188 :
    AlignedValid 12 2 missing4186_4188 records4186_4188 :=
  aligned4186_4187.append aligned4187_4188

def missing4185_4188 : List (BitVec (edgeCount 12)) :=
  missing4185_4186 ++ missing4186_4188
abbrev records4185_4188 : List Blob :=
  records4185_4186 ++ records4186_4188
theorem aligned4185_4188 :
    AlignedValid 12 2 missing4185_4188 records4185_4188 :=
  aligned4185_4186.append aligned4186_4188

def missing4188_4189 : List (BitVec (edgeCount 12)) :=
  [missing4188]
abbrev records4188_4189 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4188]
theorem aligned4188_4189 :
    AlignedValid 12 2 missing4188_4189 records4188_4189 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4188
    maskCheck4188 AlignedValid.nil

def missing4189_4190 : List (BitVec (edgeCount 12)) :=
  [missing4189]
abbrev records4189_4190 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4189]
theorem aligned4189_4190 :
    AlignedValid 12 2 missing4189_4190 records4189_4190 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4189
    maskCheck4189 AlignedValid.nil

def missing4190_4191 : List (BitVec (edgeCount 12)) :=
  [missing4190]
abbrev records4190_4191 : List Blob :=
  [StrongPackedBucketN12A2Shard032.record4190]
theorem aligned4190_4191 :
    AlignedValid 12 2 missing4190_4191 records4190_4191 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A2Shard032.check4190
    maskCheck4190 AlignedValid.nil

def missing4189_4191 : List (BitVec (edgeCount 12)) :=
  missing4189_4190 ++ missing4190_4191
abbrev records4189_4191 : List Blob :=
  records4189_4190 ++ records4190_4191
theorem aligned4189_4191 :
    AlignedValid 12 2 missing4189_4191 records4189_4191 :=
  aligned4189_4190.append aligned4190_4191

def missing4188_4191 : List (BitVec (edgeCount 12)) :=
  missing4188_4189 ++ missing4189_4191
abbrev records4188_4191 : List Blob :=
  records4188_4189 ++ records4189_4191
theorem aligned4188_4191 :
    AlignedValid 12 2 missing4188_4191 records4188_4191 :=
  aligned4188_4189.append aligned4189_4191

def missing4185_4191 : List (BitVec (edgeCount 12)) :=
  missing4185_4188 ++ missing4188_4191
abbrev records4185_4191 : List Blob :=
  records4185_4188 ++ records4188_4191
theorem aligned4185_4191 :
    AlignedValid 12 2 missing4185_4191 records4185_4191 :=
  aligned4185_4188.append aligned4188_4191

def missing4179_4191 : List (BitVec (edgeCount 12)) :=
  missing4179_4185 ++ missing4185_4191
abbrev records4179_4191 : List Blob :=
  records4179_4185 ++ records4185_4191
theorem aligned4179_4191 :
    AlignedValid 12 2 missing4179_4191 records4179_4191 :=
  aligned4179_4185.append aligned4185_4191

def missing4167_4191 : List (BitVec (edgeCount 12)) :=
  missing4167_4179 ++ missing4179_4191
abbrev records4167_4191 : List Blob :=
  records4167_4179 ++ records4179_4191
theorem aligned4167_4191 :
    AlignedValid 12 2 missing4167_4191 records4167_4191 :=
  aligned4167_4179.append aligned4179_4191

def missing4143_4191 : List (BitVec (edgeCount 12)) :=
  missing4143_4167 ++ missing4167_4191
abbrev records4143_4191 : List Blob :=
  records4143_4167 ++ records4167_4191
theorem aligned4143_4191 :
    AlignedValid 12 2 missing4143_4191 records4143_4191 :=
  aligned4143_4167.append aligned4167_4191

def missing4096_4191 : List (BitVec (edgeCount 12)) :=
  missing4096_4143 ++ missing4143_4191
abbrev records4096_4191 : List Blob :=
  records4096_4143 ++ records4143_4191
theorem aligned4096_4191 :
    AlignedValid 12 2 missing4096_4191 records4096_4191 :=
  aligned4096_4143.append aligned4143_4191

abbrev missing : List (BitVec (edgeCount 12)) := missing4096_4191
abbrev records : List Blob := records4096_4191
theorem aligned : AlignedValid 12 2 missing records := aligned4096_4191

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A2AlignedShard032
