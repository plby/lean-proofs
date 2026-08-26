/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard040

/-! Decode-only alignment checks for n=12, a=4, records 5120--5247. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard040

open PackedBucketCertificate

def missing5120 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28067312968379924480
theorem maskCheck5120 :
    checkMaskFor missing5120 StrongPackedBucketN12A4Shard040.record5120 = true := by
  decide

def missing5121 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28175399359436816384
theorem maskCheck5121 :
    checkMaskFor missing5121 StrongPackedBucketN12A4Shard040.record5121 = true := by
  decide

def missing5122 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28571716126645420032
theorem maskCheck5122 :
    checkMaskFor missing5122 StrongPackedBucketN12A4Shard040.record5122 = true := by
  decide

def missing5123 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28607744923664384000
theorem maskCheck5123 :
    checkMaskFor missing5123 StrongPackedBucketN12A4Shard040.record5123 = true := by
  decide

def missing5124 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28932004096835059712
theorem maskCheck5124 :
    checkMaskFor missing5124 StrongPackedBucketN12A4Shard040.record5124 = true := by
  decide

def missing5125 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29040090487891951616
theorem maskCheck5125 :
    checkMaskFor missing5125 StrongPackedBucketN12A4Shard040.record5125 = true := by
  decide

def missing5126 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29148176878948843520
theorem maskCheck5126 :
    checkMaskFor missing5126 StrongPackedBucketN12A4Shard040.record5126 = true := by
  decide

def missing5127 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29184205675967807488
theorem maskCheck5127 :
    checkMaskFor missing5127 StrongPackedBucketN12A4Shard040.record5127 = true := by
  decide

def missing5128 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29688608834233303040
theorem maskCheck5128 :
    checkMaskFor missing5128 StrongPackedBucketN12A4Shard040.record5128 = true := by
  decide

def missing5129 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 31165789512010825728
theorem maskCheck5129 :
    checkMaskFor missing5129 StrongPackedBucketN12A4Shard040.record5129 = true := by
  decide

def missing5130 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 31201818309029789696
theorem maskCheck5130 :
    checkMaskFor missing5130 StrongPackedBucketN12A4Shard040.record5130 = true := by
  decide

def missing5131 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 31417991091143573504
theorem maskCheck5131 :
    checkMaskFor missing5131 StrongPackedBucketN12A4Shard040.record5131 = true := by
  decide

def missing5132 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 35741446733419249664
theorem maskCheck5132 :
    checkMaskFor missing5132 StrongPackedBucketN12A4Shard040.record5132 = true := by
  decide

def missing5133 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55593313890868396032
theorem maskCheck5133 :
    checkMaskFor missing5133 StrongPackedBucketN12A4Shard040.record5133 = true := by
  decide

def missing5134 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55737429078944251904
theorem maskCheck5134 :
    checkMaskFor missing5134 StrongPackedBucketN12A4Shard040.record5134 = true := by
  decide

def missing5135 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55845515470001143808
theorem maskCheck5135 :
    checkMaskFor missing5135 StrongPackedBucketN12A4Shard040.record5135 = true := by
  decide

def missing5136 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56602120207399387136
theorem maskCheck5136 :
    checkMaskFor missing5136 StrongPackedBucketN12A4Shard040.record5136 = true := by
  decide

def missing5137 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56710206598456279040
theorem maskCheck5137 :
    checkMaskFor missing5137 StrongPackedBucketN12A4Shard040.record5137 = true := by
  decide

def missing5138 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56854321786532134912
theorem maskCheck5138 :
    checkMaskFor missing5138 StrongPackedBucketN12A4Shard040.record5138 = true := by
  decide

def missing5139 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58835905622575153152
theorem maskCheck5139 :
    checkMaskFor missing5139 StrongPackedBucketN12A4Shard040.record5139 = true := by
  decide

def missing5140 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58871934419594117120
theorem maskCheck5140 :
    checkMaskFor missing5140 StrongPackedBucketN12A4Shard040.record5140 = true := by
  decide

def missing5141 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 63411562843983577088
theorem maskCheck5141 :
    checkMaskFor missing5141 StrongPackedBucketN12A4Shard040.record5141 = true := by
  decide

def missing5142 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64672570739647315968
theorem maskCheck5142 :
    checkMaskFor missing5142 StrongPackedBucketN12A4Shard040.record5142 = true := by
  decide

def missing5143 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64780657130704207872
theorem maskCheck5143 :
    checkMaskFor missing5143 StrongPackedBucketN12A4Shard040.record5143 = true := by
  decide

def missing5144 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64924772318780063744
theorem maskCheck5144 :
    checkMaskFor missing5144 StrongPackedBucketN12A4Shard040.record5144 = true := by
  decide

def missing5145 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65753434650216235008
theorem maskCheck5145 :
    checkMaskFor missing5145 StrongPackedBucketN12A4Shard040.record5145 = true := by
  decide

def missing5146 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65789463447235198976
theorem maskCheck5146 :
    checkMaskFor missing5146 StrongPackedBucketN12A4Shard040.record5146 = true := by
  decide

def missing5147 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 68023248862410964992
theorem maskCheck5147 :
    checkMaskFor missing5147 StrongPackedBucketN12A4Shard040.record5147 = true := by
  decide

def missing5148 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1126111494379929600
theorem maskCheck5148 :
    checkMaskFor missing5148 StrongPackedBucketN12A4Shard040.record5148 = true := by
  decide

def missing5149 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2134917810910920704
theorem maskCheck5149 :
    checkMaskFor missing5149 StrongPackedBucketN12A4Shard040.record5149 = true := by
  decide

def missing5150 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2243004201967812608
theorem maskCheck5150 :
    checkMaskFor missing5150 StrongPackedBucketN12A4Shard040.record5150 = true := by
  decide

def missing5151 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4368703226086686720
theorem maskCheck5151 :
    checkMaskFor missing5151 StrongPackedBucketN12A4Shard040.record5151 = true := by
  decide

def missing5152 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4404732023105650688
theorem maskCheck5152 :
    checkMaskFor missing5152 StrongPackedBucketN12A4Shard040.record5152 = true := by
  decide

def missing5153 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8944360447495110656
theorem maskCheck5153 :
    checkMaskFor missing5153 StrongPackedBucketN12A4Shard040.record5153 = true := by
  decide

def missing5154 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9773022778931281920
theorem maskCheck5154 :
    checkMaskFor missing5154 StrongPackedBucketN12A4Shard040.record5154 = true := by
  decide

def missing5155 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10205368343158849536
theorem maskCheck5155 :
    checkMaskFor missing5155 StrongPackedBucketN12A4Shard040.record5155 = true := by
  decide

def missing5156 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11286232253727768576
theorem maskCheck5156 :
    checkMaskFor missing5156 StrongPackedBucketN12A4Shard040.record5156 = true := by
  decide

def missing5157 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18996394815786057728
theorem maskCheck5157 :
    checkMaskFor missing5157 StrongPackedBucketN12A4Shard040.record5157 = true := by
  decide

def missing5158 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19428740380013625344
theorem maskCheck5158 :
    checkMaskFor missing5158 StrongPackedBucketN12A4Shard040.record5158 = true := by
  decide

def missing5159 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19536826771070517248
theorem maskCheck5159 :
    checkMaskFor missing5159 StrongPackedBucketN12A4Shard040.record5159 = true := by
  decide

def missing5160 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20509604290582544384
theorem maskCheck5160 :
    checkMaskFor missing5160 StrongPackedBucketN12A4Shard040.record5160 = true := by
  decide

def missing5161 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20545633087601508352
theorem maskCheck5161 :
    checkMaskFor missing5161 StrongPackedBucketN12A4Shard040.record5161 = true := by
  decide

def missing5162 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22779418502777274368
theorem maskCheck5162 :
    checkMaskFor missing5162 StrongPackedBucketN12A4Shard040.record5162 = true := by
  decide

def missing5163 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27931536476489121792
theorem maskCheck5163 :
    checkMaskFor missing5163 StrongPackedBucketN12A4Shard040.record5163 = true := by
  decide

def missing5164 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28075651664564977664
theorem maskCheck5164 :
    checkMaskFor missing5164 StrongPackedBucketN12A4Shard040.record5164 = true := by
  decide

def missing5165 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28183738055621869568
theorem maskCheck5165 :
    checkMaskFor missing5165 StrongPackedBucketN12A4Shard040.record5165 = true := by
  decide

def missing5166 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28580054822830473216
theorem maskCheck5166 :
    checkMaskFor missing5166 StrongPackedBucketN12A4Shard040.record5166 = true := by
  decide

def missing5167 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28616083619849437184
theorem maskCheck5167 :
    checkMaskFor missing5167 StrongPackedBucketN12A4Shard040.record5167 = true := by
  decide

def missing5168 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29696947530418356224
theorem maskCheck5168 :
    checkMaskFor missing5168 StrongPackedBucketN12A4Shard040.record5168 = true := by
  decide

def missing5169 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55601652587053449216
theorem maskCheck5169 :
    checkMaskFor missing5169 StrongPackedBucketN12A4Shard040.record5169 = true := by
  decide

def missing5170 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55745767775129305088
theorem maskCheck5170 :
    checkMaskFor missing5170 StrongPackedBucketN12A4Shard040.record5170 = true := by
  decide

def missing5171 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55853854166186196992
theorem maskCheck5171 :
    checkMaskFor missing5171 StrongPackedBucketN12A4Shard040.record5171 = true := by
  decide

def missing5172 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56250170933394800640
theorem maskCheck5172 :
    checkMaskFor missing5172 StrongPackedBucketN12A4Shard040.record5172 = true := by
  decide

def missing5173 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56286199730413764608
theorem maskCheck5173 :
    checkMaskFor missing5173 StrongPackedBucketN12A4Shard040.record5173 = true := by
  decide

def missing5174 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57367063640982683648
theorem maskCheck5174 :
    checkMaskFor missing5174 StrongPackedBucketN12A4Shard040.record5174 = true := by
  decide

def missing5175 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64680909435832369152
theorem maskCheck5175 :
    checkMaskFor missing5175 StrongPackedBucketN12A4Shard040.record5175 = true := by
  decide

def missing5176 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64897082217946152960
theorem maskCheck5176 :
    checkMaskFor missing5176 StrongPackedBucketN12A4Shard040.record5176 = true := by
  decide

def missing5177 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1126252231868284928
theorem maskCheck5177 :
    checkMaskFor missing5177 StrongPackedBucketN12A4Shard040.record5177 = true := by
  decide

def missing5178 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1990943360323420160
theorem maskCheck5178 :
    checkMaskFor missing5178 StrongPackedBucketN12A4Shard040.record5178 = true := by
  decide

def missing5179 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2135058548399276032
theorem maskCheck5179 :
    checkMaskFor missing5179 StrongPackedBucketN12A4Shard040.record5179 = true := by
  decide

def missing5180 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2207116142437203968
theorem maskCheck5180 :
    checkMaskFor missing5180 StrongPackedBucketN12A4Shard040.record5180 = true := by
  decide

def missing5181 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2243144939456167936
theorem maskCheck5181 :
    checkMaskFor missing5181 StrongPackedBucketN12A4Shard040.record5181 = true := by
  decide

def missing5182 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4152671181461258240
theorem maskCheck5182 :
    checkMaskFor missing5182 StrongPackedBucketN12A4Shard040.record5182 = true := by
  decide

def missing5183 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4224728775499186176
theorem maskCheck5183 :
    checkMaskFor missing5183 StrongPackedBucketN12A4Shard040.record5183 = true := by
  decide

def missing5184 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4260757572518150144
theorem maskCheck5184 :
    checkMaskFor missing5184 StrongPackedBucketN12A4Shard040.record5184 = true := by
  decide

def missing5185 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4368843963575042048
theorem maskCheck5185 :
    checkMaskFor missing5185 StrongPackedBucketN12A4Shard040.record5185 = true := by
  decide

def missing5186 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4476930354631933952
theorem maskCheck5186 :
    checkMaskFor missing5186 StrongPackedBucketN12A4Shard040.record5186 = true := by
  decide

def missing5187 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8692299605850718208
theorem maskCheck5187 :
    checkMaskFor missing5187 StrongPackedBucketN12A4Shard040.record5187 = true := by
  decide

def missing5188 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8728328402869682176
theorem maskCheck5188 :
    checkMaskFor missing5188 StrongPackedBucketN12A4Shard040.record5188 = true := by
  decide

def missing5189 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8800385996907610112
theorem maskCheck5189 :
    checkMaskFor missing5189 StrongPackedBucketN12A4Shard040.record5189 = true := by
  decide

def missing5190 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9773163516419637248
theorem maskCheck5190 :
    checkMaskFor missing5190 StrongPackedBucketN12A4Shard040.record5190 = true := by
  decide

def missing5191 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10061393892571348992
theorem maskCheck5191 :
    checkMaskFor missing5191 StrongPackedBucketN12A4Shard040.record5191 = true := by
  decide

def missing5192 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10277566674685132800
theorem maskCheck5192 :
    checkMaskFor missing5192 StrongPackedBucketN12A4Shard040.record5192 = true := by
  decide

def missing5193 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11070200209102340096
theorem maskCheck5193 :
    checkMaskFor missing5193 StrongPackedBucketN12A4Shard040.record5193 = true := by
  decide

def missing5194 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11142257803140268032
theorem maskCheck5194 :
    checkMaskFor missing5194 StrongPackedBucketN12A4Shard040.record5194 = true := by
  decide

def missing5195 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13303985624278106112
theorem maskCheck5195 :
    checkMaskFor missing5195 StrongPackedBucketN12A4Shard040.record5195 = true := by
  decide

def missing5196 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18996535553274413056
theorem maskCheck5196 :
    checkMaskFor missing5196 StrongPackedBucketN12A4Shard040.record5196 = true := by
  decide

def missing5197 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19284765929426124800
theorem maskCheck5197 :
    checkMaskFor missing5197 StrongPackedBucketN12A4Shard040.record5197 = true := by
  decide

def missing5198 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19428881117501980672
theorem maskCheck5198 :
    checkMaskFor missing5198 StrongPackedBucketN12A4Shard040.record5198 = true := by
  decide

def missing5199 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19500938711539908608
theorem maskCheck5199 :
    checkMaskFor missing5199 StrongPackedBucketN12A4Shard040.record5199 = true := by
  decide

def missing5200 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19536967508558872576
theorem maskCheck5200 :
    checkMaskFor missing5200 StrongPackedBucketN12A4Shard040.record5200 = true := by
  decide

def missing5201 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20293572245957115904
theorem maskCheck5201 :
    checkMaskFor missing5201 StrongPackedBucketN12A4Shard040.record5201 = true := by
  decide

def missing5202 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20365629839995043840
theorem maskCheck5202 :
    checkMaskFor missing5202 StrongPackedBucketN12A4Shard040.record5202 = true := by
  decide

def missing5203 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20401658637014007808
theorem maskCheck5203 :
    checkMaskFor missing5203 StrongPackedBucketN12A4Shard040.record5203 = true := by
  decide

def missing5204 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20509745028070899712
theorem maskCheck5204 :
    checkMaskFor missing5204 StrongPackedBucketN12A4Shard040.record5204 = true := by
  decide

def missing5205 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20545773825089863680
theorem maskCheck5205 :
    checkMaskFor missing5205 StrongPackedBucketN12A4Shard040.record5205 = true := by
  decide

def missing5206 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20617831419127791616
theorem maskCheck5206 :
    checkMaskFor missing5206 StrongPackedBucketN12A4Shard040.record5206 = true := by
  decide

def missing5207 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22527357661132881920
theorem maskCheck5207 :
    checkMaskFor missing5207 StrongPackedBucketN12A4Shard040.record5207 = true := by
  decide

def missing5208 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22563386458151845888
theorem maskCheck5208 :
    checkMaskFor missing5208 StrongPackedBucketN12A4Shard040.record5208 = true := by
  decide

def missing5209 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22635444052189773824
theorem maskCheck5209 :
    checkMaskFor missing5209 StrongPackedBucketN12A4Shard040.record5209 = true := by
  decide

def missing5210 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22779559240265629696
theorem maskCheck5210 :
    checkMaskFor missing5210 StrongPackedBucketN12A4Shard040.record5210 = true := by
  decide

def missing5211 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27103014882541305856
theorem maskCheck5211 :
    checkMaskFor missing5211 StrongPackedBucketN12A4Shard040.record5211 = true := by
  decide

def missing5212 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27931677213977477120
theorem maskCheck5212 :
    checkMaskFor missing5212 StrongPackedBucketN12A4Shard040.record5212 = true := by
  decide

def missing5213 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28075792402053332992
theorem maskCheck5213 :
    checkMaskFor missing5213 StrongPackedBucketN12A4Shard040.record5213 = true := by
  decide

def missing5214 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28147849996091260928
theorem maskCheck5214 :
    checkMaskFor missing5214 StrongPackedBucketN12A4Shard040.record5214 = true := by
  decide

def missing5215 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28183878793110224896
theorem maskCheck5215 :
    checkMaskFor missing5215 StrongPackedBucketN12A4Shard040.record5215 = true := by
  decide

def missing5216 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28364022778205044736
theorem maskCheck5216 :
    checkMaskFor missing5216 StrongPackedBucketN12A4Shard040.record5216 = true := by
  decide

def missing5217 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28436080372242972672
theorem maskCheck5217 :
    checkMaskFor missing5217 StrongPackedBucketN12A4Shard040.record5217 = true := by
  decide

def missing5218 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28472109169261936640
theorem maskCheck5218 :
    checkMaskFor missing5218 StrongPackedBucketN12A4Shard040.record5218 = true := by
  decide

def missing5219 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28580195560318828544
theorem maskCheck5219 :
    checkMaskFor missing5219 StrongPackedBucketN12A4Shard040.record5219 = true := by
  decide

def missing5220 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28616224357337792512
theorem maskCheck5220 :
    checkMaskFor missing5220 StrongPackedBucketN12A4Shard040.record5220 = true := by
  decide

def missing5221 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28688281951375720448
theorem maskCheck5221 :
    checkMaskFor missing5221 StrongPackedBucketN12A4Shard040.record5221 = true := by
  decide

def missing5222 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29444886688773963776
theorem maskCheck5222 :
    checkMaskFor missing5222 StrongPackedBucketN12A4Shard040.record5222 = true := by
  decide

def missing5223 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29480915485792927744
theorem maskCheck5223 :
    checkMaskFor missing5223 StrongPackedBucketN12A4Shard040.record5223 = true := by
  decide

def missing5224 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29552973079830855680
theorem maskCheck5224 :
    checkMaskFor missing5224 StrongPackedBucketN12A4Shard040.record5224 = true := by
  decide

def missing5225 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29697088267906711552
theorem maskCheck5225 :
    checkMaskFor missing5225 StrongPackedBucketN12A4Shard040.record5225 = true := by
  decide

def missing5226 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 31714700900968693760
theorem maskCheck5226 :
    checkMaskFor missing5226 StrongPackedBucketN12A4Shard040.record5226 = true := by
  decide

def missing5227 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55601793324541804544
theorem maskCheck5227 :
    checkMaskFor missing5227 StrongPackedBucketN12A4Shard040.record5227 = true := by
  decide

def missing5228 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55745908512617660416
theorem maskCheck5228 :
    checkMaskFor missing5228 StrongPackedBucketN12A4Shard040.record5228 = true := by
  decide

def missing5229 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55817966106655588352
theorem maskCheck5229 :
    checkMaskFor missing5229 StrongPackedBucketN12A4Shard040.record5229 = true := by
  decide

def missing5230 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55853994903674552320
theorem maskCheck5230 :
    checkMaskFor missing5230 StrongPackedBucketN12A4Shard040.record5230 = true := by
  decide

def missing5231 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56034138888769372160
theorem maskCheck5231 :
    checkMaskFor missing5231 StrongPackedBucketN12A4Shard040.record5231 = true := by
  decide

def missing5232 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56106196482807300096
theorem maskCheck5232 :
    checkMaskFor missing5232 StrongPackedBucketN12A4Shard040.record5232 = true := by
  decide

def missing5233 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56142225279826264064
theorem maskCheck5233 :
    checkMaskFor missing5233 StrongPackedBucketN12A4Shard040.record5233 = true := by
  decide

def missing5234 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56250311670883155968
theorem maskCheck5234 :
    checkMaskFor missing5234 StrongPackedBucketN12A4Shard040.record5234 = true := by
  decide

def missing5235 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56358398061940047872
theorem maskCheck5235 :
    checkMaskFor missing5235 StrongPackedBucketN12A4Shard040.record5235 = true := by
  decide

def missing5236 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57115002799338291200
theorem maskCheck5236 :
    checkMaskFor missing5236 StrongPackedBucketN12A4Shard040.record5236 = true := by
  decide

def missing5237 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57151031596357255168
theorem maskCheck5237 :
    checkMaskFor missing5237 StrongPackedBucketN12A4Shard040.record5237 = true := by
  decide

def missing5238 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57223089190395183104
theorem maskCheck5238 :
    checkMaskFor missing5238 StrongPackedBucketN12A4Shard040.record5238 = true := by
  decide

def missing5239 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59384817011533021184
theorem maskCheck5239 :
    checkMaskFor missing5239 StrongPackedBucketN12A4Shard040.record5239 = true := by
  decide

def missing5240 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64681050173320724480
theorem maskCheck5240 :
    checkMaskFor missing5240 StrongPackedBucketN12A4Shard040.record5240 = true := by
  decide

def missing5241 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64753107767358652416
theorem maskCheck5241 :
    checkMaskFor missing5241 StrongPackedBucketN12A4Shard040.record5241 = true := by
  decide

def missing5242 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65185453331586220032
theorem maskCheck5242 :
    checkMaskFor missing5242 StrongPackedBucketN12A4Shard040.record5242 = true := by
  decide

def missing5243 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1126744813077528576
theorem maskCheck5243 :
    checkMaskFor missing5243 StrongPackedBucketN12A4Shard040.record5243 = true := by
  decide

def missing5244 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1703205565380952064
theorem maskCheck5244 :
    checkMaskFor missing5244 StrongPackedBucketN12A4Shard040.record5244 = true := by
  decide

def missing5245 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2135551129608519680
theorem maskCheck5245 :
    checkMaskFor missing5245 StrongPackedBucketN12A4Shard040.record5245 = true := by
  decide

def missing5246 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2243637520665411584
theorem maskCheck5246 :
    checkMaskFor missing5246 StrongPackedBucketN12A4Shard040.record5246 = true := by
  decide

def missing5247 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3720818198442934272
theorem maskCheck5247 :
    checkMaskFor missing5247 StrongPackedBucketN12A4Shard040.record5247 = true := by
  decide

def missing5120_5121 : List (BitVec (edgeCount 12)) :=
  [missing5120]
abbrev records5120_5121 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5120]
theorem aligned5120_5121 :
    AlignedValid 12 4 missing5120_5121 records5120_5121 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5120
    maskCheck5120 AlignedValid.nil

def missing5121_5122 : List (BitVec (edgeCount 12)) :=
  [missing5121]
abbrev records5121_5122 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5121]
theorem aligned5121_5122 :
    AlignedValid 12 4 missing5121_5122 records5121_5122 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5121
    maskCheck5121 AlignedValid.nil

def missing5120_5122 : List (BitVec (edgeCount 12)) :=
  missing5120_5121 ++ missing5121_5122
abbrev records5120_5122 : List Blob :=
  records5120_5121 ++ records5121_5122
theorem aligned5120_5122 :
    AlignedValid 12 4 missing5120_5122 records5120_5122 :=
  aligned5120_5121.append aligned5121_5122

def missing5122_5123 : List (BitVec (edgeCount 12)) :=
  [missing5122]
abbrev records5122_5123 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5122]
theorem aligned5122_5123 :
    AlignedValid 12 4 missing5122_5123 records5122_5123 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5122
    maskCheck5122 AlignedValid.nil

def missing5123_5124 : List (BitVec (edgeCount 12)) :=
  [missing5123]
abbrev records5123_5124 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5123]
theorem aligned5123_5124 :
    AlignedValid 12 4 missing5123_5124 records5123_5124 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5123
    maskCheck5123 AlignedValid.nil

def missing5122_5124 : List (BitVec (edgeCount 12)) :=
  missing5122_5123 ++ missing5123_5124
abbrev records5122_5124 : List Blob :=
  records5122_5123 ++ records5123_5124
theorem aligned5122_5124 :
    AlignedValid 12 4 missing5122_5124 records5122_5124 :=
  aligned5122_5123.append aligned5123_5124

def missing5120_5124 : List (BitVec (edgeCount 12)) :=
  missing5120_5122 ++ missing5122_5124
abbrev records5120_5124 : List Blob :=
  records5120_5122 ++ records5122_5124
theorem aligned5120_5124 :
    AlignedValid 12 4 missing5120_5124 records5120_5124 :=
  aligned5120_5122.append aligned5122_5124

def missing5124_5125 : List (BitVec (edgeCount 12)) :=
  [missing5124]
abbrev records5124_5125 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5124]
theorem aligned5124_5125 :
    AlignedValid 12 4 missing5124_5125 records5124_5125 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5124
    maskCheck5124 AlignedValid.nil

def missing5125_5126 : List (BitVec (edgeCount 12)) :=
  [missing5125]
abbrev records5125_5126 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5125]
theorem aligned5125_5126 :
    AlignedValid 12 4 missing5125_5126 records5125_5126 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5125
    maskCheck5125 AlignedValid.nil

def missing5124_5126 : List (BitVec (edgeCount 12)) :=
  missing5124_5125 ++ missing5125_5126
abbrev records5124_5126 : List Blob :=
  records5124_5125 ++ records5125_5126
theorem aligned5124_5126 :
    AlignedValid 12 4 missing5124_5126 records5124_5126 :=
  aligned5124_5125.append aligned5125_5126

def missing5126_5127 : List (BitVec (edgeCount 12)) :=
  [missing5126]
abbrev records5126_5127 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5126]
theorem aligned5126_5127 :
    AlignedValid 12 4 missing5126_5127 records5126_5127 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5126
    maskCheck5126 AlignedValid.nil

def missing5127_5128 : List (BitVec (edgeCount 12)) :=
  [missing5127]
abbrev records5127_5128 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5127]
theorem aligned5127_5128 :
    AlignedValid 12 4 missing5127_5128 records5127_5128 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5127
    maskCheck5127 AlignedValid.nil

def missing5126_5128 : List (BitVec (edgeCount 12)) :=
  missing5126_5127 ++ missing5127_5128
abbrev records5126_5128 : List Blob :=
  records5126_5127 ++ records5127_5128
theorem aligned5126_5128 :
    AlignedValid 12 4 missing5126_5128 records5126_5128 :=
  aligned5126_5127.append aligned5127_5128

def missing5124_5128 : List (BitVec (edgeCount 12)) :=
  missing5124_5126 ++ missing5126_5128
abbrev records5124_5128 : List Blob :=
  records5124_5126 ++ records5126_5128
theorem aligned5124_5128 :
    AlignedValid 12 4 missing5124_5128 records5124_5128 :=
  aligned5124_5126.append aligned5126_5128

def missing5120_5128 : List (BitVec (edgeCount 12)) :=
  missing5120_5124 ++ missing5124_5128
abbrev records5120_5128 : List Blob :=
  records5120_5124 ++ records5124_5128
theorem aligned5120_5128 :
    AlignedValid 12 4 missing5120_5128 records5120_5128 :=
  aligned5120_5124.append aligned5124_5128

def missing5128_5129 : List (BitVec (edgeCount 12)) :=
  [missing5128]
abbrev records5128_5129 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5128]
theorem aligned5128_5129 :
    AlignedValid 12 4 missing5128_5129 records5128_5129 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5128
    maskCheck5128 AlignedValid.nil

def missing5129_5130 : List (BitVec (edgeCount 12)) :=
  [missing5129]
abbrev records5129_5130 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5129]
theorem aligned5129_5130 :
    AlignedValid 12 4 missing5129_5130 records5129_5130 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5129
    maskCheck5129 AlignedValid.nil

def missing5128_5130 : List (BitVec (edgeCount 12)) :=
  missing5128_5129 ++ missing5129_5130
abbrev records5128_5130 : List Blob :=
  records5128_5129 ++ records5129_5130
theorem aligned5128_5130 :
    AlignedValid 12 4 missing5128_5130 records5128_5130 :=
  aligned5128_5129.append aligned5129_5130

def missing5130_5131 : List (BitVec (edgeCount 12)) :=
  [missing5130]
abbrev records5130_5131 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5130]
theorem aligned5130_5131 :
    AlignedValid 12 4 missing5130_5131 records5130_5131 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5130
    maskCheck5130 AlignedValid.nil

def missing5131_5132 : List (BitVec (edgeCount 12)) :=
  [missing5131]
abbrev records5131_5132 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5131]
theorem aligned5131_5132 :
    AlignedValid 12 4 missing5131_5132 records5131_5132 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5131
    maskCheck5131 AlignedValid.nil

def missing5130_5132 : List (BitVec (edgeCount 12)) :=
  missing5130_5131 ++ missing5131_5132
abbrev records5130_5132 : List Blob :=
  records5130_5131 ++ records5131_5132
theorem aligned5130_5132 :
    AlignedValid 12 4 missing5130_5132 records5130_5132 :=
  aligned5130_5131.append aligned5131_5132

def missing5128_5132 : List (BitVec (edgeCount 12)) :=
  missing5128_5130 ++ missing5130_5132
abbrev records5128_5132 : List Blob :=
  records5128_5130 ++ records5130_5132
theorem aligned5128_5132 :
    AlignedValid 12 4 missing5128_5132 records5128_5132 :=
  aligned5128_5130.append aligned5130_5132

def missing5132_5133 : List (BitVec (edgeCount 12)) :=
  [missing5132]
abbrev records5132_5133 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5132]
theorem aligned5132_5133 :
    AlignedValid 12 4 missing5132_5133 records5132_5133 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5132
    maskCheck5132 AlignedValid.nil

def missing5133_5134 : List (BitVec (edgeCount 12)) :=
  [missing5133]
abbrev records5133_5134 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5133]
theorem aligned5133_5134 :
    AlignedValid 12 4 missing5133_5134 records5133_5134 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5133
    maskCheck5133 AlignedValid.nil

def missing5132_5134 : List (BitVec (edgeCount 12)) :=
  missing5132_5133 ++ missing5133_5134
abbrev records5132_5134 : List Blob :=
  records5132_5133 ++ records5133_5134
theorem aligned5132_5134 :
    AlignedValid 12 4 missing5132_5134 records5132_5134 :=
  aligned5132_5133.append aligned5133_5134

def missing5134_5135 : List (BitVec (edgeCount 12)) :=
  [missing5134]
abbrev records5134_5135 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5134]
theorem aligned5134_5135 :
    AlignedValid 12 4 missing5134_5135 records5134_5135 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5134
    maskCheck5134 AlignedValid.nil

def missing5135_5136 : List (BitVec (edgeCount 12)) :=
  [missing5135]
abbrev records5135_5136 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5135]
theorem aligned5135_5136 :
    AlignedValid 12 4 missing5135_5136 records5135_5136 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5135
    maskCheck5135 AlignedValid.nil

def missing5134_5136 : List (BitVec (edgeCount 12)) :=
  missing5134_5135 ++ missing5135_5136
abbrev records5134_5136 : List Blob :=
  records5134_5135 ++ records5135_5136
theorem aligned5134_5136 :
    AlignedValid 12 4 missing5134_5136 records5134_5136 :=
  aligned5134_5135.append aligned5135_5136

def missing5132_5136 : List (BitVec (edgeCount 12)) :=
  missing5132_5134 ++ missing5134_5136
abbrev records5132_5136 : List Blob :=
  records5132_5134 ++ records5134_5136
theorem aligned5132_5136 :
    AlignedValid 12 4 missing5132_5136 records5132_5136 :=
  aligned5132_5134.append aligned5134_5136

def missing5128_5136 : List (BitVec (edgeCount 12)) :=
  missing5128_5132 ++ missing5132_5136
abbrev records5128_5136 : List Blob :=
  records5128_5132 ++ records5132_5136
theorem aligned5128_5136 :
    AlignedValid 12 4 missing5128_5136 records5128_5136 :=
  aligned5128_5132.append aligned5132_5136

def missing5120_5136 : List (BitVec (edgeCount 12)) :=
  missing5120_5128 ++ missing5128_5136
abbrev records5120_5136 : List Blob :=
  records5120_5128 ++ records5128_5136
theorem aligned5120_5136 :
    AlignedValid 12 4 missing5120_5136 records5120_5136 :=
  aligned5120_5128.append aligned5128_5136

def missing5136_5137 : List (BitVec (edgeCount 12)) :=
  [missing5136]
abbrev records5136_5137 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5136]
theorem aligned5136_5137 :
    AlignedValid 12 4 missing5136_5137 records5136_5137 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5136
    maskCheck5136 AlignedValid.nil

def missing5137_5138 : List (BitVec (edgeCount 12)) :=
  [missing5137]
abbrev records5137_5138 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5137]
theorem aligned5137_5138 :
    AlignedValid 12 4 missing5137_5138 records5137_5138 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5137
    maskCheck5137 AlignedValid.nil

def missing5136_5138 : List (BitVec (edgeCount 12)) :=
  missing5136_5137 ++ missing5137_5138
abbrev records5136_5138 : List Blob :=
  records5136_5137 ++ records5137_5138
theorem aligned5136_5138 :
    AlignedValid 12 4 missing5136_5138 records5136_5138 :=
  aligned5136_5137.append aligned5137_5138

def missing5138_5139 : List (BitVec (edgeCount 12)) :=
  [missing5138]
abbrev records5138_5139 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5138]
theorem aligned5138_5139 :
    AlignedValid 12 4 missing5138_5139 records5138_5139 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5138
    maskCheck5138 AlignedValid.nil

def missing5139_5140 : List (BitVec (edgeCount 12)) :=
  [missing5139]
abbrev records5139_5140 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5139]
theorem aligned5139_5140 :
    AlignedValid 12 4 missing5139_5140 records5139_5140 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5139
    maskCheck5139 AlignedValid.nil

def missing5138_5140 : List (BitVec (edgeCount 12)) :=
  missing5138_5139 ++ missing5139_5140
abbrev records5138_5140 : List Blob :=
  records5138_5139 ++ records5139_5140
theorem aligned5138_5140 :
    AlignedValid 12 4 missing5138_5140 records5138_5140 :=
  aligned5138_5139.append aligned5139_5140

def missing5136_5140 : List (BitVec (edgeCount 12)) :=
  missing5136_5138 ++ missing5138_5140
abbrev records5136_5140 : List Blob :=
  records5136_5138 ++ records5138_5140
theorem aligned5136_5140 :
    AlignedValid 12 4 missing5136_5140 records5136_5140 :=
  aligned5136_5138.append aligned5138_5140

def missing5140_5141 : List (BitVec (edgeCount 12)) :=
  [missing5140]
abbrev records5140_5141 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5140]
theorem aligned5140_5141 :
    AlignedValid 12 4 missing5140_5141 records5140_5141 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5140
    maskCheck5140 AlignedValid.nil

def missing5141_5142 : List (BitVec (edgeCount 12)) :=
  [missing5141]
abbrev records5141_5142 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5141]
theorem aligned5141_5142 :
    AlignedValid 12 4 missing5141_5142 records5141_5142 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5141
    maskCheck5141 AlignedValid.nil

def missing5140_5142 : List (BitVec (edgeCount 12)) :=
  missing5140_5141 ++ missing5141_5142
abbrev records5140_5142 : List Blob :=
  records5140_5141 ++ records5141_5142
theorem aligned5140_5142 :
    AlignedValid 12 4 missing5140_5142 records5140_5142 :=
  aligned5140_5141.append aligned5141_5142

def missing5142_5143 : List (BitVec (edgeCount 12)) :=
  [missing5142]
abbrev records5142_5143 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5142]
theorem aligned5142_5143 :
    AlignedValid 12 4 missing5142_5143 records5142_5143 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5142
    maskCheck5142 AlignedValid.nil

def missing5143_5144 : List (BitVec (edgeCount 12)) :=
  [missing5143]
abbrev records5143_5144 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5143]
theorem aligned5143_5144 :
    AlignedValid 12 4 missing5143_5144 records5143_5144 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5143
    maskCheck5143 AlignedValid.nil

def missing5142_5144 : List (BitVec (edgeCount 12)) :=
  missing5142_5143 ++ missing5143_5144
abbrev records5142_5144 : List Blob :=
  records5142_5143 ++ records5143_5144
theorem aligned5142_5144 :
    AlignedValid 12 4 missing5142_5144 records5142_5144 :=
  aligned5142_5143.append aligned5143_5144

def missing5140_5144 : List (BitVec (edgeCount 12)) :=
  missing5140_5142 ++ missing5142_5144
abbrev records5140_5144 : List Blob :=
  records5140_5142 ++ records5142_5144
theorem aligned5140_5144 :
    AlignedValid 12 4 missing5140_5144 records5140_5144 :=
  aligned5140_5142.append aligned5142_5144

def missing5136_5144 : List (BitVec (edgeCount 12)) :=
  missing5136_5140 ++ missing5140_5144
abbrev records5136_5144 : List Blob :=
  records5136_5140 ++ records5140_5144
theorem aligned5136_5144 :
    AlignedValid 12 4 missing5136_5144 records5136_5144 :=
  aligned5136_5140.append aligned5140_5144

def missing5144_5145 : List (BitVec (edgeCount 12)) :=
  [missing5144]
abbrev records5144_5145 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5144]
theorem aligned5144_5145 :
    AlignedValid 12 4 missing5144_5145 records5144_5145 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5144
    maskCheck5144 AlignedValid.nil

def missing5145_5146 : List (BitVec (edgeCount 12)) :=
  [missing5145]
abbrev records5145_5146 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5145]
theorem aligned5145_5146 :
    AlignedValid 12 4 missing5145_5146 records5145_5146 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5145
    maskCheck5145 AlignedValid.nil

def missing5144_5146 : List (BitVec (edgeCount 12)) :=
  missing5144_5145 ++ missing5145_5146
abbrev records5144_5146 : List Blob :=
  records5144_5145 ++ records5145_5146
theorem aligned5144_5146 :
    AlignedValid 12 4 missing5144_5146 records5144_5146 :=
  aligned5144_5145.append aligned5145_5146

def missing5146_5147 : List (BitVec (edgeCount 12)) :=
  [missing5146]
abbrev records5146_5147 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5146]
theorem aligned5146_5147 :
    AlignedValid 12 4 missing5146_5147 records5146_5147 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5146
    maskCheck5146 AlignedValid.nil

def missing5147_5148 : List (BitVec (edgeCount 12)) :=
  [missing5147]
abbrev records5147_5148 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5147]
theorem aligned5147_5148 :
    AlignedValid 12 4 missing5147_5148 records5147_5148 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5147
    maskCheck5147 AlignedValid.nil

def missing5146_5148 : List (BitVec (edgeCount 12)) :=
  missing5146_5147 ++ missing5147_5148
abbrev records5146_5148 : List Blob :=
  records5146_5147 ++ records5147_5148
theorem aligned5146_5148 :
    AlignedValid 12 4 missing5146_5148 records5146_5148 :=
  aligned5146_5147.append aligned5147_5148

def missing5144_5148 : List (BitVec (edgeCount 12)) :=
  missing5144_5146 ++ missing5146_5148
abbrev records5144_5148 : List Blob :=
  records5144_5146 ++ records5146_5148
theorem aligned5144_5148 :
    AlignedValid 12 4 missing5144_5148 records5144_5148 :=
  aligned5144_5146.append aligned5146_5148

def missing5148_5149 : List (BitVec (edgeCount 12)) :=
  [missing5148]
abbrev records5148_5149 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5148]
theorem aligned5148_5149 :
    AlignedValid 12 4 missing5148_5149 records5148_5149 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5148
    maskCheck5148 AlignedValid.nil

def missing5149_5150 : List (BitVec (edgeCount 12)) :=
  [missing5149]
abbrev records5149_5150 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5149]
theorem aligned5149_5150 :
    AlignedValid 12 4 missing5149_5150 records5149_5150 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5149
    maskCheck5149 AlignedValid.nil

def missing5148_5150 : List (BitVec (edgeCount 12)) :=
  missing5148_5149 ++ missing5149_5150
abbrev records5148_5150 : List Blob :=
  records5148_5149 ++ records5149_5150
theorem aligned5148_5150 :
    AlignedValid 12 4 missing5148_5150 records5148_5150 :=
  aligned5148_5149.append aligned5149_5150

def missing5150_5151 : List (BitVec (edgeCount 12)) :=
  [missing5150]
abbrev records5150_5151 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5150]
theorem aligned5150_5151 :
    AlignedValid 12 4 missing5150_5151 records5150_5151 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5150
    maskCheck5150 AlignedValid.nil

def missing5151_5152 : List (BitVec (edgeCount 12)) :=
  [missing5151]
abbrev records5151_5152 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5151]
theorem aligned5151_5152 :
    AlignedValid 12 4 missing5151_5152 records5151_5152 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5151
    maskCheck5151 AlignedValid.nil

def missing5150_5152 : List (BitVec (edgeCount 12)) :=
  missing5150_5151 ++ missing5151_5152
abbrev records5150_5152 : List Blob :=
  records5150_5151 ++ records5151_5152
theorem aligned5150_5152 :
    AlignedValid 12 4 missing5150_5152 records5150_5152 :=
  aligned5150_5151.append aligned5151_5152

def missing5148_5152 : List (BitVec (edgeCount 12)) :=
  missing5148_5150 ++ missing5150_5152
abbrev records5148_5152 : List Blob :=
  records5148_5150 ++ records5150_5152
theorem aligned5148_5152 :
    AlignedValid 12 4 missing5148_5152 records5148_5152 :=
  aligned5148_5150.append aligned5150_5152

def missing5144_5152 : List (BitVec (edgeCount 12)) :=
  missing5144_5148 ++ missing5148_5152
abbrev records5144_5152 : List Blob :=
  records5144_5148 ++ records5148_5152
theorem aligned5144_5152 :
    AlignedValid 12 4 missing5144_5152 records5144_5152 :=
  aligned5144_5148.append aligned5148_5152

def missing5136_5152 : List (BitVec (edgeCount 12)) :=
  missing5136_5144 ++ missing5144_5152
abbrev records5136_5152 : List Blob :=
  records5136_5144 ++ records5144_5152
theorem aligned5136_5152 :
    AlignedValid 12 4 missing5136_5152 records5136_5152 :=
  aligned5136_5144.append aligned5144_5152

def missing5120_5152 : List (BitVec (edgeCount 12)) :=
  missing5120_5136 ++ missing5136_5152
abbrev records5120_5152 : List Blob :=
  records5120_5136 ++ records5136_5152
theorem aligned5120_5152 :
    AlignedValid 12 4 missing5120_5152 records5120_5152 :=
  aligned5120_5136.append aligned5136_5152

def missing5152_5153 : List (BitVec (edgeCount 12)) :=
  [missing5152]
abbrev records5152_5153 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5152]
theorem aligned5152_5153 :
    AlignedValid 12 4 missing5152_5153 records5152_5153 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5152
    maskCheck5152 AlignedValid.nil

def missing5153_5154 : List (BitVec (edgeCount 12)) :=
  [missing5153]
abbrev records5153_5154 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5153]
theorem aligned5153_5154 :
    AlignedValid 12 4 missing5153_5154 records5153_5154 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5153
    maskCheck5153 AlignedValid.nil

def missing5152_5154 : List (BitVec (edgeCount 12)) :=
  missing5152_5153 ++ missing5153_5154
abbrev records5152_5154 : List Blob :=
  records5152_5153 ++ records5153_5154
theorem aligned5152_5154 :
    AlignedValid 12 4 missing5152_5154 records5152_5154 :=
  aligned5152_5153.append aligned5153_5154

def missing5154_5155 : List (BitVec (edgeCount 12)) :=
  [missing5154]
abbrev records5154_5155 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5154]
theorem aligned5154_5155 :
    AlignedValid 12 4 missing5154_5155 records5154_5155 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5154
    maskCheck5154 AlignedValid.nil

def missing5155_5156 : List (BitVec (edgeCount 12)) :=
  [missing5155]
abbrev records5155_5156 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5155]
theorem aligned5155_5156 :
    AlignedValid 12 4 missing5155_5156 records5155_5156 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5155
    maskCheck5155 AlignedValid.nil

def missing5154_5156 : List (BitVec (edgeCount 12)) :=
  missing5154_5155 ++ missing5155_5156
abbrev records5154_5156 : List Blob :=
  records5154_5155 ++ records5155_5156
theorem aligned5154_5156 :
    AlignedValid 12 4 missing5154_5156 records5154_5156 :=
  aligned5154_5155.append aligned5155_5156

def missing5152_5156 : List (BitVec (edgeCount 12)) :=
  missing5152_5154 ++ missing5154_5156
abbrev records5152_5156 : List Blob :=
  records5152_5154 ++ records5154_5156
theorem aligned5152_5156 :
    AlignedValid 12 4 missing5152_5156 records5152_5156 :=
  aligned5152_5154.append aligned5154_5156

def missing5156_5157 : List (BitVec (edgeCount 12)) :=
  [missing5156]
abbrev records5156_5157 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5156]
theorem aligned5156_5157 :
    AlignedValid 12 4 missing5156_5157 records5156_5157 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5156
    maskCheck5156 AlignedValid.nil

def missing5157_5158 : List (BitVec (edgeCount 12)) :=
  [missing5157]
abbrev records5157_5158 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5157]
theorem aligned5157_5158 :
    AlignedValid 12 4 missing5157_5158 records5157_5158 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5157
    maskCheck5157 AlignedValid.nil

def missing5156_5158 : List (BitVec (edgeCount 12)) :=
  missing5156_5157 ++ missing5157_5158
abbrev records5156_5158 : List Blob :=
  records5156_5157 ++ records5157_5158
theorem aligned5156_5158 :
    AlignedValid 12 4 missing5156_5158 records5156_5158 :=
  aligned5156_5157.append aligned5157_5158

def missing5158_5159 : List (BitVec (edgeCount 12)) :=
  [missing5158]
abbrev records5158_5159 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5158]
theorem aligned5158_5159 :
    AlignedValid 12 4 missing5158_5159 records5158_5159 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5158
    maskCheck5158 AlignedValid.nil

def missing5159_5160 : List (BitVec (edgeCount 12)) :=
  [missing5159]
abbrev records5159_5160 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5159]
theorem aligned5159_5160 :
    AlignedValid 12 4 missing5159_5160 records5159_5160 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5159
    maskCheck5159 AlignedValid.nil

def missing5158_5160 : List (BitVec (edgeCount 12)) :=
  missing5158_5159 ++ missing5159_5160
abbrev records5158_5160 : List Blob :=
  records5158_5159 ++ records5159_5160
theorem aligned5158_5160 :
    AlignedValid 12 4 missing5158_5160 records5158_5160 :=
  aligned5158_5159.append aligned5159_5160

def missing5156_5160 : List (BitVec (edgeCount 12)) :=
  missing5156_5158 ++ missing5158_5160
abbrev records5156_5160 : List Blob :=
  records5156_5158 ++ records5158_5160
theorem aligned5156_5160 :
    AlignedValid 12 4 missing5156_5160 records5156_5160 :=
  aligned5156_5158.append aligned5158_5160

def missing5152_5160 : List (BitVec (edgeCount 12)) :=
  missing5152_5156 ++ missing5156_5160
abbrev records5152_5160 : List Blob :=
  records5152_5156 ++ records5156_5160
theorem aligned5152_5160 :
    AlignedValid 12 4 missing5152_5160 records5152_5160 :=
  aligned5152_5156.append aligned5156_5160

def missing5160_5161 : List (BitVec (edgeCount 12)) :=
  [missing5160]
abbrev records5160_5161 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5160]
theorem aligned5160_5161 :
    AlignedValid 12 4 missing5160_5161 records5160_5161 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5160
    maskCheck5160 AlignedValid.nil

def missing5161_5162 : List (BitVec (edgeCount 12)) :=
  [missing5161]
abbrev records5161_5162 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5161]
theorem aligned5161_5162 :
    AlignedValid 12 4 missing5161_5162 records5161_5162 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5161
    maskCheck5161 AlignedValid.nil

def missing5160_5162 : List (BitVec (edgeCount 12)) :=
  missing5160_5161 ++ missing5161_5162
abbrev records5160_5162 : List Blob :=
  records5160_5161 ++ records5161_5162
theorem aligned5160_5162 :
    AlignedValid 12 4 missing5160_5162 records5160_5162 :=
  aligned5160_5161.append aligned5161_5162

def missing5162_5163 : List (BitVec (edgeCount 12)) :=
  [missing5162]
abbrev records5162_5163 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5162]
theorem aligned5162_5163 :
    AlignedValid 12 4 missing5162_5163 records5162_5163 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5162
    maskCheck5162 AlignedValid.nil

def missing5163_5164 : List (BitVec (edgeCount 12)) :=
  [missing5163]
abbrev records5163_5164 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5163]
theorem aligned5163_5164 :
    AlignedValid 12 4 missing5163_5164 records5163_5164 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5163
    maskCheck5163 AlignedValid.nil

def missing5162_5164 : List (BitVec (edgeCount 12)) :=
  missing5162_5163 ++ missing5163_5164
abbrev records5162_5164 : List Blob :=
  records5162_5163 ++ records5163_5164
theorem aligned5162_5164 :
    AlignedValid 12 4 missing5162_5164 records5162_5164 :=
  aligned5162_5163.append aligned5163_5164

def missing5160_5164 : List (BitVec (edgeCount 12)) :=
  missing5160_5162 ++ missing5162_5164
abbrev records5160_5164 : List Blob :=
  records5160_5162 ++ records5162_5164
theorem aligned5160_5164 :
    AlignedValid 12 4 missing5160_5164 records5160_5164 :=
  aligned5160_5162.append aligned5162_5164

def missing5164_5165 : List (BitVec (edgeCount 12)) :=
  [missing5164]
abbrev records5164_5165 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5164]
theorem aligned5164_5165 :
    AlignedValid 12 4 missing5164_5165 records5164_5165 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5164
    maskCheck5164 AlignedValid.nil

def missing5165_5166 : List (BitVec (edgeCount 12)) :=
  [missing5165]
abbrev records5165_5166 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5165]
theorem aligned5165_5166 :
    AlignedValid 12 4 missing5165_5166 records5165_5166 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5165
    maskCheck5165 AlignedValid.nil

def missing5164_5166 : List (BitVec (edgeCount 12)) :=
  missing5164_5165 ++ missing5165_5166
abbrev records5164_5166 : List Blob :=
  records5164_5165 ++ records5165_5166
theorem aligned5164_5166 :
    AlignedValid 12 4 missing5164_5166 records5164_5166 :=
  aligned5164_5165.append aligned5165_5166

def missing5166_5167 : List (BitVec (edgeCount 12)) :=
  [missing5166]
abbrev records5166_5167 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5166]
theorem aligned5166_5167 :
    AlignedValid 12 4 missing5166_5167 records5166_5167 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5166
    maskCheck5166 AlignedValid.nil

def missing5167_5168 : List (BitVec (edgeCount 12)) :=
  [missing5167]
abbrev records5167_5168 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5167]
theorem aligned5167_5168 :
    AlignedValid 12 4 missing5167_5168 records5167_5168 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5167
    maskCheck5167 AlignedValid.nil

def missing5166_5168 : List (BitVec (edgeCount 12)) :=
  missing5166_5167 ++ missing5167_5168
abbrev records5166_5168 : List Blob :=
  records5166_5167 ++ records5167_5168
theorem aligned5166_5168 :
    AlignedValid 12 4 missing5166_5168 records5166_5168 :=
  aligned5166_5167.append aligned5167_5168

def missing5164_5168 : List (BitVec (edgeCount 12)) :=
  missing5164_5166 ++ missing5166_5168
abbrev records5164_5168 : List Blob :=
  records5164_5166 ++ records5166_5168
theorem aligned5164_5168 :
    AlignedValid 12 4 missing5164_5168 records5164_5168 :=
  aligned5164_5166.append aligned5166_5168

def missing5160_5168 : List (BitVec (edgeCount 12)) :=
  missing5160_5164 ++ missing5164_5168
abbrev records5160_5168 : List Blob :=
  records5160_5164 ++ records5164_5168
theorem aligned5160_5168 :
    AlignedValid 12 4 missing5160_5168 records5160_5168 :=
  aligned5160_5164.append aligned5164_5168

def missing5152_5168 : List (BitVec (edgeCount 12)) :=
  missing5152_5160 ++ missing5160_5168
abbrev records5152_5168 : List Blob :=
  records5152_5160 ++ records5160_5168
theorem aligned5152_5168 :
    AlignedValid 12 4 missing5152_5168 records5152_5168 :=
  aligned5152_5160.append aligned5160_5168

def missing5168_5169 : List (BitVec (edgeCount 12)) :=
  [missing5168]
abbrev records5168_5169 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5168]
theorem aligned5168_5169 :
    AlignedValid 12 4 missing5168_5169 records5168_5169 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5168
    maskCheck5168 AlignedValid.nil

def missing5169_5170 : List (BitVec (edgeCount 12)) :=
  [missing5169]
abbrev records5169_5170 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5169]
theorem aligned5169_5170 :
    AlignedValid 12 4 missing5169_5170 records5169_5170 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5169
    maskCheck5169 AlignedValid.nil

def missing5168_5170 : List (BitVec (edgeCount 12)) :=
  missing5168_5169 ++ missing5169_5170
abbrev records5168_5170 : List Blob :=
  records5168_5169 ++ records5169_5170
theorem aligned5168_5170 :
    AlignedValid 12 4 missing5168_5170 records5168_5170 :=
  aligned5168_5169.append aligned5169_5170

def missing5170_5171 : List (BitVec (edgeCount 12)) :=
  [missing5170]
abbrev records5170_5171 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5170]
theorem aligned5170_5171 :
    AlignedValid 12 4 missing5170_5171 records5170_5171 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5170
    maskCheck5170 AlignedValid.nil

def missing5171_5172 : List (BitVec (edgeCount 12)) :=
  [missing5171]
abbrev records5171_5172 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5171]
theorem aligned5171_5172 :
    AlignedValid 12 4 missing5171_5172 records5171_5172 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5171
    maskCheck5171 AlignedValid.nil

def missing5170_5172 : List (BitVec (edgeCount 12)) :=
  missing5170_5171 ++ missing5171_5172
abbrev records5170_5172 : List Blob :=
  records5170_5171 ++ records5171_5172
theorem aligned5170_5172 :
    AlignedValid 12 4 missing5170_5172 records5170_5172 :=
  aligned5170_5171.append aligned5171_5172

def missing5168_5172 : List (BitVec (edgeCount 12)) :=
  missing5168_5170 ++ missing5170_5172
abbrev records5168_5172 : List Blob :=
  records5168_5170 ++ records5170_5172
theorem aligned5168_5172 :
    AlignedValid 12 4 missing5168_5172 records5168_5172 :=
  aligned5168_5170.append aligned5170_5172

def missing5172_5173 : List (BitVec (edgeCount 12)) :=
  [missing5172]
abbrev records5172_5173 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5172]
theorem aligned5172_5173 :
    AlignedValid 12 4 missing5172_5173 records5172_5173 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5172
    maskCheck5172 AlignedValid.nil

def missing5173_5174 : List (BitVec (edgeCount 12)) :=
  [missing5173]
abbrev records5173_5174 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5173]
theorem aligned5173_5174 :
    AlignedValid 12 4 missing5173_5174 records5173_5174 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5173
    maskCheck5173 AlignedValid.nil

def missing5172_5174 : List (BitVec (edgeCount 12)) :=
  missing5172_5173 ++ missing5173_5174
abbrev records5172_5174 : List Blob :=
  records5172_5173 ++ records5173_5174
theorem aligned5172_5174 :
    AlignedValid 12 4 missing5172_5174 records5172_5174 :=
  aligned5172_5173.append aligned5173_5174

def missing5174_5175 : List (BitVec (edgeCount 12)) :=
  [missing5174]
abbrev records5174_5175 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5174]
theorem aligned5174_5175 :
    AlignedValid 12 4 missing5174_5175 records5174_5175 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5174
    maskCheck5174 AlignedValid.nil

def missing5175_5176 : List (BitVec (edgeCount 12)) :=
  [missing5175]
abbrev records5175_5176 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5175]
theorem aligned5175_5176 :
    AlignedValid 12 4 missing5175_5176 records5175_5176 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5175
    maskCheck5175 AlignedValid.nil

def missing5174_5176 : List (BitVec (edgeCount 12)) :=
  missing5174_5175 ++ missing5175_5176
abbrev records5174_5176 : List Blob :=
  records5174_5175 ++ records5175_5176
theorem aligned5174_5176 :
    AlignedValid 12 4 missing5174_5176 records5174_5176 :=
  aligned5174_5175.append aligned5175_5176

def missing5172_5176 : List (BitVec (edgeCount 12)) :=
  missing5172_5174 ++ missing5174_5176
abbrev records5172_5176 : List Blob :=
  records5172_5174 ++ records5174_5176
theorem aligned5172_5176 :
    AlignedValid 12 4 missing5172_5176 records5172_5176 :=
  aligned5172_5174.append aligned5174_5176

def missing5168_5176 : List (BitVec (edgeCount 12)) :=
  missing5168_5172 ++ missing5172_5176
abbrev records5168_5176 : List Blob :=
  records5168_5172 ++ records5172_5176
theorem aligned5168_5176 :
    AlignedValid 12 4 missing5168_5176 records5168_5176 :=
  aligned5168_5172.append aligned5172_5176

def missing5176_5177 : List (BitVec (edgeCount 12)) :=
  [missing5176]
abbrev records5176_5177 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5176]
theorem aligned5176_5177 :
    AlignedValid 12 4 missing5176_5177 records5176_5177 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5176
    maskCheck5176 AlignedValid.nil

def missing5177_5178 : List (BitVec (edgeCount 12)) :=
  [missing5177]
abbrev records5177_5178 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5177]
theorem aligned5177_5178 :
    AlignedValid 12 4 missing5177_5178 records5177_5178 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5177
    maskCheck5177 AlignedValid.nil

def missing5176_5178 : List (BitVec (edgeCount 12)) :=
  missing5176_5177 ++ missing5177_5178
abbrev records5176_5178 : List Blob :=
  records5176_5177 ++ records5177_5178
theorem aligned5176_5178 :
    AlignedValid 12 4 missing5176_5178 records5176_5178 :=
  aligned5176_5177.append aligned5177_5178

def missing5178_5179 : List (BitVec (edgeCount 12)) :=
  [missing5178]
abbrev records5178_5179 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5178]
theorem aligned5178_5179 :
    AlignedValid 12 4 missing5178_5179 records5178_5179 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5178
    maskCheck5178 AlignedValid.nil

def missing5179_5180 : List (BitVec (edgeCount 12)) :=
  [missing5179]
abbrev records5179_5180 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5179]
theorem aligned5179_5180 :
    AlignedValid 12 4 missing5179_5180 records5179_5180 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5179
    maskCheck5179 AlignedValid.nil

def missing5178_5180 : List (BitVec (edgeCount 12)) :=
  missing5178_5179 ++ missing5179_5180
abbrev records5178_5180 : List Blob :=
  records5178_5179 ++ records5179_5180
theorem aligned5178_5180 :
    AlignedValid 12 4 missing5178_5180 records5178_5180 :=
  aligned5178_5179.append aligned5179_5180

def missing5176_5180 : List (BitVec (edgeCount 12)) :=
  missing5176_5178 ++ missing5178_5180
abbrev records5176_5180 : List Blob :=
  records5176_5178 ++ records5178_5180
theorem aligned5176_5180 :
    AlignedValid 12 4 missing5176_5180 records5176_5180 :=
  aligned5176_5178.append aligned5178_5180

def missing5180_5181 : List (BitVec (edgeCount 12)) :=
  [missing5180]
abbrev records5180_5181 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5180]
theorem aligned5180_5181 :
    AlignedValid 12 4 missing5180_5181 records5180_5181 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5180
    maskCheck5180 AlignedValid.nil

def missing5181_5182 : List (BitVec (edgeCount 12)) :=
  [missing5181]
abbrev records5181_5182 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5181]
theorem aligned5181_5182 :
    AlignedValid 12 4 missing5181_5182 records5181_5182 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5181
    maskCheck5181 AlignedValid.nil

def missing5180_5182 : List (BitVec (edgeCount 12)) :=
  missing5180_5181 ++ missing5181_5182
abbrev records5180_5182 : List Blob :=
  records5180_5181 ++ records5181_5182
theorem aligned5180_5182 :
    AlignedValid 12 4 missing5180_5182 records5180_5182 :=
  aligned5180_5181.append aligned5181_5182

def missing5182_5183 : List (BitVec (edgeCount 12)) :=
  [missing5182]
abbrev records5182_5183 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5182]
theorem aligned5182_5183 :
    AlignedValid 12 4 missing5182_5183 records5182_5183 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5182
    maskCheck5182 AlignedValid.nil

def missing5183_5184 : List (BitVec (edgeCount 12)) :=
  [missing5183]
abbrev records5183_5184 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5183]
theorem aligned5183_5184 :
    AlignedValid 12 4 missing5183_5184 records5183_5184 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5183
    maskCheck5183 AlignedValid.nil

def missing5182_5184 : List (BitVec (edgeCount 12)) :=
  missing5182_5183 ++ missing5183_5184
abbrev records5182_5184 : List Blob :=
  records5182_5183 ++ records5183_5184
theorem aligned5182_5184 :
    AlignedValid 12 4 missing5182_5184 records5182_5184 :=
  aligned5182_5183.append aligned5183_5184

def missing5180_5184 : List (BitVec (edgeCount 12)) :=
  missing5180_5182 ++ missing5182_5184
abbrev records5180_5184 : List Blob :=
  records5180_5182 ++ records5182_5184
theorem aligned5180_5184 :
    AlignedValid 12 4 missing5180_5184 records5180_5184 :=
  aligned5180_5182.append aligned5182_5184

def missing5176_5184 : List (BitVec (edgeCount 12)) :=
  missing5176_5180 ++ missing5180_5184
abbrev records5176_5184 : List Blob :=
  records5176_5180 ++ records5180_5184
theorem aligned5176_5184 :
    AlignedValid 12 4 missing5176_5184 records5176_5184 :=
  aligned5176_5180.append aligned5180_5184

def missing5168_5184 : List (BitVec (edgeCount 12)) :=
  missing5168_5176 ++ missing5176_5184
abbrev records5168_5184 : List Blob :=
  records5168_5176 ++ records5176_5184
theorem aligned5168_5184 :
    AlignedValid 12 4 missing5168_5184 records5168_5184 :=
  aligned5168_5176.append aligned5176_5184

def missing5152_5184 : List (BitVec (edgeCount 12)) :=
  missing5152_5168 ++ missing5168_5184
abbrev records5152_5184 : List Blob :=
  records5152_5168 ++ records5168_5184
theorem aligned5152_5184 :
    AlignedValid 12 4 missing5152_5184 records5152_5184 :=
  aligned5152_5168.append aligned5168_5184

def missing5120_5184 : List (BitVec (edgeCount 12)) :=
  missing5120_5152 ++ missing5152_5184
abbrev records5120_5184 : List Blob :=
  records5120_5152 ++ records5152_5184
theorem aligned5120_5184 :
    AlignedValid 12 4 missing5120_5184 records5120_5184 :=
  aligned5120_5152.append aligned5152_5184

def missing5184_5185 : List (BitVec (edgeCount 12)) :=
  [missing5184]
abbrev records5184_5185 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5184]
theorem aligned5184_5185 :
    AlignedValid 12 4 missing5184_5185 records5184_5185 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5184
    maskCheck5184 AlignedValid.nil

def missing5185_5186 : List (BitVec (edgeCount 12)) :=
  [missing5185]
abbrev records5185_5186 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5185]
theorem aligned5185_5186 :
    AlignedValid 12 4 missing5185_5186 records5185_5186 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5185
    maskCheck5185 AlignedValid.nil

def missing5184_5186 : List (BitVec (edgeCount 12)) :=
  missing5184_5185 ++ missing5185_5186
abbrev records5184_5186 : List Blob :=
  records5184_5185 ++ records5185_5186
theorem aligned5184_5186 :
    AlignedValid 12 4 missing5184_5186 records5184_5186 :=
  aligned5184_5185.append aligned5185_5186

def missing5186_5187 : List (BitVec (edgeCount 12)) :=
  [missing5186]
abbrev records5186_5187 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5186]
theorem aligned5186_5187 :
    AlignedValid 12 4 missing5186_5187 records5186_5187 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5186
    maskCheck5186 AlignedValid.nil

def missing5187_5188 : List (BitVec (edgeCount 12)) :=
  [missing5187]
abbrev records5187_5188 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5187]
theorem aligned5187_5188 :
    AlignedValid 12 4 missing5187_5188 records5187_5188 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5187
    maskCheck5187 AlignedValid.nil

def missing5186_5188 : List (BitVec (edgeCount 12)) :=
  missing5186_5187 ++ missing5187_5188
abbrev records5186_5188 : List Blob :=
  records5186_5187 ++ records5187_5188
theorem aligned5186_5188 :
    AlignedValid 12 4 missing5186_5188 records5186_5188 :=
  aligned5186_5187.append aligned5187_5188

def missing5184_5188 : List (BitVec (edgeCount 12)) :=
  missing5184_5186 ++ missing5186_5188
abbrev records5184_5188 : List Blob :=
  records5184_5186 ++ records5186_5188
theorem aligned5184_5188 :
    AlignedValid 12 4 missing5184_5188 records5184_5188 :=
  aligned5184_5186.append aligned5186_5188

def missing5188_5189 : List (BitVec (edgeCount 12)) :=
  [missing5188]
abbrev records5188_5189 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5188]
theorem aligned5188_5189 :
    AlignedValid 12 4 missing5188_5189 records5188_5189 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5188
    maskCheck5188 AlignedValid.nil

def missing5189_5190 : List (BitVec (edgeCount 12)) :=
  [missing5189]
abbrev records5189_5190 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5189]
theorem aligned5189_5190 :
    AlignedValid 12 4 missing5189_5190 records5189_5190 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5189
    maskCheck5189 AlignedValid.nil

def missing5188_5190 : List (BitVec (edgeCount 12)) :=
  missing5188_5189 ++ missing5189_5190
abbrev records5188_5190 : List Blob :=
  records5188_5189 ++ records5189_5190
theorem aligned5188_5190 :
    AlignedValid 12 4 missing5188_5190 records5188_5190 :=
  aligned5188_5189.append aligned5189_5190

def missing5190_5191 : List (BitVec (edgeCount 12)) :=
  [missing5190]
abbrev records5190_5191 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5190]
theorem aligned5190_5191 :
    AlignedValid 12 4 missing5190_5191 records5190_5191 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5190
    maskCheck5190 AlignedValid.nil

def missing5191_5192 : List (BitVec (edgeCount 12)) :=
  [missing5191]
abbrev records5191_5192 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5191]
theorem aligned5191_5192 :
    AlignedValid 12 4 missing5191_5192 records5191_5192 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5191
    maskCheck5191 AlignedValid.nil

def missing5190_5192 : List (BitVec (edgeCount 12)) :=
  missing5190_5191 ++ missing5191_5192
abbrev records5190_5192 : List Blob :=
  records5190_5191 ++ records5191_5192
theorem aligned5190_5192 :
    AlignedValid 12 4 missing5190_5192 records5190_5192 :=
  aligned5190_5191.append aligned5191_5192

def missing5188_5192 : List (BitVec (edgeCount 12)) :=
  missing5188_5190 ++ missing5190_5192
abbrev records5188_5192 : List Blob :=
  records5188_5190 ++ records5190_5192
theorem aligned5188_5192 :
    AlignedValid 12 4 missing5188_5192 records5188_5192 :=
  aligned5188_5190.append aligned5190_5192

def missing5184_5192 : List (BitVec (edgeCount 12)) :=
  missing5184_5188 ++ missing5188_5192
abbrev records5184_5192 : List Blob :=
  records5184_5188 ++ records5188_5192
theorem aligned5184_5192 :
    AlignedValid 12 4 missing5184_5192 records5184_5192 :=
  aligned5184_5188.append aligned5188_5192

def missing5192_5193 : List (BitVec (edgeCount 12)) :=
  [missing5192]
abbrev records5192_5193 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5192]
theorem aligned5192_5193 :
    AlignedValid 12 4 missing5192_5193 records5192_5193 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5192
    maskCheck5192 AlignedValid.nil

def missing5193_5194 : List (BitVec (edgeCount 12)) :=
  [missing5193]
abbrev records5193_5194 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5193]
theorem aligned5193_5194 :
    AlignedValid 12 4 missing5193_5194 records5193_5194 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5193
    maskCheck5193 AlignedValid.nil

def missing5192_5194 : List (BitVec (edgeCount 12)) :=
  missing5192_5193 ++ missing5193_5194
abbrev records5192_5194 : List Blob :=
  records5192_5193 ++ records5193_5194
theorem aligned5192_5194 :
    AlignedValid 12 4 missing5192_5194 records5192_5194 :=
  aligned5192_5193.append aligned5193_5194

def missing5194_5195 : List (BitVec (edgeCount 12)) :=
  [missing5194]
abbrev records5194_5195 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5194]
theorem aligned5194_5195 :
    AlignedValid 12 4 missing5194_5195 records5194_5195 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5194
    maskCheck5194 AlignedValid.nil

def missing5195_5196 : List (BitVec (edgeCount 12)) :=
  [missing5195]
abbrev records5195_5196 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5195]
theorem aligned5195_5196 :
    AlignedValid 12 4 missing5195_5196 records5195_5196 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5195
    maskCheck5195 AlignedValid.nil

def missing5194_5196 : List (BitVec (edgeCount 12)) :=
  missing5194_5195 ++ missing5195_5196
abbrev records5194_5196 : List Blob :=
  records5194_5195 ++ records5195_5196
theorem aligned5194_5196 :
    AlignedValid 12 4 missing5194_5196 records5194_5196 :=
  aligned5194_5195.append aligned5195_5196

def missing5192_5196 : List (BitVec (edgeCount 12)) :=
  missing5192_5194 ++ missing5194_5196
abbrev records5192_5196 : List Blob :=
  records5192_5194 ++ records5194_5196
theorem aligned5192_5196 :
    AlignedValid 12 4 missing5192_5196 records5192_5196 :=
  aligned5192_5194.append aligned5194_5196

def missing5196_5197 : List (BitVec (edgeCount 12)) :=
  [missing5196]
abbrev records5196_5197 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5196]
theorem aligned5196_5197 :
    AlignedValid 12 4 missing5196_5197 records5196_5197 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5196
    maskCheck5196 AlignedValid.nil

def missing5197_5198 : List (BitVec (edgeCount 12)) :=
  [missing5197]
abbrev records5197_5198 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5197]
theorem aligned5197_5198 :
    AlignedValid 12 4 missing5197_5198 records5197_5198 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5197
    maskCheck5197 AlignedValid.nil

def missing5196_5198 : List (BitVec (edgeCount 12)) :=
  missing5196_5197 ++ missing5197_5198
abbrev records5196_5198 : List Blob :=
  records5196_5197 ++ records5197_5198
theorem aligned5196_5198 :
    AlignedValid 12 4 missing5196_5198 records5196_5198 :=
  aligned5196_5197.append aligned5197_5198

def missing5198_5199 : List (BitVec (edgeCount 12)) :=
  [missing5198]
abbrev records5198_5199 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5198]
theorem aligned5198_5199 :
    AlignedValid 12 4 missing5198_5199 records5198_5199 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5198
    maskCheck5198 AlignedValid.nil

def missing5199_5200 : List (BitVec (edgeCount 12)) :=
  [missing5199]
abbrev records5199_5200 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5199]
theorem aligned5199_5200 :
    AlignedValid 12 4 missing5199_5200 records5199_5200 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5199
    maskCheck5199 AlignedValid.nil

def missing5198_5200 : List (BitVec (edgeCount 12)) :=
  missing5198_5199 ++ missing5199_5200
abbrev records5198_5200 : List Blob :=
  records5198_5199 ++ records5199_5200
theorem aligned5198_5200 :
    AlignedValid 12 4 missing5198_5200 records5198_5200 :=
  aligned5198_5199.append aligned5199_5200

def missing5196_5200 : List (BitVec (edgeCount 12)) :=
  missing5196_5198 ++ missing5198_5200
abbrev records5196_5200 : List Blob :=
  records5196_5198 ++ records5198_5200
theorem aligned5196_5200 :
    AlignedValid 12 4 missing5196_5200 records5196_5200 :=
  aligned5196_5198.append aligned5198_5200

def missing5192_5200 : List (BitVec (edgeCount 12)) :=
  missing5192_5196 ++ missing5196_5200
abbrev records5192_5200 : List Blob :=
  records5192_5196 ++ records5196_5200
theorem aligned5192_5200 :
    AlignedValid 12 4 missing5192_5200 records5192_5200 :=
  aligned5192_5196.append aligned5196_5200

def missing5184_5200 : List (BitVec (edgeCount 12)) :=
  missing5184_5192 ++ missing5192_5200
abbrev records5184_5200 : List Blob :=
  records5184_5192 ++ records5192_5200
theorem aligned5184_5200 :
    AlignedValid 12 4 missing5184_5200 records5184_5200 :=
  aligned5184_5192.append aligned5192_5200

def missing5200_5201 : List (BitVec (edgeCount 12)) :=
  [missing5200]
abbrev records5200_5201 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5200]
theorem aligned5200_5201 :
    AlignedValid 12 4 missing5200_5201 records5200_5201 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5200
    maskCheck5200 AlignedValid.nil

def missing5201_5202 : List (BitVec (edgeCount 12)) :=
  [missing5201]
abbrev records5201_5202 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5201]
theorem aligned5201_5202 :
    AlignedValid 12 4 missing5201_5202 records5201_5202 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5201
    maskCheck5201 AlignedValid.nil

def missing5200_5202 : List (BitVec (edgeCount 12)) :=
  missing5200_5201 ++ missing5201_5202
abbrev records5200_5202 : List Blob :=
  records5200_5201 ++ records5201_5202
theorem aligned5200_5202 :
    AlignedValid 12 4 missing5200_5202 records5200_5202 :=
  aligned5200_5201.append aligned5201_5202

def missing5202_5203 : List (BitVec (edgeCount 12)) :=
  [missing5202]
abbrev records5202_5203 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5202]
theorem aligned5202_5203 :
    AlignedValid 12 4 missing5202_5203 records5202_5203 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5202
    maskCheck5202 AlignedValid.nil

def missing5203_5204 : List (BitVec (edgeCount 12)) :=
  [missing5203]
abbrev records5203_5204 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5203]
theorem aligned5203_5204 :
    AlignedValid 12 4 missing5203_5204 records5203_5204 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5203
    maskCheck5203 AlignedValid.nil

def missing5202_5204 : List (BitVec (edgeCount 12)) :=
  missing5202_5203 ++ missing5203_5204
abbrev records5202_5204 : List Blob :=
  records5202_5203 ++ records5203_5204
theorem aligned5202_5204 :
    AlignedValid 12 4 missing5202_5204 records5202_5204 :=
  aligned5202_5203.append aligned5203_5204

def missing5200_5204 : List (BitVec (edgeCount 12)) :=
  missing5200_5202 ++ missing5202_5204
abbrev records5200_5204 : List Blob :=
  records5200_5202 ++ records5202_5204
theorem aligned5200_5204 :
    AlignedValid 12 4 missing5200_5204 records5200_5204 :=
  aligned5200_5202.append aligned5202_5204

def missing5204_5205 : List (BitVec (edgeCount 12)) :=
  [missing5204]
abbrev records5204_5205 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5204]
theorem aligned5204_5205 :
    AlignedValid 12 4 missing5204_5205 records5204_5205 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5204
    maskCheck5204 AlignedValid.nil

def missing5205_5206 : List (BitVec (edgeCount 12)) :=
  [missing5205]
abbrev records5205_5206 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5205]
theorem aligned5205_5206 :
    AlignedValid 12 4 missing5205_5206 records5205_5206 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5205
    maskCheck5205 AlignedValid.nil

def missing5204_5206 : List (BitVec (edgeCount 12)) :=
  missing5204_5205 ++ missing5205_5206
abbrev records5204_5206 : List Blob :=
  records5204_5205 ++ records5205_5206
theorem aligned5204_5206 :
    AlignedValid 12 4 missing5204_5206 records5204_5206 :=
  aligned5204_5205.append aligned5205_5206

def missing5206_5207 : List (BitVec (edgeCount 12)) :=
  [missing5206]
abbrev records5206_5207 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5206]
theorem aligned5206_5207 :
    AlignedValid 12 4 missing5206_5207 records5206_5207 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5206
    maskCheck5206 AlignedValid.nil

def missing5207_5208 : List (BitVec (edgeCount 12)) :=
  [missing5207]
abbrev records5207_5208 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5207]
theorem aligned5207_5208 :
    AlignedValid 12 4 missing5207_5208 records5207_5208 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5207
    maskCheck5207 AlignedValid.nil

def missing5206_5208 : List (BitVec (edgeCount 12)) :=
  missing5206_5207 ++ missing5207_5208
abbrev records5206_5208 : List Blob :=
  records5206_5207 ++ records5207_5208
theorem aligned5206_5208 :
    AlignedValid 12 4 missing5206_5208 records5206_5208 :=
  aligned5206_5207.append aligned5207_5208

def missing5204_5208 : List (BitVec (edgeCount 12)) :=
  missing5204_5206 ++ missing5206_5208
abbrev records5204_5208 : List Blob :=
  records5204_5206 ++ records5206_5208
theorem aligned5204_5208 :
    AlignedValid 12 4 missing5204_5208 records5204_5208 :=
  aligned5204_5206.append aligned5206_5208

def missing5200_5208 : List (BitVec (edgeCount 12)) :=
  missing5200_5204 ++ missing5204_5208
abbrev records5200_5208 : List Blob :=
  records5200_5204 ++ records5204_5208
theorem aligned5200_5208 :
    AlignedValid 12 4 missing5200_5208 records5200_5208 :=
  aligned5200_5204.append aligned5204_5208

def missing5208_5209 : List (BitVec (edgeCount 12)) :=
  [missing5208]
abbrev records5208_5209 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5208]
theorem aligned5208_5209 :
    AlignedValid 12 4 missing5208_5209 records5208_5209 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5208
    maskCheck5208 AlignedValid.nil

def missing5209_5210 : List (BitVec (edgeCount 12)) :=
  [missing5209]
abbrev records5209_5210 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5209]
theorem aligned5209_5210 :
    AlignedValid 12 4 missing5209_5210 records5209_5210 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5209
    maskCheck5209 AlignedValid.nil

def missing5208_5210 : List (BitVec (edgeCount 12)) :=
  missing5208_5209 ++ missing5209_5210
abbrev records5208_5210 : List Blob :=
  records5208_5209 ++ records5209_5210
theorem aligned5208_5210 :
    AlignedValid 12 4 missing5208_5210 records5208_5210 :=
  aligned5208_5209.append aligned5209_5210

def missing5210_5211 : List (BitVec (edgeCount 12)) :=
  [missing5210]
abbrev records5210_5211 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5210]
theorem aligned5210_5211 :
    AlignedValid 12 4 missing5210_5211 records5210_5211 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5210
    maskCheck5210 AlignedValid.nil

def missing5211_5212 : List (BitVec (edgeCount 12)) :=
  [missing5211]
abbrev records5211_5212 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5211]
theorem aligned5211_5212 :
    AlignedValid 12 4 missing5211_5212 records5211_5212 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5211
    maskCheck5211 AlignedValid.nil

def missing5210_5212 : List (BitVec (edgeCount 12)) :=
  missing5210_5211 ++ missing5211_5212
abbrev records5210_5212 : List Blob :=
  records5210_5211 ++ records5211_5212
theorem aligned5210_5212 :
    AlignedValid 12 4 missing5210_5212 records5210_5212 :=
  aligned5210_5211.append aligned5211_5212

def missing5208_5212 : List (BitVec (edgeCount 12)) :=
  missing5208_5210 ++ missing5210_5212
abbrev records5208_5212 : List Blob :=
  records5208_5210 ++ records5210_5212
theorem aligned5208_5212 :
    AlignedValid 12 4 missing5208_5212 records5208_5212 :=
  aligned5208_5210.append aligned5210_5212

def missing5212_5213 : List (BitVec (edgeCount 12)) :=
  [missing5212]
abbrev records5212_5213 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5212]
theorem aligned5212_5213 :
    AlignedValid 12 4 missing5212_5213 records5212_5213 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5212
    maskCheck5212 AlignedValid.nil

def missing5213_5214 : List (BitVec (edgeCount 12)) :=
  [missing5213]
abbrev records5213_5214 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5213]
theorem aligned5213_5214 :
    AlignedValid 12 4 missing5213_5214 records5213_5214 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5213
    maskCheck5213 AlignedValid.nil

def missing5212_5214 : List (BitVec (edgeCount 12)) :=
  missing5212_5213 ++ missing5213_5214
abbrev records5212_5214 : List Blob :=
  records5212_5213 ++ records5213_5214
theorem aligned5212_5214 :
    AlignedValid 12 4 missing5212_5214 records5212_5214 :=
  aligned5212_5213.append aligned5213_5214

def missing5214_5215 : List (BitVec (edgeCount 12)) :=
  [missing5214]
abbrev records5214_5215 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5214]
theorem aligned5214_5215 :
    AlignedValid 12 4 missing5214_5215 records5214_5215 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5214
    maskCheck5214 AlignedValid.nil

def missing5215_5216 : List (BitVec (edgeCount 12)) :=
  [missing5215]
abbrev records5215_5216 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5215]
theorem aligned5215_5216 :
    AlignedValid 12 4 missing5215_5216 records5215_5216 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5215
    maskCheck5215 AlignedValid.nil

def missing5214_5216 : List (BitVec (edgeCount 12)) :=
  missing5214_5215 ++ missing5215_5216
abbrev records5214_5216 : List Blob :=
  records5214_5215 ++ records5215_5216
theorem aligned5214_5216 :
    AlignedValid 12 4 missing5214_5216 records5214_5216 :=
  aligned5214_5215.append aligned5215_5216

def missing5212_5216 : List (BitVec (edgeCount 12)) :=
  missing5212_5214 ++ missing5214_5216
abbrev records5212_5216 : List Blob :=
  records5212_5214 ++ records5214_5216
theorem aligned5212_5216 :
    AlignedValid 12 4 missing5212_5216 records5212_5216 :=
  aligned5212_5214.append aligned5214_5216

def missing5208_5216 : List (BitVec (edgeCount 12)) :=
  missing5208_5212 ++ missing5212_5216
abbrev records5208_5216 : List Blob :=
  records5208_5212 ++ records5212_5216
theorem aligned5208_5216 :
    AlignedValid 12 4 missing5208_5216 records5208_5216 :=
  aligned5208_5212.append aligned5212_5216

def missing5200_5216 : List (BitVec (edgeCount 12)) :=
  missing5200_5208 ++ missing5208_5216
abbrev records5200_5216 : List Blob :=
  records5200_5208 ++ records5208_5216
theorem aligned5200_5216 :
    AlignedValid 12 4 missing5200_5216 records5200_5216 :=
  aligned5200_5208.append aligned5208_5216

def missing5184_5216 : List (BitVec (edgeCount 12)) :=
  missing5184_5200 ++ missing5200_5216
abbrev records5184_5216 : List Blob :=
  records5184_5200 ++ records5200_5216
theorem aligned5184_5216 :
    AlignedValid 12 4 missing5184_5216 records5184_5216 :=
  aligned5184_5200.append aligned5200_5216

def missing5216_5217 : List (BitVec (edgeCount 12)) :=
  [missing5216]
abbrev records5216_5217 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5216]
theorem aligned5216_5217 :
    AlignedValid 12 4 missing5216_5217 records5216_5217 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5216
    maskCheck5216 AlignedValid.nil

def missing5217_5218 : List (BitVec (edgeCount 12)) :=
  [missing5217]
abbrev records5217_5218 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5217]
theorem aligned5217_5218 :
    AlignedValid 12 4 missing5217_5218 records5217_5218 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5217
    maskCheck5217 AlignedValid.nil

def missing5216_5218 : List (BitVec (edgeCount 12)) :=
  missing5216_5217 ++ missing5217_5218
abbrev records5216_5218 : List Blob :=
  records5216_5217 ++ records5217_5218
theorem aligned5216_5218 :
    AlignedValid 12 4 missing5216_5218 records5216_5218 :=
  aligned5216_5217.append aligned5217_5218

def missing5218_5219 : List (BitVec (edgeCount 12)) :=
  [missing5218]
abbrev records5218_5219 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5218]
theorem aligned5218_5219 :
    AlignedValid 12 4 missing5218_5219 records5218_5219 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5218
    maskCheck5218 AlignedValid.nil

def missing5219_5220 : List (BitVec (edgeCount 12)) :=
  [missing5219]
abbrev records5219_5220 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5219]
theorem aligned5219_5220 :
    AlignedValid 12 4 missing5219_5220 records5219_5220 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5219
    maskCheck5219 AlignedValid.nil

def missing5218_5220 : List (BitVec (edgeCount 12)) :=
  missing5218_5219 ++ missing5219_5220
abbrev records5218_5220 : List Blob :=
  records5218_5219 ++ records5219_5220
theorem aligned5218_5220 :
    AlignedValid 12 4 missing5218_5220 records5218_5220 :=
  aligned5218_5219.append aligned5219_5220

def missing5216_5220 : List (BitVec (edgeCount 12)) :=
  missing5216_5218 ++ missing5218_5220
abbrev records5216_5220 : List Blob :=
  records5216_5218 ++ records5218_5220
theorem aligned5216_5220 :
    AlignedValid 12 4 missing5216_5220 records5216_5220 :=
  aligned5216_5218.append aligned5218_5220

def missing5220_5221 : List (BitVec (edgeCount 12)) :=
  [missing5220]
abbrev records5220_5221 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5220]
theorem aligned5220_5221 :
    AlignedValid 12 4 missing5220_5221 records5220_5221 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5220
    maskCheck5220 AlignedValid.nil

def missing5221_5222 : List (BitVec (edgeCount 12)) :=
  [missing5221]
abbrev records5221_5222 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5221]
theorem aligned5221_5222 :
    AlignedValid 12 4 missing5221_5222 records5221_5222 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5221
    maskCheck5221 AlignedValid.nil

def missing5220_5222 : List (BitVec (edgeCount 12)) :=
  missing5220_5221 ++ missing5221_5222
abbrev records5220_5222 : List Blob :=
  records5220_5221 ++ records5221_5222
theorem aligned5220_5222 :
    AlignedValid 12 4 missing5220_5222 records5220_5222 :=
  aligned5220_5221.append aligned5221_5222

def missing5222_5223 : List (BitVec (edgeCount 12)) :=
  [missing5222]
abbrev records5222_5223 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5222]
theorem aligned5222_5223 :
    AlignedValid 12 4 missing5222_5223 records5222_5223 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5222
    maskCheck5222 AlignedValid.nil

def missing5223_5224 : List (BitVec (edgeCount 12)) :=
  [missing5223]
abbrev records5223_5224 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5223]
theorem aligned5223_5224 :
    AlignedValid 12 4 missing5223_5224 records5223_5224 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5223
    maskCheck5223 AlignedValid.nil

def missing5222_5224 : List (BitVec (edgeCount 12)) :=
  missing5222_5223 ++ missing5223_5224
abbrev records5222_5224 : List Blob :=
  records5222_5223 ++ records5223_5224
theorem aligned5222_5224 :
    AlignedValid 12 4 missing5222_5224 records5222_5224 :=
  aligned5222_5223.append aligned5223_5224

def missing5220_5224 : List (BitVec (edgeCount 12)) :=
  missing5220_5222 ++ missing5222_5224
abbrev records5220_5224 : List Blob :=
  records5220_5222 ++ records5222_5224
theorem aligned5220_5224 :
    AlignedValid 12 4 missing5220_5224 records5220_5224 :=
  aligned5220_5222.append aligned5222_5224

def missing5216_5224 : List (BitVec (edgeCount 12)) :=
  missing5216_5220 ++ missing5220_5224
abbrev records5216_5224 : List Blob :=
  records5216_5220 ++ records5220_5224
theorem aligned5216_5224 :
    AlignedValid 12 4 missing5216_5224 records5216_5224 :=
  aligned5216_5220.append aligned5220_5224

def missing5224_5225 : List (BitVec (edgeCount 12)) :=
  [missing5224]
abbrev records5224_5225 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5224]
theorem aligned5224_5225 :
    AlignedValid 12 4 missing5224_5225 records5224_5225 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5224
    maskCheck5224 AlignedValid.nil

def missing5225_5226 : List (BitVec (edgeCount 12)) :=
  [missing5225]
abbrev records5225_5226 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5225]
theorem aligned5225_5226 :
    AlignedValid 12 4 missing5225_5226 records5225_5226 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5225
    maskCheck5225 AlignedValid.nil

def missing5224_5226 : List (BitVec (edgeCount 12)) :=
  missing5224_5225 ++ missing5225_5226
abbrev records5224_5226 : List Blob :=
  records5224_5225 ++ records5225_5226
theorem aligned5224_5226 :
    AlignedValid 12 4 missing5224_5226 records5224_5226 :=
  aligned5224_5225.append aligned5225_5226

def missing5226_5227 : List (BitVec (edgeCount 12)) :=
  [missing5226]
abbrev records5226_5227 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5226]
theorem aligned5226_5227 :
    AlignedValid 12 4 missing5226_5227 records5226_5227 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5226
    maskCheck5226 AlignedValid.nil

def missing5227_5228 : List (BitVec (edgeCount 12)) :=
  [missing5227]
abbrev records5227_5228 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5227]
theorem aligned5227_5228 :
    AlignedValid 12 4 missing5227_5228 records5227_5228 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5227
    maskCheck5227 AlignedValid.nil

def missing5226_5228 : List (BitVec (edgeCount 12)) :=
  missing5226_5227 ++ missing5227_5228
abbrev records5226_5228 : List Blob :=
  records5226_5227 ++ records5227_5228
theorem aligned5226_5228 :
    AlignedValid 12 4 missing5226_5228 records5226_5228 :=
  aligned5226_5227.append aligned5227_5228

def missing5224_5228 : List (BitVec (edgeCount 12)) :=
  missing5224_5226 ++ missing5226_5228
abbrev records5224_5228 : List Blob :=
  records5224_5226 ++ records5226_5228
theorem aligned5224_5228 :
    AlignedValid 12 4 missing5224_5228 records5224_5228 :=
  aligned5224_5226.append aligned5226_5228

def missing5228_5229 : List (BitVec (edgeCount 12)) :=
  [missing5228]
abbrev records5228_5229 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5228]
theorem aligned5228_5229 :
    AlignedValid 12 4 missing5228_5229 records5228_5229 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5228
    maskCheck5228 AlignedValid.nil

def missing5229_5230 : List (BitVec (edgeCount 12)) :=
  [missing5229]
abbrev records5229_5230 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5229]
theorem aligned5229_5230 :
    AlignedValid 12 4 missing5229_5230 records5229_5230 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5229
    maskCheck5229 AlignedValid.nil

def missing5228_5230 : List (BitVec (edgeCount 12)) :=
  missing5228_5229 ++ missing5229_5230
abbrev records5228_5230 : List Blob :=
  records5228_5229 ++ records5229_5230
theorem aligned5228_5230 :
    AlignedValid 12 4 missing5228_5230 records5228_5230 :=
  aligned5228_5229.append aligned5229_5230

def missing5230_5231 : List (BitVec (edgeCount 12)) :=
  [missing5230]
abbrev records5230_5231 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5230]
theorem aligned5230_5231 :
    AlignedValid 12 4 missing5230_5231 records5230_5231 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5230
    maskCheck5230 AlignedValid.nil

def missing5231_5232 : List (BitVec (edgeCount 12)) :=
  [missing5231]
abbrev records5231_5232 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5231]
theorem aligned5231_5232 :
    AlignedValid 12 4 missing5231_5232 records5231_5232 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5231
    maskCheck5231 AlignedValid.nil

def missing5230_5232 : List (BitVec (edgeCount 12)) :=
  missing5230_5231 ++ missing5231_5232
abbrev records5230_5232 : List Blob :=
  records5230_5231 ++ records5231_5232
theorem aligned5230_5232 :
    AlignedValid 12 4 missing5230_5232 records5230_5232 :=
  aligned5230_5231.append aligned5231_5232

def missing5228_5232 : List (BitVec (edgeCount 12)) :=
  missing5228_5230 ++ missing5230_5232
abbrev records5228_5232 : List Blob :=
  records5228_5230 ++ records5230_5232
theorem aligned5228_5232 :
    AlignedValid 12 4 missing5228_5232 records5228_5232 :=
  aligned5228_5230.append aligned5230_5232

def missing5224_5232 : List (BitVec (edgeCount 12)) :=
  missing5224_5228 ++ missing5228_5232
abbrev records5224_5232 : List Blob :=
  records5224_5228 ++ records5228_5232
theorem aligned5224_5232 :
    AlignedValid 12 4 missing5224_5232 records5224_5232 :=
  aligned5224_5228.append aligned5228_5232

def missing5216_5232 : List (BitVec (edgeCount 12)) :=
  missing5216_5224 ++ missing5224_5232
abbrev records5216_5232 : List Blob :=
  records5216_5224 ++ records5224_5232
theorem aligned5216_5232 :
    AlignedValid 12 4 missing5216_5232 records5216_5232 :=
  aligned5216_5224.append aligned5224_5232

def missing5232_5233 : List (BitVec (edgeCount 12)) :=
  [missing5232]
abbrev records5232_5233 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5232]
theorem aligned5232_5233 :
    AlignedValid 12 4 missing5232_5233 records5232_5233 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5232
    maskCheck5232 AlignedValid.nil

def missing5233_5234 : List (BitVec (edgeCount 12)) :=
  [missing5233]
abbrev records5233_5234 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5233]
theorem aligned5233_5234 :
    AlignedValid 12 4 missing5233_5234 records5233_5234 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5233
    maskCheck5233 AlignedValid.nil

def missing5232_5234 : List (BitVec (edgeCount 12)) :=
  missing5232_5233 ++ missing5233_5234
abbrev records5232_5234 : List Blob :=
  records5232_5233 ++ records5233_5234
theorem aligned5232_5234 :
    AlignedValid 12 4 missing5232_5234 records5232_5234 :=
  aligned5232_5233.append aligned5233_5234

def missing5234_5235 : List (BitVec (edgeCount 12)) :=
  [missing5234]
abbrev records5234_5235 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5234]
theorem aligned5234_5235 :
    AlignedValid 12 4 missing5234_5235 records5234_5235 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5234
    maskCheck5234 AlignedValid.nil

def missing5235_5236 : List (BitVec (edgeCount 12)) :=
  [missing5235]
abbrev records5235_5236 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5235]
theorem aligned5235_5236 :
    AlignedValid 12 4 missing5235_5236 records5235_5236 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5235
    maskCheck5235 AlignedValid.nil

def missing5234_5236 : List (BitVec (edgeCount 12)) :=
  missing5234_5235 ++ missing5235_5236
abbrev records5234_5236 : List Blob :=
  records5234_5235 ++ records5235_5236
theorem aligned5234_5236 :
    AlignedValid 12 4 missing5234_5236 records5234_5236 :=
  aligned5234_5235.append aligned5235_5236

def missing5232_5236 : List (BitVec (edgeCount 12)) :=
  missing5232_5234 ++ missing5234_5236
abbrev records5232_5236 : List Blob :=
  records5232_5234 ++ records5234_5236
theorem aligned5232_5236 :
    AlignedValid 12 4 missing5232_5236 records5232_5236 :=
  aligned5232_5234.append aligned5234_5236

def missing5236_5237 : List (BitVec (edgeCount 12)) :=
  [missing5236]
abbrev records5236_5237 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5236]
theorem aligned5236_5237 :
    AlignedValid 12 4 missing5236_5237 records5236_5237 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5236
    maskCheck5236 AlignedValid.nil

def missing5237_5238 : List (BitVec (edgeCount 12)) :=
  [missing5237]
abbrev records5237_5238 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5237]
theorem aligned5237_5238 :
    AlignedValid 12 4 missing5237_5238 records5237_5238 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5237
    maskCheck5237 AlignedValid.nil

def missing5236_5238 : List (BitVec (edgeCount 12)) :=
  missing5236_5237 ++ missing5237_5238
abbrev records5236_5238 : List Blob :=
  records5236_5237 ++ records5237_5238
theorem aligned5236_5238 :
    AlignedValid 12 4 missing5236_5238 records5236_5238 :=
  aligned5236_5237.append aligned5237_5238

def missing5238_5239 : List (BitVec (edgeCount 12)) :=
  [missing5238]
abbrev records5238_5239 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5238]
theorem aligned5238_5239 :
    AlignedValid 12 4 missing5238_5239 records5238_5239 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5238
    maskCheck5238 AlignedValid.nil

def missing5239_5240 : List (BitVec (edgeCount 12)) :=
  [missing5239]
abbrev records5239_5240 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5239]
theorem aligned5239_5240 :
    AlignedValid 12 4 missing5239_5240 records5239_5240 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5239
    maskCheck5239 AlignedValid.nil

def missing5238_5240 : List (BitVec (edgeCount 12)) :=
  missing5238_5239 ++ missing5239_5240
abbrev records5238_5240 : List Blob :=
  records5238_5239 ++ records5239_5240
theorem aligned5238_5240 :
    AlignedValid 12 4 missing5238_5240 records5238_5240 :=
  aligned5238_5239.append aligned5239_5240

def missing5236_5240 : List (BitVec (edgeCount 12)) :=
  missing5236_5238 ++ missing5238_5240
abbrev records5236_5240 : List Blob :=
  records5236_5238 ++ records5238_5240
theorem aligned5236_5240 :
    AlignedValid 12 4 missing5236_5240 records5236_5240 :=
  aligned5236_5238.append aligned5238_5240

def missing5232_5240 : List (BitVec (edgeCount 12)) :=
  missing5232_5236 ++ missing5236_5240
abbrev records5232_5240 : List Blob :=
  records5232_5236 ++ records5236_5240
theorem aligned5232_5240 :
    AlignedValid 12 4 missing5232_5240 records5232_5240 :=
  aligned5232_5236.append aligned5236_5240

def missing5240_5241 : List (BitVec (edgeCount 12)) :=
  [missing5240]
abbrev records5240_5241 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5240]
theorem aligned5240_5241 :
    AlignedValid 12 4 missing5240_5241 records5240_5241 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5240
    maskCheck5240 AlignedValid.nil

def missing5241_5242 : List (BitVec (edgeCount 12)) :=
  [missing5241]
abbrev records5241_5242 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5241]
theorem aligned5241_5242 :
    AlignedValid 12 4 missing5241_5242 records5241_5242 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5241
    maskCheck5241 AlignedValid.nil

def missing5240_5242 : List (BitVec (edgeCount 12)) :=
  missing5240_5241 ++ missing5241_5242
abbrev records5240_5242 : List Blob :=
  records5240_5241 ++ records5241_5242
theorem aligned5240_5242 :
    AlignedValid 12 4 missing5240_5242 records5240_5242 :=
  aligned5240_5241.append aligned5241_5242

def missing5242_5243 : List (BitVec (edgeCount 12)) :=
  [missing5242]
abbrev records5242_5243 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5242]
theorem aligned5242_5243 :
    AlignedValid 12 4 missing5242_5243 records5242_5243 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5242
    maskCheck5242 AlignedValid.nil

def missing5243_5244 : List (BitVec (edgeCount 12)) :=
  [missing5243]
abbrev records5243_5244 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5243]
theorem aligned5243_5244 :
    AlignedValid 12 4 missing5243_5244 records5243_5244 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5243
    maskCheck5243 AlignedValid.nil

def missing5242_5244 : List (BitVec (edgeCount 12)) :=
  missing5242_5243 ++ missing5243_5244
abbrev records5242_5244 : List Blob :=
  records5242_5243 ++ records5243_5244
theorem aligned5242_5244 :
    AlignedValid 12 4 missing5242_5244 records5242_5244 :=
  aligned5242_5243.append aligned5243_5244

def missing5240_5244 : List (BitVec (edgeCount 12)) :=
  missing5240_5242 ++ missing5242_5244
abbrev records5240_5244 : List Blob :=
  records5240_5242 ++ records5242_5244
theorem aligned5240_5244 :
    AlignedValid 12 4 missing5240_5244 records5240_5244 :=
  aligned5240_5242.append aligned5242_5244

def missing5244_5245 : List (BitVec (edgeCount 12)) :=
  [missing5244]
abbrev records5244_5245 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5244]
theorem aligned5244_5245 :
    AlignedValid 12 4 missing5244_5245 records5244_5245 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5244
    maskCheck5244 AlignedValid.nil

def missing5245_5246 : List (BitVec (edgeCount 12)) :=
  [missing5245]
abbrev records5245_5246 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5245]
theorem aligned5245_5246 :
    AlignedValid 12 4 missing5245_5246 records5245_5246 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5245
    maskCheck5245 AlignedValid.nil

def missing5244_5246 : List (BitVec (edgeCount 12)) :=
  missing5244_5245 ++ missing5245_5246
abbrev records5244_5246 : List Blob :=
  records5244_5245 ++ records5245_5246
theorem aligned5244_5246 :
    AlignedValid 12 4 missing5244_5246 records5244_5246 :=
  aligned5244_5245.append aligned5245_5246

def missing5246_5247 : List (BitVec (edgeCount 12)) :=
  [missing5246]
abbrev records5246_5247 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5246]
theorem aligned5246_5247 :
    AlignedValid 12 4 missing5246_5247 records5246_5247 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5246
    maskCheck5246 AlignedValid.nil

def missing5247_5248 : List (BitVec (edgeCount 12)) :=
  [missing5247]
abbrev records5247_5248 : List Blob :=
  [StrongPackedBucketN12A4Shard040.record5247]
theorem aligned5247_5248 :
    AlignedValid 12 4 missing5247_5248 records5247_5248 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard040.check5247
    maskCheck5247 AlignedValid.nil

def missing5246_5248 : List (BitVec (edgeCount 12)) :=
  missing5246_5247 ++ missing5247_5248
abbrev records5246_5248 : List Blob :=
  records5246_5247 ++ records5247_5248
theorem aligned5246_5248 :
    AlignedValid 12 4 missing5246_5248 records5246_5248 :=
  aligned5246_5247.append aligned5247_5248

def missing5244_5248 : List (BitVec (edgeCount 12)) :=
  missing5244_5246 ++ missing5246_5248
abbrev records5244_5248 : List Blob :=
  records5244_5246 ++ records5246_5248
theorem aligned5244_5248 :
    AlignedValid 12 4 missing5244_5248 records5244_5248 :=
  aligned5244_5246.append aligned5246_5248

def missing5240_5248 : List (BitVec (edgeCount 12)) :=
  missing5240_5244 ++ missing5244_5248
abbrev records5240_5248 : List Blob :=
  records5240_5244 ++ records5244_5248
theorem aligned5240_5248 :
    AlignedValid 12 4 missing5240_5248 records5240_5248 :=
  aligned5240_5244.append aligned5244_5248

def missing5232_5248 : List (BitVec (edgeCount 12)) :=
  missing5232_5240 ++ missing5240_5248
abbrev records5232_5248 : List Blob :=
  records5232_5240 ++ records5240_5248
theorem aligned5232_5248 :
    AlignedValid 12 4 missing5232_5248 records5232_5248 :=
  aligned5232_5240.append aligned5240_5248

def missing5216_5248 : List (BitVec (edgeCount 12)) :=
  missing5216_5232 ++ missing5232_5248
abbrev records5216_5248 : List Blob :=
  records5216_5232 ++ records5232_5248
theorem aligned5216_5248 :
    AlignedValid 12 4 missing5216_5248 records5216_5248 :=
  aligned5216_5232.append aligned5232_5248

def missing5184_5248 : List (BitVec (edgeCount 12)) :=
  missing5184_5216 ++ missing5216_5248
abbrev records5184_5248 : List Blob :=
  records5184_5216 ++ records5216_5248
theorem aligned5184_5248 :
    AlignedValid 12 4 missing5184_5248 records5184_5248 :=
  aligned5184_5216.append aligned5216_5248

def missing5120_5248 : List (BitVec (edgeCount 12)) :=
  missing5120_5184 ++ missing5184_5248
abbrev records5120_5248 : List Blob :=
  records5120_5184 ++ records5184_5248
theorem aligned5120_5248 :
    AlignedValid 12 4 missing5120_5248 records5120_5248 :=
  aligned5120_5184.append aligned5184_5248

abbrev missing : List (BitVec (edgeCount 12)) := missing5120_5248
abbrev records : List Blob := records5120_5248
theorem aligned : AlignedValid 12 4 missing records := aligned5120_5248

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard040
