/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A3Shard048

/-! Decode-only alignment checks for n=12, a=3, records 6144--6271. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard048

open PackedBucketCertificate

def missing6144 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4400157917565681664
theorem maskCheck6144 :
    checkMaskFor missing6144 StrongPackedBucketN12A3Shard048.record6144 = true := by
  decide

def missing6145 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5156762654963924992
theorem maskCheck6145 :
    checkMaskFor missing6145 StrongPackedBucketN12A3Shard048.record6145 = true := by
  decide

def missing6146 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5589108219191492608
theorem maskCheck6146 :
    checkMaskFor missing6146 StrongPackedBucketN12A3Shard048.record6146 = true := by
  decide

def missing6147 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5661165813229420544
theorem maskCheck6147 :
    checkMaskFor missing6147 StrongPackedBucketN12A3Shard048.record6147 = true := by
  decide

def missing6148 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6669972129760411648
theorem maskCheck6148 :
    checkMaskFor missing6148 StrongPackedBucketN12A3Shard048.record6148 = true := by
  decide

def missing6149 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9768448673391312896
theorem maskCheck6149 :
    checkMaskFor missing6149 StrongPackedBucketN12A3Shard048.record6149 = true := by
  decide

def missing6150 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10200794237618880512
theorem maskCheck6150 :
    checkMaskFor missing6150 StrongPackedBucketN12A3Shard048.record6150 = true := by
  decide

def missing6151 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11317686945206763520
theorem maskCheck6151 :
    checkMaskFor missing6151 StrongPackedBucketN12A3Shard048.record6151 = true := by
  decide

def missing6152 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14091904315666989056
theorem maskCheck6152 :
    checkMaskFor missing6152 StrongPackedBucketN12A3Shard048.record6152 = true := by
  decide

def missing6153 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14236019503742844928
theorem maskCheck6153 :
    checkMaskFor missing6153 StrongPackedBucketN12A3Shard048.record6153 = true := by
  decide

def missing6154 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18991820710246088704
theorem maskCheck6154 :
    checkMaskFor missing6154 StrongPackedBucketN12A3Shard048.record6154 = true := by
  decide

def missing6155 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19496223868511584256
theorem maskCheck6155 :
    checkMaskFor missing6155 StrongPackedBucketN12A3Shard048.record6155 = true := by
  decide

def missing6156 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23315276352521764864
theorem maskCheck6156 :
    checkMaskFor missing6156 StrongPackedBucketN12A3Shard048.record6156 = true := by
  decide

def missing6157 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23531449134635548672
theorem maskCheck6157 :
    checkMaskFor missing6157 StrongPackedBucketN12A3Shard048.record6157 = true := by
  decide

def missing6158 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27926962370949152768
theorem maskCheck6158 :
    checkMaskFor missing6158 StrongPackedBucketN12A3Shard048.record6158 = true := by
  decide

def missing6159 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60136706905902940160
theorem maskCheck6159 :
    checkMaskFor missing6159 StrongPackedBucketN12A3Shard048.record6159 = true := by
  decide

def missing6160 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081110545309892608
theorem maskCheck6160 :
    checkMaskFor missing6160 StrongPackedBucketN12A3Shard048.record6160 = true := by
  decide

def missing6161 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2089916861840883712
theorem maskCheck6161 :
    checkMaskFor missing6161 StrongPackedBucketN12A3Shard048.record6161 = true := by
  decide

def missing6162 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2161974455878811648
theorem maskCheck6162 :
    checkMaskFor missing6162 StrongPackedBucketN12A3Shard048.record6162 = true := by
  decide

def missing6163 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4323702277016649728
theorem maskCheck6163 :
    checkMaskFor missing6163 StrongPackedBucketN12A3Shard048.record6163 = true := by
  decide

def missing6164 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5116335811433857024
theorem maskCheck6164 :
    checkMaskFor missing6164 StrongPackedBucketN12A3Shard048.record6164 = true := by
  decide

def missing6165 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5548681375661424640
theorem maskCheck6165 :
    checkMaskFor missing6165 StrongPackedBucketN12A3Shard048.record6165 = true := by
  decide

def missing6166 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5620738969699352576
theorem maskCheck6166 :
    checkMaskFor missing6166 StrongPackedBucketN12A3Shard048.record6166 = true := by
  decide

def missing6167 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6629545286230343680
theorem maskCheck6167 :
    checkMaskFor missing6167 StrongPackedBucketN12A3Shard048.record6167 = true := by
  decide

def missing6168 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9475820250728497152
theorem maskCheck6168 :
    checkMaskFor missing6168 StrongPackedBucketN12A3Shard048.record6168 = true := by
  decide

def missing6169 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9619935438804353024
theorem maskCheck6169 :
    checkMaskFor missing6169 StrongPackedBucketN12A3Shard048.record6169 = true := by
  decide

def missing6170 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9691993032842280960
theorem maskCheck6170 :
    checkMaskFor missing6170 StrongPackedBucketN12A3Shard048.record6170 = true := by
  decide

def missing6171 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9728021829861244928
theorem maskCheck6171 :
    checkMaskFor missing6171 StrongPackedBucketN12A3Shard048.record6171 = true := by
  decide

def missing6172 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10124338597069848576
theorem maskCheck6172 :
    checkMaskFor missing6172 StrongPackedBucketN12A3Shard048.record6172 = true := by
  decide

def missing6173 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10160367394088812544
theorem maskCheck6173 :
    checkMaskFor missing6173 StrongPackedBucketN12A3Shard048.record6173 = true := by
  decide

def missing6174 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10232424988126740480
theorem maskCheck6174 :
    checkMaskFor missing6174 StrongPackedBucketN12A3Shard048.record6174 = true := by
  decide

def missing6175 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11241231304657731584
theorem maskCheck6175 :
    checkMaskFor missing6175 StrongPackedBucketN12A3Shard048.record6175 = true := by
  decide

def missing6176 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13943391081080029184
theorem maskCheck6176 :
    checkMaskFor missing6176 StrongPackedBucketN12A3Shard048.record6176 = true := by
  decide

def missing6177 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14015448675117957120
theorem maskCheck6177 :
    checkMaskFor missing6177 StrongPackedBucketN12A3Shard048.record6177 = true := by
  decide

def missing6178 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14051477472136921088
theorem maskCheck6178 :
    checkMaskFor missing6178 StrongPackedBucketN12A3Shard048.record6178 = true := by
  decide

def missing6179 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14159563863193812992
theorem maskCheck6179 :
    checkMaskFor missing6179 StrongPackedBucketN12A3Shard048.record6179 = true := by
  decide

def missing6180 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14195592660212776960
theorem maskCheck6180 :
    checkMaskFor missing6180 StrongPackedBucketN12A3Shard048.record6180 = true := by
  decide

def missing6181 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14267650254250704896
theorem maskCheck6181 :
    checkMaskFor missing6181 StrongPackedBucketN12A3Shard048.record6181 = true := by
  decide

def missing6182 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14699995818478272512
theorem maskCheck6182 :
    checkMaskFor missing6182 StrongPackedBucketN12A3Shard048.record6182 = true := by
  decide

def missing6183 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699192287583272960
theorem maskCheck6183 :
    checkMaskFor missing6183 StrongPackedBucketN12A3Shard048.record6183 = true := by
  decide

def missing6184 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18843307475659128832
theorem maskCheck6184 :
    checkMaskFor missing6184 StrongPackedBucketN12A3Shard048.record6184 = true := by
  decide

def missing6185 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18915365069697056768
theorem maskCheck6185 :
    checkMaskFor missing6185 StrongPackedBucketN12A3Shard048.record6185 = true := by
  decide

def missing6186 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18951393866716020736
theorem maskCheck6186 :
    checkMaskFor missing6186 StrongPackedBucketN12A3Shard048.record6186 = true := by
  decide

def missing6187 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19347710633924624384
theorem maskCheck6187 :
    checkMaskFor missing6187 StrongPackedBucketN12A3Shard048.record6187 = true := by
  decide

def missing6188 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19383739430943588352
theorem maskCheck6188 :
    checkMaskFor missing6188 StrongPackedBucketN12A3Shard048.record6188 = true := by
  decide

def missing6189 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19455797024981516288
theorem maskCheck6189 :
    checkMaskFor missing6189 StrongPackedBucketN12A3Shard048.record6189 = true := by
  decide

def missing6190 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20464603341512507392
theorem maskCheck6190 :
    checkMaskFor missing6190 StrongPackedBucketN12A3Shard048.record6190 = true := by
  decide

def missing6191 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23166763117934804992
theorem maskCheck6191 :
    checkMaskFor missing6191 StrongPackedBucketN12A3Shard048.record6191 = true := by
  decide

def missing6192 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23238820711972732928
theorem maskCheck6192 :
    checkMaskFor missing6192 StrongPackedBucketN12A3Shard048.record6192 = true := by
  decide

def missing6193 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23274849508991696896
theorem maskCheck6193 :
    checkMaskFor missing6193 StrongPackedBucketN12A3Shard048.record6193 = true := by
  decide

def missing6194 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23382935900048588800
theorem maskCheck6194 :
    checkMaskFor missing6194 StrongPackedBucketN12A3Shard048.record6194 = true := by
  decide

def missing6195 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23418964697067552768
theorem maskCheck6195 :
    checkMaskFor missing6195 StrongPackedBucketN12A3Shard048.record6195 = true := by
  decide

def missing6196 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23491022291105480704
theorem maskCheck6196 :
    checkMaskFor missing6196 StrongPackedBucketN12A3Shard048.record6196 = true := by
  decide

def missing6197 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23923367855333048320
theorem maskCheck6197 :
    checkMaskFor missing6197 StrongPackedBucketN12A3Shard048.record6197 = true := by
  decide

def missing6198 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27778449136362192896
theorem maskCheck6198 :
    checkMaskFor missing6198 StrongPackedBucketN12A3Shard048.record6198 = true := by
  decide

def missing6199 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27850506730400120832
theorem maskCheck6199 :
    checkMaskFor missing6199 StrongPackedBucketN12A3Shard048.record6199 = true := by
  decide

def missing6200 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27886535527419084800
theorem maskCheck6200 :
    checkMaskFor missing6200 StrongPackedBucketN12A3Shard048.record6200 = true := by
  decide

def missing6201 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27994621918475976704
theorem maskCheck6201 :
    checkMaskFor missing6201 StrongPackedBucketN12A3Shard048.record6201 = true := by
  decide

def missing6202 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28030650715494940672
theorem maskCheck6202 :
    checkMaskFor missing6202 StrongPackedBucketN12A3Shard048.record6202 = true := by
  decide

def missing6203 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28102708309532868608
theorem maskCheck6203 :
    checkMaskFor missing6203 StrongPackedBucketN12A3Shard048.record6203 = true := by
  decide

def missing6204 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28535053873760436224
theorem maskCheck6204 :
    checkMaskFor missing6204 StrongPackedBucketN12A3Shard048.record6204 = true := by
  decide

def missing6205 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32318077560751652864
theorem maskCheck6205 :
    checkMaskFor missing6205 StrongPackedBucketN12A3Shard048.record6205 = true := by
  decide

def missing6206 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32354106357770616832
theorem maskCheck6206 :
    checkMaskFor missing6206 StrongPackedBucketN12A3Shard048.record6206 = true := by
  decide

def missing6207 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32426163951808544768
theorem maskCheck6207 :
    checkMaskFor missing6207 StrongPackedBucketN12A3Shard048.record6207 = true := by
  decide

def missing6208 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32570279139884400640
theorem maskCheck6208 :
    checkMaskFor missing6208 StrongPackedBucketN12A3Shard048.record6208 = true := by
  decide

def missing6209 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37145936361292824576
theorem maskCheck6209 :
    checkMaskFor missing6209 StrongPackedBucketN12A3Shard048.record6209 = true := by
  decide

def missing6210 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41721593582701248512
theorem maskCheck6210 :
    checkMaskFor missing6210 StrongPackedBucketN12A3Shard048.record6210 = true := by
  decide

def missing6211 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46225193210071744512
theorem maskCheck6211 :
    checkMaskFor missing6211 StrongPackedBucketN12A3Shard048.record6211 = true := by
  decide

def missing6212 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46297250804109672448
theorem maskCheck6212 :
    checkMaskFor missing6212 StrongPackedBucketN12A3Shard048.record6212 = true := by
  decide

def missing6213 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46333279601128636416
theorem maskCheck6213 :
    checkMaskFor missing6213 StrongPackedBucketN12A3Shard048.record6213 = true := by
  decide

def missing6214 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46477394789204492288
theorem maskCheck6214 :
    checkMaskFor missing6214 StrongPackedBucketN12A3Shard048.record6214 = true := by
  decide

def missing6215 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50800850431480168448
theorem maskCheck6215 :
    checkMaskFor missing6215 StrongPackedBucketN12A3Shard048.record6215 = true := by
  decide

def missing6216 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50872908025518096384
theorem maskCheck6216 :
    checkMaskFor missing6216 StrongPackedBucketN12A3Shard048.record6216 = true := by
  decide

def missing6217 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55556651637983412224
theorem maskCheck6217 :
    checkMaskFor missing6217 StrongPackedBucketN12A3Shard048.record6217 = true := by
  decide

def missing6218 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60024222468334944256
theorem maskCheck6218 :
    checkMaskFor missing6218 StrongPackedBucketN12A3Shard048.record6218 = true := by
  decide

def missing6219 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64635908486762332160
theorem maskCheck6219 :
    checkMaskFor missing6219 StrongPackedBucketN12A3Shard048.record6219 = true := by
  decide

def missing6220 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64707966080800260096
theorem maskCheck6220 :
    checkMaskFor missing6220 StrongPackedBucketN12A3Shard048.record6220 = true := by
  decide

def missing6221 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 69175536911151792128
theorem maskCheck6221 :
    checkMaskFor missing6221 StrongPackedBucketN12A3Shard048.record6221 = true := by
  decide

def missing6222 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 540819327513788416
theorem maskCheck6222 :
    checkMaskFor missing6222 StrongPackedBucketN12A3Shard048.record6222 = true := by
  decide

def missing6223 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 829049703665500160
theorem maskCheck6223 :
    checkMaskFor missing6223 StrongPackedBucketN12A3Shard048.record6223 = true := by
  decide

def missing6224 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1045222485779283968
theorem maskCheck6224 :
    checkMaskFor missing6224 StrongPackedBucketN12A3Shard048.record6224 = true := by
  decide

def missing6225 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081251282798247936
theorem maskCheck6225 :
    checkMaskFor missing6225 StrongPackedBucketN12A3Shard048.record6225 = true := by
  decide

def missing6226 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1945942411253383168
theorem maskCheck6226 :
    checkMaskFor missing6226 StrongPackedBucketN12A3Shard048.record6226 = true := by
  decide

def missing6227 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2090057599329239040
theorem maskCheck6227 :
    checkMaskFor missing6227 StrongPackedBucketN12A3Shard048.record6227 = true := by
  decide

def missing6228 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2162115193367166976
theorem maskCheck6228 :
    checkMaskFor missing6228 StrongPackedBucketN12A3Shard048.record6228 = true := by
  decide

def missing6229 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4107670232391221248
theorem maskCheck6229 :
    checkMaskFor missing6229 StrongPackedBucketN12A3Shard048.record6229 = true := by
  decide

def missing6230 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4179727826429149184
theorem maskCheck6230 :
    checkMaskFor missing6230 StrongPackedBucketN12A3Shard048.record6230 = true := by
  decide

def missing6231 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4323843014505005056
theorem maskCheck6231 :
    checkMaskFor missing6231 StrongPackedBucketN12A3Shard048.record6231 = true := by
  decide

def missing6232 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4864274969789464576
theorem maskCheck6232 :
    checkMaskFor missing6232 StrongPackedBucketN12A3Shard048.record6232 = true := by
  decide

def missing6233 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5080447751903248384
theorem maskCheck6233 :
    checkMaskFor missing6233 StrongPackedBucketN12A3Shard048.record6233 = true := by
  decide

def missing6234 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5116476548922212352
theorem maskCheck6234 :
    checkMaskFor missing6234 StrongPackedBucketN12A3Shard048.record6234 = true := by
  decide

def missing6235 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5404706925073924096
theorem maskCheck6235 :
    checkMaskFor missing6235 StrongPackedBucketN12A3Shard048.record6235 = true := by
  decide

def missing6236 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5548822113149779968
theorem maskCheck6236 :
    checkMaskFor missing6236 StrongPackedBucketN12A3Shard048.record6236 = true := by
  decide

def missing6237 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5620879707187707904
theorem maskCheck6237 :
    checkMaskFor missing6237 StrongPackedBucketN12A3Shard048.record6237 = true := by
  decide

def missing6238 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6413513241604915200
theorem maskCheck6238 :
    checkMaskFor missing6238 StrongPackedBucketN12A3Shard048.record6238 = true := by
  decide

def missing6239 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6485570835642843136
theorem maskCheck6239 :
    checkMaskFor missing6239 StrongPackedBucketN12A3Shard048.record6239 = true := by
  decide

def missing6240 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6629686023718699008
theorem maskCheck6240 :
    checkMaskFor missing6240 StrongPackedBucketN12A3Shard048.record6240 = true := by
  decide

def missing6241 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9475960988216852480
theorem maskCheck6241 :
    checkMaskFor missing6241 StrongPackedBucketN12A3Shard048.record6241 = true := by
  decide

def missing6242 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9620076176292708352
theorem maskCheck6242 :
    checkMaskFor missing6242 StrongPackedBucketN12A3Shard048.record6242 = true := by
  decide

def missing6243 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9692133770330636288
theorem maskCheck6243 :
    checkMaskFor missing6243 StrongPackedBucketN12A3Shard048.record6243 = true := by
  decide

def missing6244 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9728162567349600256
theorem maskCheck6244 :
    checkMaskFor missing6244 StrongPackedBucketN12A3Shard048.record6244 = true := by
  decide

def missing6245 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9980364146482348032
theorem maskCheck6245 :
    checkMaskFor missing6245 StrongPackedBucketN12A3Shard048.record6245 = true := by
  decide

def missing6246 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10016392943501312000
theorem maskCheck6246 :
    checkMaskFor missing6246 StrongPackedBucketN12A3Shard048.record6246 = true := by
  decide

def missing6247 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10124479334558203904
theorem maskCheck6247 :
    checkMaskFor missing6247 StrongPackedBucketN12A3Shard048.record6247 = true := by
  decide

def missing6248 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10160508131577167872
theorem maskCheck6248 :
    checkMaskFor missing6248 StrongPackedBucketN12A3Shard048.record6248 = true := by
  decide

def missing6249 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10232565725615095808
theorem maskCheck6249 :
    checkMaskFor missing6249 StrongPackedBucketN12A3Shard048.record6249 = true := by
  decide

def missing6250 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11025199260032303104
theorem maskCheck6250 :
    checkMaskFor missing6250 StrongPackedBucketN12A3Shard048.record6250 = true := by
  decide

def missing6251 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11097256854070231040
theorem maskCheck6251 :
    checkMaskFor missing6251 StrongPackedBucketN12A3Shard048.record6251 = true := by
  decide

def missing6252 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14015589412606312448
theorem maskCheck6252 :
    checkMaskFor missing6252 StrongPackedBucketN12A3Shard048.record6252 = true := by
  decide

def missing6253 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14051618209625276416
theorem maskCheck6253 :
    checkMaskFor missing6253 StrongPackedBucketN12A3Shard048.record6253 = true := by
  decide

def missing6254 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14159704600682168320
theorem maskCheck6254 :
    checkMaskFor missing6254 StrongPackedBucketN12A3Shard048.record6254 = true := by
  decide

def missing6255 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14195733397701132288
theorem maskCheck6255 :
    checkMaskFor missing6255 StrongPackedBucketN12A3Shard048.record6255 = true := by
  decide

def missing6256 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14267790991739060224
theorem maskCheck6256 :
    checkMaskFor missing6256 StrongPackedBucketN12A3Shard048.record6256 = true := by
  decide

def missing6257 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14483963773852844032
theorem maskCheck6257 :
    checkMaskFor missing6257 StrongPackedBucketN12A3Shard048.record6257 = true := by
  decide

def missing6258 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699333025071628288
theorem maskCheck6258 :
    checkMaskFor missing6258 StrongPackedBucketN12A3Shard048.record6258 = true := by
  decide

def missing6259 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18843448213147484160
theorem maskCheck6259 :
    checkMaskFor missing6259 StrongPackedBucketN12A3Shard048.record6259 = true := by
  decide

def missing6260 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18915505807185412096
theorem maskCheck6260 :
    checkMaskFor missing6260 StrongPackedBucketN12A3Shard048.record6260 = true := by
  decide

def missing6261 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18951534604204376064
theorem maskCheck6261 :
    checkMaskFor missing6261 StrongPackedBucketN12A3Shard048.record6261 = true := by
  decide

def missing6262 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19131678589299195904
theorem maskCheck6262 :
    checkMaskFor missing6262 StrongPackedBucketN12A3Shard048.record6262 = true := by
  decide

def missing6263 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19203736183337123840
theorem maskCheck6263 :
    checkMaskFor missing6263 StrongPackedBucketN12A3Shard048.record6263 = true := by
  decide

def missing6264 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19239764980356087808
theorem maskCheck6264 :
    checkMaskFor missing6264 StrongPackedBucketN12A3Shard048.record6264 = true := by
  decide

def missing6265 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19347851371412979712
theorem maskCheck6265 :
    checkMaskFor missing6265 StrongPackedBucketN12A3Shard048.record6265 = true := by
  decide

def missing6266 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19383880168431943680
theorem maskCheck6266 :
    checkMaskFor missing6266 StrongPackedBucketN12A3Shard048.record6266 = true := by
  decide

def missing6267 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20248571296887078912
theorem maskCheck6267 :
    checkMaskFor missing6267 StrongPackedBucketN12A3Shard048.record6267 = true := by
  decide

def missing6268 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23166903855423160320
theorem maskCheck6268 :
    checkMaskFor missing6268 StrongPackedBucketN12A3Shard048.record6268 = true := by
  decide

def missing6269 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23238961449461088256
theorem maskCheck6269 :
    checkMaskFor missing6269 StrongPackedBucketN12A3Shard048.record6269 = true := by
  decide

def missing6270 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23274990246480052224
theorem maskCheck6270 :
    checkMaskFor missing6270 StrongPackedBucketN12A3Shard048.record6270 = true := by
  decide

def missing6271 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23383076637536944128
theorem maskCheck6271 :
    checkMaskFor missing6271 StrongPackedBucketN12A3Shard048.record6271 = true := by
  decide

def missing6144_6145 : List (BitVec (edgeCount 12)) :=
  [missing6144]
abbrev records6144_6145 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6144]
theorem aligned6144_6145 :
    AlignedValid 12 3 missing6144_6145 records6144_6145 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6144
    maskCheck6144 AlignedValid.nil

def missing6145_6146 : List (BitVec (edgeCount 12)) :=
  [missing6145]
abbrev records6145_6146 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6145]
theorem aligned6145_6146 :
    AlignedValid 12 3 missing6145_6146 records6145_6146 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6145
    maskCheck6145 AlignedValid.nil

def missing6144_6146 : List (BitVec (edgeCount 12)) :=
  missing6144_6145 ++ missing6145_6146
abbrev records6144_6146 : List Blob :=
  records6144_6145 ++ records6145_6146
theorem aligned6144_6146 :
    AlignedValid 12 3 missing6144_6146 records6144_6146 :=
  aligned6144_6145.append aligned6145_6146

def missing6146_6147 : List (BitVec (edgeCount 12)) :=
  [missing6146]
abbrev records6146_6147 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6146]
theorem aligned6146_6147 :
    AlignedValid 12 3 missing6146_6147 records6146_6147 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6146
    maskCheck6146 AlignedValid.nil

def missing6147_6148 : List (BitVec (edgeCount 12)) :=
  [missing6147]
abbrev records6147_6148 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6147]
theorem aligned6147_6148 :
    AlignedValid 12 3 missing6147_6148 records6147_6148 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6147
    maskCheck6147 AlignedValid.nil

def missing6146_6148 : List (BitVec (edgeCount 12)) :=
  missing6146_6147 ++ missing6147_6148
abbrev records6146_6148 : List Blob :=
  records6146_6147 ++ records6147_6148
theorem aligned6146_6148 :
    AlignedValid 12 3 missing6146_6148 records6146_6148 :=
  aligned6146_6147.append aligned6147_6148

def missing6144_6148 : List (BitVec (edgeCount 12)) :=
  missing6144_6146 ++ missing6146_6148
abbrev records6144_6148 : List Blob :=
  records6144_6146 ++ records6146_6148
theorem aligned6144_6148 :
    AlignedValid 12 3 missing6144_6148 records6144_6148 :=
  aligned6144_6146.append aligned6146_6148

def missing6148_6149 : List (BitVec (edgeCount 12)) :=
  [missing6148]
abbrev records6148_6149 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6148]
theorem aligned6148_6149 :
    AlignedValid 12 3 missing6148_6149 records6148_6149 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6148
    maskCheck6148 AlignedValid.nil

def missing6149_6150 : List (BitVec (edgeCount 12)) :=
  [missing6149]
abbrev records6149_6150 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6149]
theorem aligned6149_6150 :
    AlignedValid 12 3 missing6149_6150 records6149_6150 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6149
    maskCheck6149 AlignedValid.nil

def missing6148_6150 : List (BitVec (edgeCount 12)) :=
  missing6148_6149 ++ missing6149_6150
abbrev records6148_6150 : List Blob :=
  records6148_6149 ++ records6149_6150
theorem aligned6148_6150 :
    AlignedValid 12 3 missing6148_6150 records6148_6150 :=
  aligned6148_6149.append aligned6149_6150

def missing6150_6151 : List (BitVec (edgeCount 12)) :=
  [missing6150]
abbrev records6150_6151 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6150]
theorem aligned6150_6151 :
    AlignedValid 12 3 missing6150_6151 records6150_6151 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6150
    maskCheck6150 AlignedValid.nil

def missing6151_6152 : List (BitVec (edgeCount 12)) :=
  [missing6151]
abbrev records6151_6152 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6151]
theorem aligned6151_6152 :
    AlignedValid 12 3 missing6151_6152 records6151_6152 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6151
    maskCheck6151 AlignedValid.nil

def missing6150_6152 : List (BitVec (edgeCount 12)) :=
  missing6150_6151 ++ missing6151_6152
abbrev records6150_6152 : List Blob :=
  records6150_6151 ++ records6151_6152
theorem aligned6150_6152 :
    AlignedValid 12 3 missing6150_6152 records6150_6152 :=
  aligned6150_6151.append aligned6151_6152

def missing6148_6152 : List (BitVec (edgeCount 12)) :=
  missing6148_6150 ++ missing6150_6152
abbrev records6148_6152 : List Blob :=
  records6148_6150 ++ records6150_6152
theorem aligned6148_6152 :
    AlignedValid 12 3 missing6148_6152 records6148_6152 :=
  aligned6148_6150.append aligned6150_6152

def missing6144_6152 : List (BitVec (edgeCount 12)) :=
  missing6144_6148 ++ missing6148_6152
abbrev records6144_6152 : List Blob :=
  records6144_6148 ++ records6148_6152
theorem aligned6144_6152 :
    AlignedValid 12 3 missing6144_6152 records6144_6152 :=
  aligned6144_6148.append aligned6148_6152

def missing6152_6153 : List (BitVec (edgeCount 12)) :=
  [missing6152]
abbrev records6152_6153 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6152]
theorem aligned6152_6153 :
    AlignedValid 12 3 missing6152_6153 records6152_6153 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6152
    maskCheck6152 AlignedValid.nil

def missing6153_6154 : List (BitVec (edgeCount 12)) :=
  [missing6153]
abbrev records6153_6154 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6153]
theorem aligned6153_6154 :
    AlignedValid 12 3 missing6153_6154 records6153_6154 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6153
    maskCheck6153 AlignedValid.nil

def missing6152_6154 : List (BitVec (edgeCount 12)) :=
  missing6152_6153 ++ missing6153_6154
abbrev records6152_6154 : List Blob :=
  records6152_6153 ++ records6153_6154
theorem aligned6152_6154 :
    AlignedValid 12 3 missing6152_6154 records6152_6154 :=
  aligned6152_6153.append aligned6153_6154

def missing6154_6155 : List (BitVec (edgeCount 12)) :=
  [missing6154]
abbrev records6154_6155 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6154]
theorem aligned6154_6155 :
    AlignedValid 12 3 missing6154_6155 records6154_6155 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6154
    maskCheck6154 AlignedValid.nil

def missing6155_6156 : List (BitVec (edgeCount 12)) :=
  [missing6155]
abbrev records6155_6156 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6155]
theorem aligned6155_6156 :
    AlignedValid 12 3 missing6155_6156 records6155_6156 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6155
    maskCheck6155 AlignedValid.nil

def missing6154_6156 : List (BitVec (edgeCount 12)) :=
  missing6154_6155 ++ missing6155_6156
abbrev records6154_6156 : List Blob :=
  records6154_6155 ++ records6155_6156
theorem aligned6154_6156 :
    AlignedValid 12 3 missing6154_6156 records6154_6156 :=
  aligned6154_6155.append aligned6155_6156

def missing6152_6156 : List (BitVec (edgeCount 12)) :=
  missing6152_6154 ++ missing6154_6156
abbrev records6152_6156 : List Blob :=
  records6152_6154 ++ records6154_6156
theorem aligned6152_6156 :
    AlignedValid 12 3 missing6152_6156 records6152_6156 :=
  aligned6152_6154.append aligned6154_6156

def missing6156_6157 : List (BitVec (edgeCount 12)) :=
  [missing6156]
abbrev records6156_6157 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6156]
theorem aligned6156_6157 :
    AlignedValid 12 3 missing6156_6157 records6156_6157 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6156
    maskCheck6156 AlignedValid.nil

def missing6157_6158 : List (BitVec (edgeCount 12)) :=
  [missing6157]
abbrev records6157_6158 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6157]
theorem aligned6157_6158 :
    AlignedValid 12 3 missing6157_6158 records6157_6158 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6157
    maskCheck6157 AlignedValid.nil

def missing6156_6158 : List (BitVec (edgeCount 12)) :=
  missing6156_6157 ++ missing6157_6158
abbrev records6156_6158 : List Blob :=
  records6156_6157 ++ records6157_6158
theorem aligned6156_6158 :
    AlignedValid 12 3 missing6156_6158 records6156_6158 :=
  aligned6156_6157.append aligned6157_6158

def missing6158_6159 : List (BitVec (edgeCount 12)) :=
  [missing6158]
abbrev records6158_6159 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6158]
theorem aligned6158_6159 :
    AlignedValid 12 3 missing6158_6159 records6158_6159 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6158
    maskCheck6158 AlignedValid.nil

def missing6159_6160 : List (BitVec (edgeCount 12)) :=
  [missing6159]
abbrev records6159_6160 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6159]
theorem aligned6159_6160 :
    AlignedValid 12 3 missing6159_6160 records6159_6160 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6159
    maskCheck6159 AlignedValid.nil

def missing6158_6160 : List (BitVec (edgeCount 12)) :=
  missing6158_6159 ++ missing6159_6160
abbrev records6158_6160 : List Blob :=
  records6158_6159 ++ records6159_6160
theorem aligned6158_6160 :
    AlignedValid 12 3 missing6158_6160 records6158_6160 :=
  aligned6158_6159.append aligned6159_6160

def missing6156_6160 : List (BitVec (edgeCount 12)) :=
  missing6156_6158 ++ missing6158_6160
abbrev records6156_6160 : List Blob :=
  records6156_6158 ++ records6158_6160
theorem aligned6156_6160 :
    AlignedValid 12 3 missing6156_6160 records6156_6160 :=
  aligned6156_6158.append aligned6158_6160

def missing6152_6160 : List (BitVec (edgeCount 12)) :=
  missing6152_6156 ++ missing6156_6160
abbrev records6152_6160 : List Blob :=
  records6152_6156 ++ records6156_6160
theorem aligned6152_6160 :
    AlignedValid 12 3 missing6152_6160 records6152_6160 :=
  aligned6152_6156.append aligned6156_6160

def missing6144_6160 : List (BitVec (edgeCount 12)) :=
  missing6144_6152 ++ missing6152_6160
abbrev records6144_6160 : List Blob :=
  records6144_6152 ++ records6152_6160
theorem aligned6144_6160 :
    AlignedValid 12 3 missing6144_6160 records6144_6160 :=
  aligned6144_6152.append aligned6152_6160

def missing6160_6161 : List (BitVec (edgeCount 12)) :=
  [missing6160]
abbrev records6160_6161 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6160]
theorem aligned6160_6161 :
    AlignedValid 12 3 missing6160_6161 records6160_6161 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6160
    maskCheck6160 AlignedValid.nil

def missing6161_6162 : List (BitVec (edgeCount 12)) :=
  [missing6161]
abbrev records6161_6162 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6161]
theorem aligned6161_6162 :
    AlignedValid 12 3 missing6161_6162 records6161_6162 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6161
    maskCheck6161 AlignedValid.nil

def missing6160_6162 : List (BitVec (edgeCount 12)) :=
  missing6160_6161 ++ missing6161_6162
abbrev records6160_6162 : List Blob :=
  records6160_6161 ++ records6161_6162
theorem aligned6160_6162 :
    AlignedValid 12 3 missing6160_6162 records6160_6162 :=
  aligned6160_6161.append aligned6161_6162

def missing6162_6163 : List (BitVec (edgeCount 12)) :=
  [missing6162]
abbrev records6162_6163 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6162]
theorem aligned6162_6163 :
    AlignedValid 12 3 missing6162_6163 records6162_6163 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6162
    maskCheck6162 AlignedValid.nil

def missing6163_6164 : List (BitVec (edgeCount 12)) :=
  [missing6163]
abbrev records6163_6164 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6163]
theorem aligned6163_6164 :
    AlignedValid 12 3 missing6163_6164 records6163_6164 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6163
    maskCheck6163 AlignedValid.nil

def missing6162_6164 : List (BitVec (edgeCount 12)) :=
  missing6162_6163 ++ missing6163_6164
abbrev records6162_6164 : List Blob :=
  records6162_6163 ++ records6163_6164
theorem aligned6162_6164 :
    AlignedValid 12 3 missing6162_6164 records6162_6164 :=
  aligned6162_6163.append aligned6163_6164

def missing6160_6164 : List (BitVec (edgeCount 12)) :=
  missing6160_6162 ++ missing6162_6164
abbrev records6160_6164 : List Blob :=
  records6160_6162 ++ records6162_6164
theorem aligned6160_6164 :
    AlignedValid 12 3 missing6160_6164 records6160_6164 :=
  aligned6160_6162.append aligned6162_6164

def missing6164_6165 : List (BitVec (edgeCount 12)) :=
  [missing6164]
abbrev records6164_6165 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6164]
theorem aligned6164_6165 :
    AlignedValid 12 3 missing6164_6165 records6164_6165 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6164
    maskCheck6164 AlignedValid.nil

def missing6165_6166 : List (BitVec (edgeCount 12)) :=
  [missing6165]
abbrev records6165_6166 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6165]
theorem aligned6165_6166 :
    AlignedValid 12 3 missing6165_6166 records6165_6166 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6165
    maskCheck6165 AlignedValid.nil

def missing6164_6166 : List (BitVec (edgeCount 12)) :=
  missing6164_6165 ++ missing6165_6166
abbrev records6164_6166 : List Blob :=
  records6164_6165 ++ records6165_6166
theorem aligned6164_6166 :
    AlignedValid 12 3 missing6164_6166 records6164_6166 :=
  aligned6164_6165.append aligned6165_6166

def missing6166_6167 : List (BitVec (edgeCount 12)) :=
  [missing6166]
abbrev records6166_6167 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6166]
theorem aligned6166_6167 :
    AlignedValid 12 3 missing6166_6167 records6166_6167 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6166
    maskCheck6166 AlignedValid.nil

def missing6167_6168 : List (BitVec (edgeCount 12)) :=
  [missing6167]
abbrev records6167_6168 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6167]
theorem aligned6167_6168 :
    AlignedValid 12 3 missing6167_6168 records6167_6168 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6167
    maskCheck6167 AlignedValid.nil

def missing6166_6168 : List (BitVec (edgeCount 12)) :=
  missing6166_6167 ++ missing6167_6168
abbrev records6166_6168 : List Blob :=
  records6166_6167 ++ records6167_6168
theorem aligned6166_6168 :
    AlignedValid 12 3 missing6166_6168 records6166_6168 :=
  aligned6166_6167.append aligned6167_6168

def missing6164_6168 : List (BitVec (edgeCount 12)) :=
  missing6164_6166 ++ missing6166_6168
abbrev records6164_6168 : List Blob :=
  records6164_6166 ++ records6166_6168
theorem aligned6164_6168 :
    AlignedValid 12 3 missing6164_6168 records6164_6168 :=
  aligned6164_6166.append aligned6166_6168

def missing6160_6168 : List (BitVec (edgeCount 12)) :=
  missing6160_6164 ++ missing6164_6168
abbrev records6160_6168 : List Blob :=
  records6160_6164 ++ records6164_6168
theorem aligned6160_6168 :
    AlignedValid 12 3 missing6160_6168 records6160_6168 :=
  aligned6160_6164.append aligned6164_6168

def missing6168_6169 : List (BitVec (edgeCount 12)) :=
  [missing6168]
abbrev records6168_6169 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6168]
theorem aligned6168_6169 :
    AlignedValid 12 3 missing6168_6169 records6168_6169 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6168
    maskCheck6168 AlignedValid.nil

def missing6169_6170 : List (BitVec (edgeCount 12)) :=
  [missing6169]
abbrev records6169_6170 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6169]
theorem aligned6169_6170 :
    AlignedValid 12 3 missing6169_6170 records6169_6170 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6169
    maskCheck6169 AlignedValid.nil

def missing6168_6170 : List (BitVec (edgeCount 12)) :=
  missing6168_6169 ++ missing6169_6170
abbrev records6168_6170 : List Blob :=
  records6168_6169 ++ records6169_6170
theorem aligned6168_6170 :
    AlignedValid 12 3 missing6168_6170 records6168_6170 :=
  aligned6168_6169.append aligned6169_6170

def missing6170_6171 : List (BitVec (edgeCount 12)) :=
  [missing6170]
abbrev records6170_6171 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6170]
theorem aligned6170_6171 :
    AlignedValid 12 3 missing6170_6171 records6170_6171 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6170
    maskCheck6170 AlignedValid.nil

def missing6171_6172 : List (BitVec (edgeCount 12)) :=
  [missing6171]
abbrev records6171_6172 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6171]
theorem aligned6171_6172 :
    AlignedValid 12 3 missing6171_6172 records6171_6172 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6171
    maskCheck6171 AlignedValid.nil

def missing6170_6172 : List (BitVec (edgeCount 12)) :=
  missing6170_6171 ++ missing6171_6172
abbrev records6170_6172 : List Blob :=
  records6170_6171 ++ records6171_6172
theorem aligned6170_6172 :
    AlignedValid 12 3 missing6170_6172 records6170_6172 :=
  aligned6170_6171.append aligned6171_6172

def missing6168_6172 : List (BitVec (edgeCount 12)) :=
  missing6168_6170 ++ missing6170_6172
abbrev records6168_6172 : List Blob :=
  records6168_6170 ++ records6170_6172
theorem aligned6168_6172 :
    AlignedValid 12 3 missing6168_6172 records6168_6172 :=
  aligned6168_6170.append aligned6170_6172

def missing6172_6173 : List (BitVec (edgeCount 12)) :=
  [missing6172]
abbrev records6172_6173 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6172]
theorem aligned6172_6173 :
    AlignedValid 12 3 missing6172_6173 records6172_6173 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6172
    maskCheck6172 AlignedValid.nil

def missing6173_6174 : List (BitVec (edgeCount 12)) :=
  [missing6173]
abbrev records6173_6174 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6173]
theorem aligned6173_6174 :
    AlignedValid 12 3 missing6173_6174 records6173_6174 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6173
    maskCheck6173 AlignedValid.nil

def missing6172_6174 : List (BitVec (edgeCount 12)) :=
  missing6172_6173 ++ missing6173_6174
abbrev records6172_6174 : List Blob :=
  records6172_6173 ++ records6173_6174
theorem aligned6172_6174 :
    AlignedValid 12 3 missing6172_6174 records6172_6174 :=
  aligned6172_6173.append aligned6173_6174

def missing6174_6175 : List (BitVec (edgeCount 12)) :=
  [missing6174]
abbrev records6174_6175 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6174]
theorem aligned6174_6175 :
    AlignedValid 12 3 missing6174_6175 records6174_6175 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6174
    maskCheck6174 AlignedValid.nil

def missing6175_6176 : List (BitVec (edgeCount 12)) :=
  [missing6175]
abbrev records6175_6176 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6175]
theorem aligned6175_6176 :
    AlignedValid 12 3 missing6175_6176 records6175_6176 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6175
    maskCheck6175 AlignedValid.nil

def missing6174_6176 : List (BitVec (edgeCount 12)) :=
  missing6174_6175 ++ missing6175_6176
abbrev records6174_6176 : List Blob :=
  records6174_6175 ++ records6175_6176
theorem aligned6174_6176 :
    AlignedValid 12 3 missing6174_6176 records6174_6176 :=
  aligned6174_6175.append aligned6175_6176

def missing6172_6176 : List (BitVec (edgeCount 12)) :=
  missing6172_6174 ++ missing6174_6176
abbrev records6172_6176 : List Blob :=
  records6172_6174 ++ records6174_6176
theorem aligned6172_6176 :
    AlignedValid 12 3 missing6172_6176 records6172_6176 :=
  aligned6172_6174.append aligned6174_6176

def missing6168_6176 : List (BitVec (edgeCount 12)) :=
  missing6168_6172 ++ missing6172_6176
abbrev records6168_6176 : List Blob :=
  records6168_6172 ++ records6172_6176
theorem aligned6168_6176 :
    AlignedValid 12 3 missing6168_6176 records6168_6176 :=
  aligned6168_6172.append aligned6172_6176

def missing6160_6176 : List (BitVec (edgeCount 12)) :=
  missing6160_6168 ++ missing6168_6176
abbrev records6160_6176 : List Blob :=
  records6160_6168 ++ records6168_6176
theorem aligned6160_6176 :
    AlignedValid 12 3 missing6160_6176 records6160_6176 :=
  aligned6160_6168.append aligned6168_6176

def missing6144_6176 : List (BitVec (edgeCount 12)) :=
  missing6144_6160 ++ missing6160_6176
abbrev records6144_6176 : List Blob :=
  records6144_6160 ++ records6160_6176
theorem aligned6144_6176 :
    AlignedValid 12 3 missing6144_6176 records6144_6176 :=
  aligned6144_6160.append aligned6160_6176

def missing6176_6177 : List (BitVec (edgeCount 12)) :=
  [missing6176]
abbrev records6176_6177 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6176]
theorem aligned6176_6177 :
    AlignedValid 12 3 missing6176_6177 records6176_6177 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6176
    maskCheck6176 AlignedValid.nil

def missing6177_6178 : List (BitVec (edgeCount 12)) :=
  [missing6177]
abbrev records6177_6178 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6177]
theorem aligned6177_6178 :
    AlignedValid 12 3 missing6177_6178 records6177_6178 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6177
    maskCheck6177 AlignedValid.nil

def missing6176_6178 : List (BitVec (edgeCount 12)) :=
  missing6176_6177 ++ missing6177_6178
abbrev records6176_6178 : List Blob :=
  records6176_6177 ++ records6177_6178
theorem aligned6176_6178 :
    AlignedValid 12 3 missing6176_6178 records6176_6178 :=
  aligned6176_6177.append aligned6177_6178

def missing6178_6179 : List (BitVec (edgeCount 12)) :=
  [missing6178]
abbrev records6178_6179 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6178]
theorem aligned6178_6179 :
    AlignedValid 12 3 missing6178_6179 records6178_6179 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6178
    maskCheck6178 AlignedValid.nil

def missing6179_6180 : List (BitVec (edgeCount 12)) :=
  [missing6179]
abbrev records6179_6180 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6179]
theorem aligned6179_6180 :
    AlignedValid 12 3 missing6179_6180 records6179_6180 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6179
    maskCheck6179 AlignedValid.nil

def missing6178_6180 : List (BitVec (edgeCount 12)) :=
  missing6178_6179 ++ missing6179_6180
abbrev records6178_6180 : List Blob :=
  records6178_6179 ++ records6179_6180
theorem aligned6178_6180 :
    AlignedValid 12 3 missing6178_6180 records6178_6180 :=
  aligned6178_6179.append aligned6179_6180

def missing6176_6180 : List (BitVec (edgeCount 12)) :=
  missing6176_6178 ++ missing6178_6180
abbrev records6176_6180 : List Blob :=
  records6176_6178 ++ records6178_6180
theorem aligned6176_6180 :
    AlignedValid 12 3 missing6176_6180 records6176_6180 :=
  aligned6176_6178.append aligned6178_6180

def missing6180_6181 : List (BitVec (edgeCount 12)) :=
  [missing6180]
abbrev records6180_6181 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6180]
theorem aligned6180_6181 :
    AlignedValid 12 3 missing6180_6181 records6180_6181 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6180
    maskCheck6180 AlignedValid.nil

def missing6181_6182 : List (BitVec (edgeCount 12)) :=
  [missing6181]
abbrev records6181_6182 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6181]
theorem aligned6181_6182 :
    AlignedValid 12 3 missing6181_6182 records6181_6182 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6181
    maskCheck6181 AlignedValid.nil

def missing6180_6182 : List (BitVec (edgeCount 12)) :=
  missing6180_6181 ++ missing6181_6182
abbrev records6180_6182 : List Blob :=
  records6180_6181 ++ records6181_6182
theorem aligned6180_6182 :
    AlignedValid 12 3 missing6180_6182 records6180_6182 :=
  aligned6180_6181.append aligned6181_6182

def missing6182_6183 : List (BitVec (edgeCount 12)) :=
  [missing6182]
abbrev records6182_6183 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6182]
theorem aligned6182_6183 :
    AlignedValid 12 3 missing6182_6183 records6182_6183 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6182
    maskCheck6182 AlignedValid.nil

def missing6183_6184 : List (BitVec (edgeCount 12)) :=
  [missing6183]
abbrev records6183_6184 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6183]
theorem aligned6183_6184 :
    AlignedValid 12 3 missing6183_6184 records6183_6184 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6183
    maskCheck6183 AlignedValid.nil

def missing6182_6184 : List (BitVec (edgeCount 12)) :=
  missing6182_6183 ++ missing6183_6184
abbrev records6182_6184 : List Blob :=
  records6182_6183 ++ records6183_6184
theorem aligned6182_6184 :
    AlignedValid 12 3 missing6182_6184 records6182_6184 :=
  aligned6182_6183.append aligned6183_6184

def missing6180_6184 : List (BitVec (edgeCount 12)) :=
  missing6180_6182 ++ missing6182_6184
abbrev records6180_6184 : List Blob :=
  records6180_6182 ++ records6182_6184
theorem aligned6180_6184 :
    AlignedValid 12 3 missing6180_6184 records6180_6184 :=
  aligned6180_6182.append aligned6182_6184

def missing6176_6184 : List (BitVec (edgeCount 12)) :=
  missing6176_6180 ++ missing6180_6184
abbrev records6176_6184 : List Blob :=
  records6176_6180 ++ records6180_6184
theorem aligned6176_6184 :
    AlignedValid 12 3 missing6176_6184 records6176_6184 :=
  aligned6176_6180.append aligned6180_6184

def missing6184_6185 : List (BitVec (edgeCount 12)) :=
  [missing6184]
abbrev records6184_6185 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6184]
theorem aligned6184_6185 :
    AlignedValid 12 3 missing6184_6185 records6184_6185 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6184
    maskCheck6184 AlignedValid.nil

def missing6185_6186 : List (BitVec (edgeCount 12)) :=
  [missing6185]
abbrev records6185_6186 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6185]
theorem aligned6185_6186 :
    AlignedValid 12 3 missing6185_6186 records6185_6186 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6185
    maskCheck6185 AlignedValid.nil

def missing6184_6186 : List (BitVec (edgeCount 12)) :=
  missing6184_6185 ++ missing6185_6186
abbrev records6184_6186 : List Blob :=
  records6184_6185 ++ records6185_6186
theorem aligned6184_6186 :
    AlignedValid 12 3 missing6184_6186 records6184_6186 :=
  aligned6184_6185.append aligned6185_6186

def missing6186_6187 : List (BitVec (edgeCount 12)) :=
  [missing6186]
abbrev records6186_6187 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6186]
theorem aligned6186_6187 :
    AlignedValid 12 3 missing6186_6187 records6186_6187 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6186
    maskCheck6186 AlignedValid.nil

def missing6187_6188 : List (BitVec (edgeCount 12)) :=
  [missing6187]
abbrev records6187_6188 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6187]
theorem aligned6187_6188 :
    AlignedValid 12 3 missing6187_6188 records6187_6188 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6187
    maskCheck6187 AlignedValid.nil

def missing6186_6188 : List (BitVec (edgeCount 12)) :=
  missing6186_6187 ++ missing6187_6188
abbrev records6186_6188 : List Blob :=
  records6186_6187 ++ records6187_6188
theorem aligned6186_6188 :
    AlignedValid 12 3 missing6186_6188 records6186_6188 :=
  aligned6186_6187.append aligned6187_6188

def missing6184_6188 : List (BitVec (edgeCount 12)) :=
  missing6184_6186 ++ missing6186_6188
abbrev records6184_6188 : List Blob :=
  records6184_6186 ++ records6186_6188
theorem aligned6184_6188 :
    AlignedValid 12 3 missing6184_6188 records6184_6188 :=
  aligned6184_6186.append aligned6186_6188

def missing6188_6189 : List (BitVec (edgeCount 12)) :=
  [missing6188]
abbrev records6188_6189 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6188]
theorem aligned6188_6189 :
    AlignedValid 12 3 missing6188_6189 records6188_6189 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6188
    maskCheck6188 AlignedValid.nil

def missing6189_6190 : List (BitVec (edgeCount 12)) :=
  [missing6189]
abbrev records6189_6190 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6189]
theorem aligned6189_6190 :
    AlignedValid 12 3 missing6189_6190 records6189_6190 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6189
    maskCheck6189 AlignedValid.nil

def missing6188_6190 : List (BitVec (edgeCount 12)) :=
  missing6188_6189 ++ missing6189_6190
abbrev records6188_6190 : List Blob :=
  records6188_6189 ++ records6189_6190
theorem aligned6188_6190 :
    AlignedValid 12 3 missing6188_6190 records6188_6190 :=
  aligned6188_6189.append aligned6189_6190

def missing6190_6191 : List (BitVec (edgeCount 12)) :=
  [missing6190]
abbrev records6190_6191 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6190]
theorem aligned6190_6191 :
    AlignedValid 12 3 missing6190_6191 records6190_6191 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6190
    maskCheck6190 AlignedValid.nil

def missing6191_6192 : List (BitVec (edgeCount 12)) :=
  [missing6191]
abbrev records6191_6192 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6191]
theorem aligned6191_6192 :
    AlignedValid 12 3 missing6191_6192 records6191_6192 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6191
    maskCheck6191 AlignedValid.nil

def missing6190_6192 : List (BitVec (edgeCount 12)) :=
  missing6190_6191 ++ missing6191_6192
abbrev records6190_6192 : List Blob :=
  records6190_6191 ++ records6191_6192
theorem aligned6190_6192 :
    AlignedValid 12 3 missing6190_6192 records6190_6192 :=
  aligned6190_6191.append aligned6191_6192

def missing6188_6192 : List (BitVec (edgeCount 12)) :=
  missing6188_6190 ++ missing6190_6192
abbrev records6188_6192 : List Blob :=
  records6188_6190 ++ records6190_6192
theorem aligned6188_6192 :
    AlignedValid 12 3 missing6188_6192 records6188_6192 :=
  aligned6188_6190.append aligned6190_6192

def missing6184_6192 : List (BitVec (edgeCount 12)) :=
  missing6184_6188 ++ missing6188_6192
abbrev records6184_6192 : List Blob :=
  records6184_6188 ++ records6188_6192
theorem aligned6184_6192 :
    AlignedValid 12 3 missing6184_6192 records6184_6192 :=
  aligned6184_6188.append aligned6188_6192

def missing6176_6192 : List (BitVec (edgeCount 12)) :=
  missing6176_6184 ++ missing6184_6192
abbrev records6176_6192 : List Blob :=
  records6176_6184 ++ records6184_6192
theorem aligned6176_6192 :
    AlignedValid 12 3 missing6176_6192 records6176_6192 :=
  aligned6176_6184.append aligned6184_6192

def missing6192_6193 : List (BitVec (edgeCount 12)) :=
  [missing6192]
abbrev records6192_6193 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6192]
theorem aligned6192_6193 :
    AlignedValid 12 3 missing6192_6193 records6192_6193 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6192
    maskCheck6192 AlignedValid.nil

def missing6193_6194 : List (BitVec (edgeCount 12)) :=
  [missing6193]
abbrev records6193_6194 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6193]
theorem aligned6193_6194 :
    AlignedValid 12 3 missing6193_6194 records6193_6194 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6193
    maskCheck6193 AlignedValid.nil

def missing6192_6194 : List (BitVec (edgeCount 12)) :=
  missing6192_6193 ++ missing6193_6194
abbrev records6192_6194 : List Blob :=
  records6192_6193 ++ records6193_6194
theorem aligned6192_6194 :
    AlignedValid 12 3 missing6192_6194 records6192_6194 :=
  aligned6192_6193.append aligned6193_6194

def missing6194_6195 : List (BitVec (edgeCount 12)) :=
  [missing6194]
abbrev records6194_6195 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6194]
theorem aligned6194_6195 :
    AlignedValid 12 3 missing6194_6195 records6194_6195 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6194
    maskCheck6194 AlignedValid.nil

def missing6195_6196 : List (BitVec (edgeCount 12)) :=
  [missing6195]
abbrev records6195_6196 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6195]
theorem aligned6195_6196 :
    AlignedValid 12 3 missing6195_6196 records6195_6196 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6195
    maskCheck6195 AlignedValid.nil

def missing6194_6196 : List (BitVec (edgeCount 12)) :=
  missing6194_6195 ++ missing6195_6196
abbrev records6194_6196 : List Blob :=
  records6194_6195 ++ records6195_6196
theorem aligned6194_6196 :
    AlignedValid 12 3 missing6194_6196 records6194_6196 :=
  aligned6194_6195.append aligned6195_6196

def missing6192_6196 : List (BitVec (edgeCount 12)) :=
  missing6192_6194 ++ missing6194_6196
abbrev records6192_6196 : List Blob :=
  records6192_6194 ++ records6194_6196
theorem aligned6192_6196 :
    AlignedValid 12 3 missing6192_6196 records6192_6196 :=
  aligned6192_6194.append aligned6194_6196

def missing6196_6197 : List (BitVec (edgeCount 12)) :=
  [missing6196]
abbrev records6196_6197 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6196]
theorem aligned6196_6197 :
    AlignedValid 12 3 missing6196_6197 records6196_6197 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6196
    maskCheck6196 AlignedValid.nil

def missing6197_6198 : List (BitVec (edgeCount 12)) :=
  [missing6197]
abbrev records6197_6198 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6197]
theorem aligned6197_6198 :
    AlignedValid 12 3 missing6197_6198 records6197_6198 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6197
    maskCheck6197 AlignedValid.nil

def missing6196_6198 : List (BitVec (edgeCount 12)) :=
  missing6196_6197 ++ missing6197_6198
abbrev records6196_6198 : List Blob :=
  records6196_6197 ++ records6197_6198
theorem aligned6196_6198 :
    AlignedValid 12 3 missing6196_6198 records6196_6198 :=
  aligned6196_6197.append aligned6197_6198

def missing6198_6199 : List (BitVec (edgeCount 12)) :=
  [missing6198]
abbrev records6198_6199 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6198]
theorem aligned6198_6199 :
    AlignedValid 12 3 missing6198_6199 records6198_6199 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6198
    maskCheck6198 AlignedValid.nil

def missing6199_6200 : List (BitVec (edgeCount 12)) :=
  [missing6199]
abbrev records6199_6200 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6199]
theorem aligned6199_6200 :
    AlignedValid 12 3 missing6199_6200 records6199_6200 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6199
    maskCheck6199 AlignedValid.nil

def missing6198_6200 : List (BitVec (edgeCount 12)) :=
  missing6198_6199 ++ missing6199_6200
abbrev records6198_6200 : List Blob :=
  records6198_6199 ++ records6199_6200
theorem aligned6198_6200 :
    AlignedValid 12 3 missing6198_6200 records6198_6200 :=
  aligned6198_6199.append aligned6199_6200

def missing6196_6200 : List (BitVec (edgeCount 12)) :=
  missing6196_6198 ++ missing6198_6200
abbrev records6196_6200 : List Blob :=
  records6196_6198 ++ records6198_6200
theorem aligned6196_6200 :
    AlignedValid 12 3 missing6196_6200 records6196_6200 :=
  aligned6196_6198.append aligned6198_6200

def missing6192_6200 : List (BitVec (edgeCount 12)) :=
  missing6192_6196 ++ missing6196_6200
abbrev records6192_6200 : List Blob :=
  records6192_6196 ++ records6196_6200
theorem aligned6192_6200 :
    AlignedValid 12 3 missing6192_6200 records6192_6200 :=
  aligned6192_6196.append aligned6196_6200

def missing6200_6201 : List (BitVec (edgeCount 12)) :=
  [missing6200]
abbrev records6200_6201 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6200]
theorem aligned6200_6201 :
    AlignedValid 12 3 missing6200_6201 records6200_6201 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6200
    maskCheck6200 AlignedValid.nil

def missing6201_6202 : List (BitVec (edgeCount 12)) :=
  [missing6201]
abbrev records6201_6202 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6201]
theorem aligned6201_6202 :
    AlignedValid 12 3 missing6201_6202 records6201_6202 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6201
    maskCheck6201 AlignedValid.nil

def missing6200_6202 : List (BitVec (edgeCount 12)) :=
  missing6200_6201 ++ missing6201_6202
abbrev records6200_6202 : List Blob :=
  records6200_6201 ++ records6201_6202
theorem aligned6200_6202 :
    AlignedValid 12 3 missing6200_6202 records6200_6202 :=
  aligned6200_6201.append aligned6201_6202

def missing6202_6203 : List (BitVec (edgeCount 12)) :=
  [missing6202]
abbrev records6202_6203 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6202]
theorem aligned6202_6203 :
    AlignedValid 12 3 missing6202_6203 records6202_6203 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6202
    maskCheck6202 AlignedValid.nil

def missing6203_6204 : List (BitVec (edgeCount 12)) :=
  [missing6203]
abbrev records6203_6204 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6203]
theorem aligned6203_6204 :
    AlignedValid 12 3 missing6203_6204 records6203_6204 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6203
    maskCheck6203 AlignedValid.nil

def missing6202_6204 : List (BitVec (edgeCount 12)) :=
  missing6202_6203 ++ missing6203_6204
abbrev records6202_6204 : List Blob :=
  records6202_6203 ++ records6203_6204
theorem aligned6202_6204 :
    AlignedValid 12 3 missing6202_6204 records6202_6204 :=
  aligned6202_6203.append aligned6203_6204

def missing6200_6204 : List (BitVec (edgeCount 12)) :=
  missing6200_6202 ++ missing6202_6204
abbrev records6200_6204 : List Blob :=
  records6200_6202 ++ records6202_6204
theorem aligned6200_6204 :
    AlignedValid 12 3 missing6200_6204 records6200_6204 :=
  aligned6200_6202.append aligned6202_6204

def missing6204_6205 : List (BitVec (edgeCount 12)) :=
  [missing6204]
abbrev records6204_6205 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6204]
theorem aligned6204_6205 :
    AlignedValid 12 3 missing6204_6205 records6204_6205 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6204
    maskCheck6204 AlignedValid.nil

def missing6205_6206 : List (BitVec (edgeCount 12)) :=
  [missing6205]
abbrev records6205_6206 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6205]
theorem aligned6205_6206 :
    AlignedValid 12 3 missing6205_6206 records6205_6206 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6205
    maskCheck6205 AlignedValid.nil

def missing6204_6206 : List (BitVec (edgeCount 12)) :=
  missing6204_6205 ++ missing6205_6206
abbrev records6204_6206 : List Blob :=
  records6204_6205 ++ records6205_6206
theorem aligned6204_6206 :
    AlignedValid 12 3 missing6204_6206 records6204_6206 :=
  aligned6204_6205.append aligned6205_6206

def missing6206_6207 : List (BitVec (edgeCount 12)) :=
  [missing6206]
abbrev records6206_6207 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6206]
theorem aligned6206_6207 :
    AlignedValid 12 3 missing6206_6207 records6206_6207 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6206
    maskCheck6206 AlignedValid.nil

def missing6207_6208 : List (BitVec (edgeCount 12)) :=
  [missing6207]
abbrev records6207_6208 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6207]
theorem aligned6207_6208 :
    AlignedValid 12 3 missing6207_6208 records6207_6208 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6207
    maskCheck6207 AlignedValid.nil

def missing6206_6208 : List (BitVec (edgeCount 12)) :=
  missing6206_6207 ++ missing6207_6208
abbrev records6206_6208 : List Blob :=
  records6206_6207 ++ records6207_6208
theorem aligned6206_6208 :
    AlignedValid 12 3 missing6206_6208 records6206_6208 :=
  aligned6206_6207.append aligned6207_6208

def missing6204_6208 : List (BitVec (edgeCount 12)) :=
  missing6204_6206 ++ missing6206_6208
abbrev records6204_6208 : List Blob :=
  records6204_6206 ++ records6206_6208
theorem aligned6204_6208 :
    AlignedValid 12 3 missing6204_6208 records6204_6208 :=
  aligned6204_6206.append aligned6206_6208

def missing6200_6208 : List (BitVec (edgeCount 12)) :=
  missing6200_6204 ++ missing6204_6208
abbrev records6200_6208 : List Blob :=
  records6200_6204 ++ records6204_6208
theorem aligned6200_6208 :
    AlignedValid 12 3 missing6200_6208 records6200_6208 :=
  aligned6200_6204.append aligned6204_6208

def missing6192_6208 : List (BitVec (edgeCount 12)) :=
  missing6192_6200 ++ missing6200_6208
abbrev records6192_6208 : List Blob :=
  records6192_6200 ++ records6200_6208
theorem aligned6192_6208 :
    AlignedValid 12 3 missing6192_6208 records6192_6208 :=
  aligned6192_6200.append aligned6200_6208

def missing6176_6208 : List (BitVec (edgeCount 12)) :=
  missing6176_6192 ++ missing6192_6208
abbrev records6176_6208 : List Blob :=
  records6176_6192 ++ records6192_6208
theorem aligned6176_6208 :
    AlignedValid 12 3 missing6176_6208 records6176_6208 :=
  aligned6176_6192.append aligned6192_6208

def missing6144_6208 : List (BitVec (edgeCount 12)) :=
  missing6144_6176 ++ missing6176_6208
abbrev records6144_6208 : List Blob :=
  records6144_6176 ++ records6176_6208
theorem aligned6144_6208 :
    AlignedValid 12 3 missing6144_6208 records6144_6208 :=
  aligned6144_6176.append aligned6176_6208

def missing6208_6209 : List (BitVec (edgeCount 12)) :=
  [missing6208]
abbrev records6208_6209 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6208]
theorem aligned6208_6209 :
    AlignedValid 12 3 missing6208_6209 records6208_6209 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6208
    maskCheck6208 AlignedValid.nil

def missing6209_6210 : List (BitVec (edgeCount 12)) :=
  [missing6209]
abbrev records6209_6210 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6209]
theorem aligned6209_6210 :
    AlignedValid 12 3 missing6209_6210 records6209_6210 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6209
    maskCheck6209 AlignedValid.nil

def missing6208_6210 : List (BitVec (edgeCount 12)) :=
  missing6208_6209 ++ missing6209_6210
abbrev records6208_6210 : List Blob :=
  records6208_6209 ++ records6209_6210
theorem aligned6208_6210 :
    AlignedValid 12 3 missing6208_6210 records6208_6210 :=
  aligned6208_6209.append aligned6209_6210

def missing6210_6211 : List (BitVec (edgeCount 12)) :=
  [missing6210]
abbrev records6210_6211 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6210]
theorem aligned6210_6211 :
    AlignedValid 12 3 missing6210_6211 records6210_6211 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6210
    maskCheck6210 AlignedValid.nil

def missing6211_6212 : List (BitVec (edgeCount 12)) :=
  [missing6211]
abbrev records6211_6212 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6211]
theorem aligned6211_6212 :
    AlignedValid 12 3 missing6211_6212 records6211_6212 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6211
    maskCheck6211 AlignedValid.nil

def missing6210_6212 : List (BitVec (edgeCount 12)) :=
  missing6210_6211 ++ missing6211_6212
abbrev records6210_6212 : List Blob :=
  records6210_6211 ++ records6211_6212
theorem aligned6210_6212 :
    AlignedValid 12 3 missing6210_6212 records6210_6212 :=
  aligned6210_6211.append aligned6211_6212

def missing6208_6212 : List (BitVec (edgeCount 12)) :=
  missing6208_6210 ++ missing6210_6212
abbrev records6208_6212 : List Blob :=
  records6208_6210 ++ records6210_6212
theorem aligned6208_6212 :
    AlignedValid 12 3 missing6208_6212 records6208_6212 :=
  aligned6208_6210.append aligned6210_6212

def missing6212_6213 : List (BitVec (edgeCount 12)) :=
  [missing6212]
abbrev records6212_6213 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6212]
theorem aligned6212_6213 :
    AlignedValid 12 3 missing6212_6213 records6212_6213 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6212
    maskCheck6212 AlignedValid.nil

def missing6213_6214 : List (BitVec (edgeCount 12)) :=
  [missing6213]
abbrev records6213_6214 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6213]
theorem aligned6213_6214 :
    AlignedValid 12 3 missing6213_6214 records6213_6214 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6213
    maskCheck6213 AlignedValid.nil

def missing6212_6214 : List (BitVec (edgeCount 12)) :=
  missing6212_6213 ++ missing6213_6214
abbrev records6212_6214 : List Blob :=
  records6212_6213 ++ records6213_6214
theorem aligned6212_6214 :
    AlignedValid 12 3 missing6212_6214 records6212_6214 :=
  aligned6212_6213.append aligned6213_6214

def missing6214_6215 : List (BitVec (edgeCount 12)) :=
  [missing6214]
abbrev records6214_6215 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6214]
theorem aligned6214_6215 :
    AlignedValid 12 3 missing6214_6215 records6214_6215 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6214
    maskCheck6214 AlignedValid.nil

def missing6215_6216 : List (BitVec (edgeCount 12)) :=
  [missing6215]
abbrev records6215_6216 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6215]
theorem aligned6215_6216 :
    AlignedValid 12 3 missing6215_6216 records6215_6216 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6215
    maskCheck6215 AlignedValid.nil

def missing6214_6216 : List (BitVec (edgeCount 12)) :=
  missing6214_6215 ++ missing6215_6216
abbrev records6214_6216 : List Blob :=
  records6214_6215 ++ records6215_6216
theorem aligned6214_6216 :
    AlignedValid 12 3 missing6214_6216 records6214_6216 :=
  aligned6214_6215.append aligned6215_6216

def missing6212_6216 : List (BitVec (edgeCount 12)) :=
  missing6212_6214 ++ missing6214_6216
abbrev records6212_6216 : List Blob :=
  records6212_6214 ++ records6214_6216
theorem aligned6212_6216 :
    AlignedValid 12 3 missing6212_6216 records6212_6216 :=
  aligned6212_6214.append aligned6214_6216

def missing6208_6216 : List (BitVec (edgeCount 12)) :=
  missing6208_6212 ++ missing6212_6216
abbrev records6208_6216 : List Blob :=
  records6208_6212 ++ records6212_6216
theorem aligned6208_6216 :
    AlignedValid 12 3 missing6208_6216 records6208_6216 :=
  aligned6208_6212.append aligned6212_6216

def missing6216_6217 : List (BitVec (edgeCount 12)) :=
  [missing6216]
abbrev records6216_6217 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6216]
theorem aligned6216_6217 :
    AlignedValid 12 3 missing6216_6217 records6216_6217 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6216
    maskCheck6216 AlignedValid.nil

def missing6217_6218 : List (BitVec (edgeCount 12)) :=
  [missing6217]
abbrev records6217_6218 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6217]
theorem aligned6217_6218 :
    AlignedValid 12 3 missing6217_6218 records6217_6218 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6217
    maskCheck6217 AlignedValid.nil

def missing6216_6218 : List (BitVec (edgeCount 12)) :=
  missing6216_6217 ++ missing6217_6218
abbrev records6216_6218 : List Blob :=
  records6216_6217 ++ records6217_6218
theorem aligned6216_6218 :
    AlignedValid 12 3 missing6216_6218 records6216_6218 :=
  aligned6216_6217.append aligned6217_6218

def missing6218_6219 : List (BitVec (edgeCount 12)) :=
  [missing6218]
abbrev records6218_6219 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6218]
theorem aligned6218_6219 :
    AlignedValid 12 3 missing6218_6219 records6218_6219 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6218
    maskCheck6218 AlignedValid.nil

def missing6219_6220 : List (BitVec (edgeCount 12)) :=
  [missing6219]
abbrev records6219_6220 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6219]
theorem aligned6219_6220 :
    AlignedValid 12 3 missing6219_6220 records6219_6220 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6219
    maskCheck6219 AlignedValid.nil

def missing6218_6220 : List (BitVec (edgeCount 12)) :=
  missing6218_6219 ++ missing6219_6220
abbrev records6218_6220 : List Blob :=
  records6218_6219 ++ records6219_6220
theorem aligned6218_6220 :
    AlignedValid 12 3 missing6218_6220 records6218_6220 :=
  aligned6218_6219.append aligned6219_6220

def missing6216_6220 : List (BitVec (edgeCount 12)) :=
  missing6216_6218 ++ missing6218_6220
abbrev records6216_6220 : List Blob :=
  records6216_6218 ++ records6218_6220
theorem aligned6216_6220 :
    AlignedValid 12 3 missing6216_6220 records6216_6220 :=
  aligned6216_6218.append aligned6218_6220

def missing6220_6221 : List (BitVec (edgeCount 12)) :=
  [missing6220]
abbrev records6220_6221 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6220]
theorem aligned6220_6221 :
    AlignedValid 12 3 missing6220_6221 records6220_6221 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6220
    maskCheck6220 AlignedValid.nil

def missing6221_6222 : List (BitVec (edgeCount 12)) :=
  [missing6221]
abbrev records6221_6222 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6221]
theorem aligned6221_6222 :
    AlignedValid 12 3 missing6221_6222 records6221_6222 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6221
    maskCheck6221 AlignedValid.nil

def missing6220_6222 : List (BitVec (edgeCount 12)) :=
  missing6220_6221 ++ missing6221_6222
abbrev records6220_6222 : List Blob :=
  records6220_6221 ++ records6221_6222
theorem aligned6220_6222 :
    AlignedValid 12 3 missing6220_6222 records6220_6222 :=
  aligned6220_6221.append aligned6221_6222

def missing6222_6223 : List (BitVec (edgeCount 12)) :=
  [missing6222]
abbrev records6222_6223 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6222]
theorem aligned6222_6223 :
    AlignedValid 12 3 missing6222_6223 records6222_6223 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6222
    maskCheck6222 AlignedValid.nil

def missing6223_6224 : List (BitVec (edgeCount 12)) :=
  [missing6223]
abbrev records6223_6224 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6223]
theorem aligned6223_6224 :
    AlignedValid 12 3 missing6223_6224 records6223_6224 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6223
    maskCheck6223 AlignedValid.nil

def missing6222_6224 : List (BitVec (edgeCount 12)) :=
  missing6222_6223 ++ missing6223_6224
abbrev records6222_6224 : List Blob :=
  records6222_6223 ++ records6223_6224
theorem aligned6222_6224 :
    AlignedValid 12 3 missing6222_6224 records6222_6224 :=
  aligned6222_6223.append aligned6223_6224

def missing6220_6224 : List (BitVec (edgeCount 12)) :=
  missing6220_6222 ++ missing6222_6224
abbrev records6220_6224 : List Blob :=
  records6220_6222 ++ records6222_6224
theorem aligned6220_6224 :
    AlignedValid 12 3 missing6220_6224 records6220_6224 :=
  aligned6220_6222.append aligned6222_6224

def missing6216_6224 : List (BitVec (edgeCount 12)) :=
  missing6216_6220 ++ missing6220_6224
abbrev records6216_6224 : List Blob :=
  records6216_6220 ++ records6220_6224
theorem aligned6216_6224 :
    AlignedValid 12 3 missing6216_6224 records6216_6224 :=
  aligned6216_6220.append aligned6220_6224

def missing6208_6224 : List (BitVec (edgeCount 12)) :=
  missing6208_6216 ++ missing6216_6224
abbrev records6208_6224 : List Blob :=
  records6208_6216 ++ records6216_6224
theorem aligned6208_6224 :
    AlignedValid 12 3 missing6208_6224 records6208_6224 :=
  aligned6208_6216.append aligned6216_6224

def missing6224_6225 : List (BitVec (edgeCount 12)) :=
  [missing6224]
abbrev records6224_6225 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6224]
theorem aligned6224_6225 :
    AlignedValid 12 3 missing6224_6225 records6224_6225 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6224
    maskCheck6224 AlignedValid.nil

def missing6225_6226 : List (BitVec (edgeCount 12)) :=
  [missing6225]
abbrev records6225_6226 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6225]
theorem aligned6225_6226 :
    AlignedValid 12 3 missing6225_6226 records6225_6226 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6225
    maskCheck6225 AlignedValid.nil

def missing6224_6226 : List (BitVec (edgeCount 12)) :=
  missing6224_6225 ++ missing6225_6226
abbrev records6224_6226 : List Blob :=
  records6224_6225 ++ records6225_6226
theorem aligned6224_6226 :
    AlignedValid 12 3 missing6224_6226 records6224_6226 :=
  aligned6224_6225.append aligned6225_6226

def missing6226_6227 : List (BitVec (edgeCount 12)) :=
  [missing6226]
abbrev records6226_6227 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6226]
theorem aligned6226_6227 :
    AlignedValid 12 3 missing6226_6227 records6226_6227 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6226
    maskCheck6226 AlignedValid.nil

def missing6227_6228 : List (BitVec (edgeCount 12)) :=
  [missing6227]
abbrev records6227_6228 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6227]
theorem aligned6227_6228 :
    AlignedValid 12 3 missing6227_6228 records6227_6228 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6227
    maskCheck6227 AlignedValid.nil

def missing6226_6228 : List (BitVec (edgeCount 12)) :=
  missing6226_6227 ++ missing6227_6228
abbrev records6226_6228 : List Blob :=
  records6226_6227 ++ records6227_6228
theorem aligned6226_6228 :
    AlignedValid 12 3 missing6226_6228 records6226_6228 :=
  aligned6226_6227.append aligned6227_6228

def missing6224_6228 : List (BitVec (edgeCount 12)) :=
  missing6224_6226 ++ missing6226_6228
abbrev records6224_6228 : List Blob :=
  records6224_6226 ++ records6226_6228
theorem aligned6224_6228 :
    AlignedValid 12 3 missing6224_6228 records6224_6228 :=
  aligned6224_6226.append aligned6226_6228

def missing6228_6229 : List (BitVec (edgeCount 12)) :=
  [missing6228]
abbrev records6228_6229 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6228]
theorem aligned6228_6229 :
    AlignedValid 12 3 missing6228_6229 records6228_6229 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6228
    maskCheck6228 AlignedValid.nil

def missing6229_6230 : List (BitVec (edgeCount 12)) :=
  [missing6229]
abbrev records6229_6230 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6229]
theorem aligned6229_6230 :
    AlignedValid 12 3 missing6229_6230 records6229_6230 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6229
    maskCheck6229 AlignedValid.nil

def missing6228_6230 : List (BitVec (edgeCount 12)) :=
  missing6228_6229 ++ missing6229_6230
abbrev records6228_6230 : List Blob :=
  records6228_6229 ++ records6229_6230
theorem aligned6228_6230 :
    AlignedValid 12 3 missing6228_6230 records6228_6230 :=
  aligned6228_6229.append aligned6229_6230

def missing6230_6231 : List (BitVec (edgeCount 12)) :=
  [missing6230]
abbrev records6230_6231 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6230]
theorem aligned6230_6231 :
    AlignedValid 12 3 missing6230_6231 records6230_6231 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6230
    maskCheck6230 AlignedValid.nil

def missing6231_6232 : List (BitVec (edgeCount 12)) :=
  [missing6231]
abbrev records6231_6232 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6231]
theorem aligned6231_6232 :
    AlignedValid 12 3 missing6231_6232 records6231_6232 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6231
    maskCheck6231 AlignedValid.nil

def missing6230_6232 : List (BitVec (edgeCount 12)) :=
  missing6230_6231 ++ missing6231_6232
abbrev records6230_6232 : List Blob :=
  records6230_6231 ++ records6231_6232
theorem aligned6230_6232 :
    AlignedValid 12 3 missing6230_6232 records6230_6232 :=
  aligned6230_6231.append aligned6231_6232

def missing6228_6232 : List (BitVec (edgeCount 12)) :=
  missing6228_6230 ++ missing6230_6232
abbrev records6228_6232 : List Blob :=
  records6228_6230 ++ records6230_6232
theorem aligned6228_6232 :
    AlignedValid 12 3 missing6228_6232 records6228_6232 :=
  aligned6228_6230.append aligned6230_6232

def missing6224_6232 : List (BitVec (edgeCount 12)) :=
  missing6224_6228 ++ missing6228_6232
abbrev records6224_6232 : List Blob :=
  records6224_6228 ++ records6228_6232
theorem aligned6224_6232 :
    AlignedValid 12 3 missing6224_6232 records6224_6232 :=
  aligned6224_6228.append aligned6228_6232

def missing6232_6233 : List (BitVec (edgeCount 12)) :=
  [missing6232]
abbrev records6232_6233 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6232]
theorem aligned6232_6233 :
    AlignedValid 12 3 missing6232_6233 records6232_6233 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6232
    maskCheck6232 AlignedValid.nil

def missing6233_6234 : List (BitVec (edgeCount 12)) :=
  [missing6233]
abbrev records6233_6234 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6233]
theorem aligned6233_6234 :
    AlignedValid 12 3 missing6233_6234 records6233_6234 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6233
    maskCheck6233 AlignedValid.nil

def missing6232_6234 : List (BitVec (edgeCount 12)) :=
  missing6232_6233 ++ missing6233_6234
abbrev records6232_6234 : List Blob :=
  records6232_6233 ++ records6233_6234
theorem aligned6232_6234 :
    AlignedValid 12 3 missing6232_6234 records6232_6234 :=
  aligned6232_6233.append aligned6233_6234

def missing6234_6235 : List (BitVec (edgeCount 12)) :=
  [missing6234]
abbrev records6234_6235 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6234]
theorem aligned6234_6235 :
    AlignedValid 12 3 missing6234_6235 records6234_6235 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6234
    maskCheck6234 AlignedValid.nil

def missing6235_6236 : List (BitVec (edgeCount 12)) :=
  [missing6235]
abbrev records6235_6236 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6235]
theorem aligned6235_6236 :
    AlignedValid 12 3 missing6235_6236 records6235_6236 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6235
    maskCheck6235 AlignedValid.nil

def missing6234_6236 : List (BitVec (edgeCount 12)) :=
  missing6234_6235 ++ missing6235_6236
abbrev records6234_6236 : List Blob :=
  records6234_6235 ++ records6235_6236
theorem aligned6234_6236 :
    AlignedValid 12 3 missing6234_6236 records6234_6236 :=
  aligned6234_6235.append aligned6235_6236

def missing6232_6236 : List (BitVec (edgeCount 12)) :=
  missing6232_6234 ++ missing6234_6236
abbrev records6232_6236 : List Blob :=
  records6232_6234 ++ records6234_6236
theorem aligned6232_6236 :
    AlignedValid 12 3 missing6232_6236 records6232_6236 :=
  aligned6232_6234.append aligned6234_6236

def missing6236_6237 : List (BitVec (edgeCount 12)) :=
  [missing6236]
abbrev records6236_6237 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6236]
theorem aligned6236_6237 :
    AlignedValid 12 3 missing6236_6237 records6236_6237 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6236
    maskCheck6236 AlignedValid.nil

def missing6237_6238 : List (BitVec (edgeCount 12)) :=
  [missing6237]
abbrev records6237_6238 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6237]
theorem aligned6237_6238 :
    AlignedValid 12 3 missing6237_6238 records6237_6238 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6237
    maskCheck6237 AlignedValid.nil

def missing6236_6238 : List (BitVec (edgeCount 12)) :=
  missing6236_6237 ++ missing6237_6238
abbrev records6236_6238 : List Blob :=
  records6236_6237 ++ records6237_6238
theorem aligned6236_6238 :
    AlignedValid 12 3 missing6236_6238 records6236_6238 :=
  aligned6236_6237.append aligned6237_6238

def missing6238_6239 : List (BitVec (edgeCount 12)) :=
  [missing6238]
abbrev records6238_6239 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6238]
theorem aligned6238_6239 :
    AlignedValid 12 3 missing6238_6239 records6238_6239 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6238
    maskCheck6238 AlignedValid.nil

def missing6239_6240 : List (BitVec (edgeCount 12)) :=
  [missing6239]
abbrev records6239_6240 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6239]
theorem aligned6239_6240 :
    AlignedValid 12 3 missing6239_6240 records6239_6240 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6239
    maskCheck6239 AlignedValid.nil

def missing6238_6240 : List (BitVec (edgeCount 12)) :=
  missing6238_6239 ++ missing6239_6240
abbrev records6238_6240 : List Blob :=
  records6238_6239 ++ records6239_6240
theorem aligned6238_6240 :
    AlignedValid 12 3 missing6238_6240 records6238_6240 :=
  aligned6238_6239.append aligned6239_6240

def missing6236_6240 : List (BitVec (edgeCount 12)) :=
  missing6236_6238 ++ missing6238_6240
abbrev records6236_6240 : List Blob :=
  records6236_6238 ++ records6238_6240
theorem aligned6236_6240 :
    AlignedValid 12 3 missing6236_6240 records6236_6240 :=
  aligned6236_6238.append aligned6238_6240

def missing6232_6240 : List (BitVec (edgeCount 12)) :=
  missing6232_6236 ++ missing6236_6240
abbrev records6232_6240 : List Blob :=
  records6232_6236 ++ records6236_6240
theorem aligned6232_6240 :
    AlignedValid 12 3 missing6232_6240 records6232_6240 :=
  aligned6232_6236.append aligned6236_6240

def missing6224_6240 : List (BitVec (edgeCount 12)) :=
  missing6224_6232 ++ missing6232_6240
abbrev records6224_6240 : List Blob :=
  records6224_6232 ++ records6232_6240
theorem aligned6224_6240 :
    AlignedValid 12 3 missing6224_6240 records6224_6240 :=
  aligned6224_6232.append aligned6232_6240

def missing6208_6240 : List (BitVec (edgeCount 12)) :=
  missing6208_6224 ++ missing6224_6240
abbrev records6208_6240 : List Blob :=
  records6208_6224 ++ records6224_6240
theorem aligned6208_6240 :
    AlignedValid 12 3 missing6208_6240 records6208_6240 :=
  aligned6208_6224.append aligned6224_6240

def missing6240_6241 : List (BitVec (edgeCount 12)) :=
  [missing6240]
abbrev records6240_6241 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6240]
theorem aligned6240_6241 :
    AlignedValid 12 3 missing6240_6241 records6240_6241 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6240
    maskCheck6240 AlignedValid.nil

def missing6241_6242 : List (BitVec (edgeCount 12)) :=
  [missing6241]
abbrev records6241_6242 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6241]
theorem aligned6241_6242 :
    AlignedValid 12 3 missing6241_6242 records6241_6242 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6241
    maskCheck6241 AlignedValid.nil

def missing6240_6242 : List (BitVec (edgeCount 12)) :=
  missing6240_6241 ++ missing6241_6242
abbrev records6240_6242 : List Blob :=
  records6240_6241 ++ records6241_6242
theorem aligned6240_6242 :
    AlignedValid 12 3 missing6240_6242 records6240_6242 :=
  aligned6240_6241.append aligned6241_6242

def missing6242_6243 : List (BitVec (edgeCount 12)) :=
  [missing6242]
abbrev records6242_6243 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6242]
theorem aligned6242_6243 :
    AlignedValid 12 3 missing6242_6243 records6242_6243 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6242
    maskCheck6242 AlignedValid.nil

def missing6243_6244 : List (BitVec (edgeCount 12)) :=
  [missing6243]
abbrev records6243_6244 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6243]
theorem aligned6243_6244 :
    AlignedValid 12 3 missing6243_6244 records6243_6244 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6243
    maskCheck6243 AlignedValid.nil

def missing6242_6244 : List (BitVec (edgeCount 12)) :=
  missing6242_6243 ++ missing6243_6244
abbrev records6242_6244 : List Blob :=
  records6242_6243 ++ records6243_6244
theorem aligned6242_6244 :
    AlignedValid 12 3 missing6242_6244 records6242_6244 :=
  aligned6242_6243.append aligned6243_6244

def missing6240_6244 : List (BitVec (edgeCount 12)) :=
  missing6240_6242 ++ missing6242_6244
abbrev records6240_6244 : List Blob :=
  records6240_6242 ++ records6242_6244
theorem aligned6240_6244 :
    AlignedValid 12 3 missing6240_6244 records6240_6244 :=
  aligned6240_6242.append aligned6242_6244

def missing6244_6245 : List (BitVec (edgeCount 12)) :=
  [missing6244]
abbrev records6244_6245 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6244]
theorem aligned6244_6245 :
    AlignedValid 12 3 missing6244_6245 records6244_6245 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6244
    maskCheck6244 AlignedValid.nil

def missing6245_6246 : List (BitVec (edgeCount 12)) :=
  [missing6245]
abbrev records6245_6246 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6245]
theorem aligned6245_6246 :
    AlignedValid 12 3 missing6245_6246 records6245_6246 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6245
    maskCheck6245 AlignedValid.nil

def missing6244_6246 : List (BitVec (edgeCount 12)) :=
  missing6244_6245 ++ missing6245_6246
abbrev records6244_6246 : List Blob :=
  records6244_6245 ++ records6245_6246
theorem aligned6244_6246 :
    AlignedValid 12 3 missing6244_6246 records6244_6246 :=
  aligned6244_6245.append aligned6245_6246

def missing6246_6247 : List (BitVec (edgeCount 12)) :=
  [missing6246]
abbrev records6246_6247 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6246]
theorem aligned6246_6247 :
    AlignedValid 12 3 missing6246_6247 records6246_6247 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6246
    maskCheck6246 AlignedValid.nil

def missing6247_6248 : List (BitVec (edgeCount 12)) :=
  [missing6247]
abbrev records6247_6248 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6247]
theorem aligned6247_6248 :
    AlignedValid 12 3 missing6247_6248 records6247_6248 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6247
    maskCheck6247 AlignedValid.nil

def missing6246_6248 : List (BitVec (edgeCount 12)) :=
  missing6246_6247 ++ missing6247_6248
abbrev records6246_6248 : List Blob :=
  records6246_6247 ++ records6247_6248
theorem aligned6246_6248 :
    AlignedValid 12 3 missing6246_6248 records6246_6248 :=
  aligned6246_6247.append aligned6247_6248

def missing6244_6248 : List (BitVec (edgeCount 12)) :=
  missing6244_6246 ++ missing6246_6248
abbrev records6244_6248 : List Blob :=
  records6244_6246 ++ records6246_6248
theorem aligned6244_6248 :
    AlignedValid 12 3 missing6244_6248 records6244_6248 :=
  aligned6244_6246.append aligned6246_6248

def missing6240_6248 : List (BitVec (edgeCount 12)) :=
  missing6240_6244 ++ missing6244_6248
abbrev records6240_6248 : List Blob :=
  records6240_6244 ++ records6244_6248
theorem aligned6240_6248 :
    AlignedValid 12 3 missing6240_6248 records6240_6248 :=
  aligned6240_6244.append aligned6244_6248

def missing6248_6249 : List (BitVec (edgeCount 12)) :=
  [missing6248]
abbrev records6248_6249 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6248]
theorem aligned6248_6249 :
    AlignedValid 12 3 missing6248_6249 records6248_6249 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6248
    maskCheck6248 AlignedValid.nil

def missing6249_6250 : List (BitVec (edgeCount 12)) :=
  [missing6249]
abbrev records6249_6250 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6249]
theorem aligned6249_6250 :
    AlignedValid 12 3 missing6249_6250 records6249_6250 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6249
    maskCheck6249 AlignedValid.nil

def missing6248_6250 : List (BitVec (edgeCount 12)) :=
  missing6248_6249 ++ missing6249_6250
abbrev records6248_6250 : List Blob :=
  records6248_6249 ++ records6249_6250
theorem aligned6248_6250 :
    AlignedValid 12 3 missing6248_6250 records6248_6250 :=
  aligned6248_6249.append aligned6249_6250

def missing6250_6251 : List (BitVec (edgeCount 12)) :=
  [missing6250]
abbrev records6250_6251 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6250]
theorem aligned6250_6251 :
    AlignedValid 12 3 missing6250_6251 records6250_6251 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6250
    maskCheck6250 AlignedValid.nil

def missing6251_6252 : List (BitVec (edgeCount 12)) :=
  [missing6251]
abbrev records6251_6252 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6251]
theorem aligned6251_6252 :
    AlignedValid 12 3 missing6251_6252 records6251_6252 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6251
    maskCheck6251 AlignedValid.nil

def missing6250_6252 : List (BitVec (edgeCount 12)) :=
  missing6250_6251 ++ missing6251_6252
abbrev records6250_6252 : List Blob :=
  records6250_6251 ++ records6251_6252
theorem aligned6250_6252 :
    AlignedValid 12 3 missing6250_6252 records6250_6252 :=
  aligned6250_6251.append aligned6251_6252

def missing6248_6252 : List (BitVec (edgeCount 12)) :=
  missing6248_6250 ++ missing6250_6252
abbrev records6248_6252 : List Blob :=
  records6248_6250 ++ records6250_6252
theorem aligned6248_6252 :
    AlignedValid 12 3 missing6248_6252 records6248_6252 :=
  aligned6248_6250.append aligned6250_6252

def missing6252_6253 : List (BitVec (edgeCount 12)) :=
  [missing6252]
abbrev records6252_6253 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6252]
theorem aligned6252_6253 :
    AlignedValid 12 3 missing6252_6253 records6252_6253 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6252
    maskCheck6252 AlignedValid.nil

def missing6253_6254 : List (BitVec (edgeCount 12)) :=
  [missing6253]
abbrev records6253_6254 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6253]
theorem aligned6253_6254 :
    AlignedValid 12 3 missing6253_6254 records6253_6254 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6253
    maskCheck6253 AlignedValid.nil

def missing6252_6254 : List (BitVec (edgeCount 12)) :=
  missing6252_6253 ++ missing6253_6254
abbrev records6252_6254 : List Blob :=
  records6252_6253 ++ records6253_6254
theorem aligned6252_6254 :
    AlignedValid 12 3 missing6252_6254 records6252_6254 :=
  aligned6252_6253.append aligned6253_6254

def missing6254_6255 : List (BitVec (edgeCount 12)) :=
  [missing6254]
abbrev records6254_6255 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6254]
theorem aligned6254_6255 :
    AlignedValid 12 3 missing6254_6255 records6254_6255 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6254
    maskCheck6254 AlignedValid.nil

def missing6255_6256 : List (BitVec (edgeCount 12)) :=
  [missing6255]
abbrev records6255_6256 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6255]
theorem aligned6255_6256 :
    AlignedValid 12 3 missing6255_6256 records6255_6256 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6255
    maskCheck6255 AlignedValid.nil

def missing6254_6256 : List (BitVec (edgeCount 12)) :=
  missing6254_6255 ++ missing6255_6256
abbrev records6254_6256 : List Blob :=
  records6254_6255 ++ records6255_6256
theorem aligned6254_6256 :
    AlignedValid 12 3 missing6254_6256 records6254_6256 :=
  aligned6254_6255.append aligned6255_6256

def missing6252_6256 : List (BitVec (edgeCount 12)) :=
  missing6252_6254 ++ missing6254_6256
abbrev records6252_6256 : List Blob :=
  records6252_6254 ++ records6254_6256
theorem aligned6252_6256 :
    AlignedValid 12 3 missing6252_6256 records6252_6256 :=
  aligned6252_6254.append aligned6254_6256

def missing6248_6256 : List (BitVec (edgeCount 12)) :=
  missing6248_6252 ++ missing6252_6256
abbrev records6248_6256 : List Blob :=
  records6248_6252 ++ records6252_6256
theorem aligned6248_6256 :
    AlignedValid 12 3 missing6248_6256 records6248_6256 :=
  aligned6248_6252.append aligned6252_6256

def missing6240_6256 : List (BitVec (edgeCount 12)) :=
  missing6240_6248 ++ missing6248_6256
abbrev records6240_6256 : List Blob :=
  records6240_6248 ++ records6248_6256
theorem aligned6240_6256 :
    AlignedValid 12 3 missing6240_6256 records6240_6256 :=
  aligned6240_6248.append aligned6248_6256

def missing6256_6257 : List (BitVec (edgeCount 12)) :=
  [missing6256]
abbrev records6256_6257 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6256]
theorem aligned6256_6257 :
    AlignedValid 12 3 missing6256_6257 records6256_6257 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6256
    maskCheck6256 AlignedValid.nil

def missing6257_6258 : List (BitVec (edgeCount 12)) :=
  [missing6257]
abbrev records6257_6258 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6257]
theorem aligned6257_6258 :
    AlignedValid 12 3 missing6257_6258 records6257_6258 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6257
    maskCheck6257 AlignedValid.nil

def missing6256_6258 : List (BitVec (edgeCount 12)) :=
  missing6256_6257 ++ missing6257_6258
abbrev records6256_6258 : List Blob :=
  records6256_6257 ++ records6257_6258
theorem aligned6256_6258 :
    AlignedValid 12 3 missing6256_6258 records6256_6258 :=
  aligned6256_6257.append aligned6257_6258

def missing6258_6259 : List (BitVec (edgeCount 12)) :=
  [missing6258]
abbrev records6258_6259 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6258]
theorem aligned6258_6259 :
    AlignedValid 12 3 missing6258_6259 records6258_6259 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6258
    maskCheck6258 AlignedValid.nil

def missing6259_6260 : List (BitVec (edgeCount 12)) :=
  [missing6259]
abbrev records6259_6260 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6259]
theorem aligned6259_6260 :
    AlignedValid 12 3 missing6259_6260 records6259_6260 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6259
    maskCheck6259 AlignedValid.nil

def missing6258_6260 : List (BitVec (edgeCount 12)) :=
  missing6258_6259 ++ missing6259_6260
abbrev records6258_6260 : List Blob :=
  records6258_6259 ++ records6259_6260
theorem aligned6258_6260 :
    AlignedValid 12 3 missing6258_6260 records6258_6260 :=
  aligned6258_6259.append aligned6259_6260

def missing6256_6260 : List (BitVec (edgeCount 12)) :=
  missing6256_6258 ++ missing6258_6260
abbrev records6256_6260 : List Blob :=
  records6256_6258 ++ records6258_6260
theorem aligned6256_6260 :
    AlignedValid 12 3 missing6256_6260 records6256_6260 :=
  aligned6256_6258.append aligned6258_6260

def missing6260_6261 : List (BitVec (edgeCount 12)) :=
  [missing6260]
abbrev records6260_6261 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6260]
theorem aligned6260_6261 :
    AlignedValid 12 3 missing6260_6261 records6260_6261 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6260
    maskCheck6260 AlignedValid.nil

def missing6261_6262 : List (BitVec (edgeCount 12)) :=
  [missing6261]
abbrev records6261_6262 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6261]
theorem aligned6261_6262 :
    AlignedValid 12 3 missing6261_6262 records6261_6262 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6261
    maskCheck6261 AlignedValid.nil

def missing6260_6262 : List (BitVec (edgeCount 12)) :=
  missing6260_6261 ++ missing6261_6262
abbrev records6260_6262 : List Blob :=
  records6260_6261 ++ records6261_6262
theorem aligned6260_6262 :
    AlignedValid 12 3 missing6260_6262 records6260_6262 :=
  aligned6260_6261.append aligned6261_6262

def missing6262_6263 : List (BitVec (edgeCount 12)) :=
  [missing6262]
abbrev records6262_6263 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6262]
theorem aligned6262_6263 :
    AlignedValid 12 3 missing6262_6263 records6262_6263 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6262
    maskCheck6262 AlignedValid.nil

def missing6263_6264 : List (BitVec (edgeCount 12)) :=
  [missing6263]
abbrev records6263_6264 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6263]
theorem aligned6263_6264 :
    AlignedValid 12 3 missing6263_6264 records6263_6264 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6263
    maskCheck6263 AlignedValid.nil

def missing6262_6264 : List (BitVec (edgeCount 12)) :=
  missing6262_6263 ++ missing6263_6264
abbrev records6262_6264 : List Blob :=
  records6262_6263 ++ records6263_6264
theorem aligned6262_6264 :
    AlignedValid 12 3 missing6262_6264 records6262_6264 :=
  aligned6262_6263.append aligned6263_6264

def missing6260_6264 : List (BitVec (edgeCount 12)) :=
  missing6260_6262 ++ missing6262_6264
abbrev records6260_6264 : List Blob :=
  records6260_6262 ++ records6262_6264
theorem aligned6260_6264 :
    AlignedValid 12 3 missing6260_6264 records6260_6264 :=
  aligned6260_6262.append aligned6262_6264

def missing6256_6264 : List (BitVec (edgeCount 12)) :=
  missing6256_6260 ++ missing6260_6264
abbrev records6256_6264 : List Blob :=
  records6256_6260 ++ records6260_6264
theorem aligned6256_6264 :
    AlignedValid 12 3 missing6256_6264 records6256_6264 :=
  aligned6256_6260.append aligned6260_6264

def missing6264_6265 : List (BitVec (edgeCount 12)) :=
  [missing6264]
abbrev records6264_6265 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6264]
theorem aligned6264_6265 :
    AlignedValid 12 3 missing6264_6265 records6264_6265 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6264
    maskCheck6264 AlignedValid.nil

def missing6265_6266 : List (BitVec (edgeCount 12)) :=
  [missing6265]
abbrev records6265_6266 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6265]
theorem aligned6265_6266 :
    AlignedValid 12 3 missing6265_6266 records6265_6266 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6265
    maskCheck6265 AlignedValid.nil

def missing6264_6266 : List (BitVec (edgeCount 12)) :=
  missing6264_6265 ++ missing6265_6266
abbrev records6264_6266 : List Blob :=
  records6264_6265 ++ records6265_6266
theorem aligned6264_6266 :
    AlignedValid 12 3 missing6264_6266 records6264_6266 :=
  aligned6264_6265.append aligned6265_6266

def missing6266_6267 : List (BitVec (edgeCount 12)) :=
  [missing6266]
abbrev records6266_6267 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6266]
theorem aligned6266_6267 :
    AlignedValid 12 3 missing6266_6267 records6266_6267 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6266
    maskCheck6266 AlignedValid.nil

def missing6267_6268 : List (BitVec (edgeCount 12)) :=
  [missing6267]
abbrev records6267_6268 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6267]
theorem aligned6267_6268 :
    AlignedValid 12 3 missing6267_6268 records6267_6268 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6267
    maskCheck6267 AlignedValid.nil

def missing6266_6268 : List (BitVec (edgeCount 12)) :=
  missing6266_6267 ++ missing6267_6268
abbrev records6266_6268 : List Blob :=
  records6266_6267 ++ records6267_6268
theorem aligned6266_6268 :
    AlignedValid 12 3 missing6266_6268 records6266_6268 :=
  aligned6266_6267.append aligned6267_6268

def missing6264_6268 : List (BitVec (edgeCount 12)) :=
  missing6264_6266 ++ missing6266_6268
abbrev records6264_6268 : List Blob :=
  records6264_6266 ++ records6266_6268
theorem aligned6264_6268 :
    AlignedValid 12 3 missing6264_6268 records6264_6268 :=
  aligned6264_6266.append aligned6266_6268

def missing6268_6269 : List (BitVec (edgeCount 12)) :=
  [missing6268]
abbrev records6268_6269 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6268]
theorem aligned6268_6269 :
    AlignedValid 12 3 missing6268_6269 records6268_6269 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6268
    maskCheck6268 AlignedValid.nil

def missing6269_6270 : List (BitVec (edgeCount 12)) :=
  [missing6269]
abbrev records6269_6270 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6269]
theorem aligned6269_6270 :
    AlignedValid 12 3 missing6269_6270 records6269_6270 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6269
    maskCheck6269 AlignedValid.nil

def missing6268_6270 : List (BitVec (edgeCount 12)) :=
  missing6268_6269 ++ missing6269_6270
abbrev records6268_6270 : List Blob :=
  records6268_6269 ++ records6269_6270
theorem aligned6268_6270 :
    AlignedValid 12 3 missing6268_6270 records6268_6270 :=
  aligned6268_6269.append aligned6269_6270

def missing6270_6271 : List (BitVec (edgeCount 12)) :=
  [missing6270]
abbrev records6270_6271 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6270]
theorem aligned6270_6271 :
    AlignedValid 12 3 missing6270_6271 records6270_6271 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6270
    maskCheck6270 AlignedValid.nil

def missing6271_6272 : List (BitVec (edgeCount 12)) :=
  [missing6271]
abbrev records6271_6272 : List Blob :=
  [StrongPackedBucketN12A3Shard048.record6271]
theorem aligned6271_6272 :
    AlignedValid 12 3 missing6271_6272 records6271_6272 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard048.check6271
    maskCheck6271 AlignedValid.nil

def missing6270_6272 : List (BitVec (edgeCount 12)) :=
  missing6270_6271 ++ missing6271_6272
abbrev records6270_6272 : List Blob :=
  records6270_6271 ++ records6271_6272
theorem aligned6270_6272 :
    AlignedValid 12 3 missing6270_6272 records6270_6272 :=
  aligned6270_6271.append aligned6271_6272

def missing6268_6272 : List (BitVec (edgeCount 12)) :=
  missing6268_6270 ++ missing6270_6272
abbrev records6268_6272 : List Blob :=
  records6268_6270 ++ records6270_6272
theorem aligned6268_6272 :
    AlignedValid 12 3 missing6268_6272 records6268_6272 :=
  aligned6268_6270.append aligned6270_6272

def missing6264_6272 : List (BitVec (edgeCount 12)) :=
  missing6264_6268 ++ missing6268_6272
abbrev records6264_6272 : List Blob :=
  records6264_6268 ++ records6268_6272
theorem aligned6264_6272 :
    AlignedValid 12 3 missing6264_6272 records6264_6272 :=
  aligned6264_6268.append aligned6268_6272

def missing6256_6272 : List (BitVec (edgeCount 12)) :=
  missing6256_6264 ++ missing6264_6272
abbrev records6256_6272 : List Blob :=
  records6256_6264 ++ records6264_6272
theorem aligned6256_6272 :
    AlignedValid 12 3 missing6256_6272 records6256_6272 :=
  aligned6256_6264.append aligned6264_6272

def missing6240_6272 : List (BitVec (edgeCount 12)) :=
  missing6240_6256 ++ missing6256_6272
abbrev records6240_6272 : List Blob :=
  records6240_6256 ++ records6256_6272
theorem aligned6240_6272 :
    AlignedValid 12 3 missing6240_6272 records6240_6272 :=
  aligned6240_6256.append aligned6256_6272

def missing6208_6272 : List (BitVec (edgeCount 12)) :=
  missing6208_6240 ++ missing6240_6272
abbrev records6208_6272 : List Blob :=
  records6208_6240 ++ records6240_6272
theorem aligned6208_6272 :
    AlignedValid 12 3 missing6208_6272 records6208_6272 :=
  aligned6208_6240.append aligned6240_6272

def missing6144_6272 : List (BitVec (edgeCount 12)) :=
  missing6144_6208 ++ missing6208_6272
abbrev records6144_6272 : List Blob :=
  records6144_6208 ++ records6208_6272
theorem aligned6144_6272 :
    AlignedValid 12 3 missing6144_6272 records6144_6272 :=
  aligned6144_6208.append aligned6208_6272

abbrev missing : List (BitVec (edgeCount 12)) := missing6144_6272
abbrev records : List Blob := records6144_6272
theorem aligned : AlignedValid 12 3 missing records := aligned6144_6272

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard048
