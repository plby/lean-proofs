/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard236

/-! Decode-only alignment checks for n=12, a=4, records 30208--30335. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard236

open PackedBucketCertificate

def missing30208 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5479826865963139072
theorem maskCheck30208 :
    checkMaskFor missing30208 StrongPackedBucketN12A4Shard236.record30208 = true := by
  decide

def missing30209 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5912172430190706688
theorem maskCheck30209 :
    checkMaskFor missing30209 StrongPackedBucketN12A4Shard236.record30209 = true := by
  decide

def missing30210 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6056287618266562560
theorem maskCheck30210 :
    checkMaskFor missing30210 StrongPackedBucketN12A4Shard236.record30210 = true := by
  decide

def missing30211 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9334908146992283648
theorem maskCheck30211 :
    checkMaskFor missing30211 StrongPackedBucketN12A4Shard236.record30211 = true := by
  decide

def missing30212 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9659167320162959360
theorem maskCheck30212 :
    checkMaskFor missing30212 StrongPackedBucketN12A4Shard236.record30212 = true := by
  decide

def missing30213 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10091512884390526976
theorem maskCheck30213 :
    checkMaskFor missing30213 StrongPackedBucketN12A4Shard236.record30213 = true := by
  decide

def missing30214 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10667973636693950464
theorem maskCheck30214 :
    checkMaskFor missing30214 StrongPackedBucketN12A4Shard236.record30214 = true := by
  decide

def missing30215 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13874536571381743616
theorem maskCheck30215 :
    checkMaskFor missing30215 StrongPackedBucketN12A4Shard236.record30215 = true := by
  decide

def missing30216 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13982622962438635520
theorem maskCheck30216 :
    checkMaskFor missing30216 StrongPackedBucketN12A4Shard236.record30216 = true := by
  decide

def missing30217 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14126738150514491392
theorem maskCheck30217 :
    checkMaskFor missing30217 StrongPackedBucketN12A4Shard236.record30217 = true := by
  decide

def missing30218 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14991429278969626624
theorem maskCheck30218 :
    checkMaskFor missing30218 StrongPackedBucketN12A4Shard236.record30218 = true := by
  decide

def missing30219 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18558280183847059456
theorem maskCheck30219 :
    checkMaskFor missing30219 StrongPackedBucketN12A4Shard236.record30219 = true := by
  decide

def missing30220 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18630337777884987392
theorem maskCheck30220 :
    checkMaskFor missing30220 StrongPackedBucketN12A4Shard236.record30220 = true := by
  decide

def missing30221 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18666366574903951360
theorem maskCheck30221 :
    checkMaskFor missing30221 StrongPackedBucketN12A4Shard236.record30221 = true := by
  decide

def missing30222 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18774452965960843264
theorem maskCheck30222 :
    checkMaskFor missing30222 StrongPackedBucketN12A4Shard236.record30222 = true := by
  decide

def missing30223 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18882539357017735168
theorem maskCheck30223 :
    checkMaskFor missing30223 StrongPackedBucketN12A4Shard236.record30223 = true := by
  decide

def missing30224 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19314884921245302784
theorem maskCheck30224 :
    checkMaskFor missing30224 StrongPackedBucketN12A4Shard236.record30224 = true := by
  decide

def missing30225 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19639144094415978496
theorem maskCheck30225 :
    checkMaskFor missing30225 StrongPackedBucketN12A4Shard236.record30225 = true := by
  decide

def missing30226 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19747230485472870400
theorem maskCheck30226 :
    checkMaskFor missing30226 StrongPackedBucketN12A4Shard236.record30226 = true := by
  decide

def missing30227 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23097908608236519424
theorem maskCheck30227 :
    checkMaskFor missing30227 StrongPackedBucketN12A4Shard236.record30227 = true := by
  decide

def missing30228 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23133937405255483392
theorem maskCheck30228 :
    checkMaskFor missing30228 StrongPackedBucketN12A4Shard236.record30228 = true := by
  decide

def missing30229 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23205994999293411328
theorem maskCheck30229 :
    checkMaskFor missing30229 StrongPackedBucketN12A4Shard236.record30229 = true := by
  decide

def missing30230 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23350110187369267200
theorem maskCheck30230 :
    checkMaskFor missing30230 StrongPackedBucketN12A4Shard236.record30230 = true := by
  decide

def missing30231 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24214801315824402432
theorem maskCheck30231 :
    checkMaskFor missing30231 StrongPackedBucketN12A4Shard236.record30231 = true := by
  decide

def missing30232 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27709594626663907328
theorem maskCheck30232 :
    checkMaskFor missing30232 StrongPackedBucketN12A4Shard236.record30232 = true := by
  decide

def missing30233 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27745623423682871296
theorem maskCheck30233 :
    checkMaskFor missing30233 StrongPackedBucketN12A4Shard236.record30233 = true := by
  decide

def missing30234 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27817681017720799232
theorem maskCheck30234 :
    checkMaskFor missing30234 StrongPackedBucketN12A4Shard236.record30234 = true := by
  decide

def missing30235 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27961796205796655104
theorem maskCheck30235 :
    checkMaskFor missing30235 StrongPackedBucketN12A4Shard236.record30235 = true := by
  decide

def missing30236 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28826487334251790336
theorem maskCheck30236 :
    checkMaskFor missing30236 StrongPackedBucketN12A4Shard236.record30236 = true := by
  decide

def missing30237 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32285251848072331264
theorem maskCheck30237 :
    checkMaskFor missing30237 StrongPackedBucketN12A4Shard236.record30237 = true := by
  decide

def missing30238 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 255862404445896704
theorem maskCheck30238 :
    checkMaskFor missing30238 StrongPackedBucketN12A4Shard236.record30238 = true := by
  decide

def missing30239 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 399977592521752576
theorem maskCheck30239 :
    checkMaskFor missing30239 StrongPackedBucketN12A4Shard236.record30239 = true := by
  decide

def missing30240 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 796294359730356224
theorem maskCheck30240 :
    checkMaskFor missing30240 StrongPackedBucketN12A4Shard236.record30240 = true := by
  decide

def missing30241 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 904380750787248128
theorem maskCheck30241 :
    checkMaskFor missing30241 StrongPackedBucketN12A4Shard236.record30241 = true := by
  decide

def missing30242 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1372755112033779712
theorem maskCheck30242 :
    checkMaskFor missing30242 StrongPackedBucketN12A4Shard236.record30242 = true := by
  decide

def missing30243 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1805100676261347328
theorem maskCheck30243 :
    checkMaskFor missing30243 StrongPackedBucketN12A4Shard236.record30243 = true := by
  decide

def missing30244 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3534482933171617792
theorem maskCheck30244 :
    checkMaskFor missing30244 StrongPackedBucketN12A4Shard236.record30244 = true := by
  decide

def missing30245 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4038886091437113344
theorem maskCheck30245 :
    checkMaskFor missing30245 StrongPackedBucketN12A4Shard236.record30245 = true := by
  decide

def missing30246 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4795490828835356672
theorem maskCheck30246 :
    checkMaskFor missing30246 StrongPackedBucketN12A4Shard236.record30246 = true := by
  decide

def missing30247 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4831519625854320640
theorem maskCheck30247 :
    checkMaskFor missing30247 StrongPackedBucketN12A4Shard236.record30247 = true := by
  decide

def missing30248 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4939606016911212544
theorem maskCheck30248 :
    checkMaskFor missing30248 StrongPackedBucketN12A4Shard236.record30248 = true := by
  decide

def missing30249 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5335922784119816192
theorem maskCheck30249 :
    checkMaskFor missing30249 StrongPackedBucketN12A4Shard236.record30249 = true := by
  decide

def missing30250 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5480037972195672064
theorem maskCheck30250 :
    checkMaskFor missing30250 StrongPackedBucketN12A4Shard236.record30250 = true := by
  decide

def missing30251 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5912383536423239680
theorem maskCheck30251 :
    checkMaskFor missing30251 StrongPackedBucketN12A4Shard236.record30251 = true := by
  decide

def missing30252 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6344729100650807296
theorem maskCheck30252 :
    checkMaskFor missing30252 StrongPackedBucketN12A4Shard236.record30252 = true := by
  decide

def missing30253 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13874747677614276608
theorem maskCheck30253 :
    checkMaskFor missing30253 StrongPackedBucketN12A4Shard236.record30253 = true := by
  decide

def missing30254 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13910776474633240576
theorem maskCheck30254 :
    checkMaskFor missing30254 StrongPackedBucketN12A4Shard236.record30254 = true := by
  decide

def missing30255 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14126949256747024384
theorem maskCheck30255 :
    checkMaskFor missing30255 StrongPackedBucketN12A4Shard236.record30255 = true := by
  decide

def missing30256 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14415179632898736128
theorem maskCheck30256 :
    checkMaskFor missing30256 StrongPackedBucketN12A4Shard236.record30256 = true := by
  decide

def missing30257 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14991640385202159616
theorem maskCheck30257 :
    checkMaskFor missing30257 StrongPackedBucketN12A4Shard236.record30257 = true := by
  decide

def missing30258 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18558491290079592448
theorem maskCheck30258 :
    checkMaskFor missing30258 StrongPackedBucketN12A4Shard236.record30258 = true := by
  decide

def missing30259 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18666577681136484352
theorem maskCheck30259 :
    checkMaskFor missing30259 StrongPackedBucketN12A4Shard236.record30259 = true := by
  decide

def missing30260 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18774664072193376256
theorem maskCheck30260 :
    checkMaskFor missing30260 StrongPackedBucketN12A4Shard236.record30260 = true := by
  decide

def missing30261 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19062894448345088000
theorem maskCheck30261 :
    checkMaskFor missing30261 StrongPackedBucketN12A4Shard236.record30261 = true := by
  decide

def missing30262 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19098923245364051968
theorem maskCheck30262 :
    checkMaskFor missing30262 StrongPackedBucketN12A4Shard236.record30262 = true := by
  decide

def missing30263 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19639355200648511488
theorem maskCheck30263 :
    checkMaskFor missing30263 StrongPackedBucketN12A4Shard236.record30263 = true := by
  decide

def missing30264 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19675383997667475456
theorem maskCheck30264 :
    checkMaskFor missing30264 StrongPackedBucketN12A4Shard236.record30264 = true := by
  decide

def missing30265 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20179787155932971008
theorem maskCheck30265 :
    checkMaskFor missing30265 StrongPackedBucketN12A4Shard236.record30265 = true := by
  decide

def missing30266 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21909169412843241472
theorem maskCheck30266 :
    checkMaskFor missing30266 StrongPackedBucketN12A4Shard236.record30266 = true := by
  decide

def missing30267 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23098119714469052416
theorem maskCheck30267 :
    checkMaskFor missing30267 StrongPackedBucketN12A4Shard236.record30267 = true := by
  decide

def missing30268 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23134148511488016384
theorem maskCheck30268 :
    checkMaskFor missing30268 StrongPackedBucketN12A4Shard236.record30268 = true := by
  decide

def missing30269 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23206206105525944320
theorem maskCheck30269 :
    checkMaskFor missing30269 StrongPackedBucketN12A4Shard236.record30269 = true := by
  decide

def missing30270 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23350321293601800192
theorem maskCheck30270 :
    checkMaskFor missing30270 StrongPackedBucketN12A4Shard236.record30270 = true := by
  decide

def missing30271 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23638551669753511936
theorem maskCheck30271 :
    checkMaskFor missing30271 StrongPackedBucketN12A4Shard236.record30271 = true := by
  decide

def missing30272 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24215012422056935424
theorem maskCheck30272 :
    checkMaskFor missing30272 StrongPackedBucketN12A4Shard236.record30272 = true := by
  decide

def missing30273 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32285462954304864256
theorem maskCheck30273 :
    checkMaskFor missing30273 StrongPackedBucketN12A4Shard236.record30273 = true := by
  decide

def missing30274 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 256917935608561664
theorem maskCheck30274 :
    checkMaskFor missing30274 StrongPackedBucketN12A4Shard236.record30274 = true := by
  decide

def missing30275 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 473090717722345472
theorem maskCheck30275 :
    checkMaskFor missing30275 StrongPackedBucketN12A4Shard236.record30275 = true := by
  decide

def missing30276 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9336174784387481600
theorem maskCheck30276 :
    checkMaskFor missing30276 StrongPackedBucketN12A4Shard236.record30276 = true := by
  decide

def missing30277 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10092779521785724928
theorem maskCheck30277 :
    checkMaskFor missing30277 StrongPackedBucketN12A4Shard236.record30277 = true := by
  decide

def missing30278 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10669240274089148416
theorem maskCheck30278 :
    checkMaskFor missing30278 StrongPackedBucketN12A4Shard236.record30278 = true := by
  decide

def missing30279 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18631604415280185344
theorem maskCheck30279 :
    checkMaskFor missing30279 StrongPackedBucketN12A4Shard236.record30279 = true := by
  decide

def missing30280 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27963062843191853056
theorem maskCheck30280 :
    checkMaskFor missing30280 StrongPackedBucketN12A4Shard236.record30280 = true := by
  decide

def missing30281 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28827753971646988288
theorem maskCheck30281 :
    checkMaskFor missing30281 StrongPackedBucketN12A4Shard236.record30281 = true := by
  decide

def missing30282 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 401173861172772864
theorem maskCheck30282 :
    checkMaskFor missing30282 StrongPackedBucketN12A4Shard236.record30282 = true := by
  decide

def missing30283 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9588517101008584704
theorem maskCheck30283 :
    checkMaskFor missing30283 StrongPackedBucketN12A4Shard236.record30283 = true := by
  decide

def missing30284 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9948805071198224384
theorem maskCheck30284 :
    checkMaskFor missing30284 StrongPackedBucketN12A4Shard236.record30284 = true := by
  decide

def missing30285 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10092920259274080256
theorem maskCheck30285 :
    checkMaskFor missing30285 StrongPackedBucketN12A4Shard236.record30285 = true := by
  decide

def missing30286 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27819088392604352512
theorem maskCheck30286 :
    checkMaskFor missing30286 StrongPackedBucketN12A4Shard236.record30286 = true := by
  decide

def missing30287 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28827894709135343616
theorem maskCheck30287 :
    checkMaskFor missing30287 StrongPackedBucketN12A4Shard236.record30287 = true := by
  decide

def missing30288 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 473301823954878464
theorem maskCheck30288 :
    checkMaskFor missing30288 StrongPackedBucketN12A4Shard236.record30288 = true := by
  decide

def missing30289 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 761532200106590208
theorem maskCheck30289 :
    checkMaskFor missing30289 StrongPackedBucketN12A4Shard236.record30289 = true := by
  decide

def missing30290 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 905647388182446080
theorem maskCheck30290 :
    checkMaskFor missing30290 StrongPackedBucketN12A4Shard236.record30290 = true := by
  decide

def missing30291 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9408443484657942528
theorem maskCheck30291 :
    checkMaskFor missing30291 StrongPackedBucketN12A4Shard236.record30291 = true := by
  decide

def missing30292 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9876817845904474112
theorem maskCheck30292 :
    checkMaskFor missing30292 StrongPackedBucketN12A4Shard236.record30292 = true := by
  decide

def missing30293 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10092990628018257920
theorem maskCheck30293 :
    checkMaskFor missing30293 StrongPackedBucketN12A4Shard236.record30293 = true := by
  decide

def missing30294 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18631815521512718336
theorem maskCheck30294 :
    checkMaskFor missing30294 StrongPackedBucketN12A4Shard236.record30294 = true := by
  decide

def missing30295 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18775930709588574208
theorem maskCheck30295 :
    checkMaskFor missing30295 StrongPackedBucketN12A4Shard236.record30295 = true := by
  decide

def missing30296 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27747101167310602240
theorem maskCheck30296 :
    checkMaskFor missing30296 StrongPackedBucketN12A4Shard236.record30296 = true := by
  decide

def missing30297 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28251504325576097792
theorem maskCheck30297 :
    checkMaskFor missing30297 StrongPackedBucketN12A4Shard236.record30297 = true := by
  decide

def missing30298 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28827965077879521280
theorem maskCheck30298 :
    checkMaskFor missing30298 StrongPackedBucketN12A4Shard236.record30298 = true := by
  decide

def missing30299 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 473724036419944448
theorem maskCheck30299 :
    checkMaskFor missing30299 StrongPackedBucketN12A4Shard236.record30299 = true := by
  decide

def missing30300 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10093412840483323904
theorem maskCheck30300 :
    checkMaskFor missing30300 StrongPackedBucketN12A4Shard236.record30300 = true := by
  decide

def missing30301 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18632237733977784320
theorem maskCheck30301 :
    checkMaskFor missing30301 StrongPackedBucketN12A4Shard236.record30301 = true := by
  decide

def missing30302 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18668266530996748288
theorem maskCheck30302 :
    checkMaskFor missing30302 StrongPackedBucketN12A4Shard236.record30302 = true := by
  decide

def missing30303 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19316784877338099712
theorem maskCheck30303 :
    checkMaskFor missing30303 StrongPackedBucketN12A4Shard236.record30303 = true := by
  decide

def missing30304 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19749130441565667328
theorem maskCheck30304 :
    checkMaskFor missing30304 StrongPackedBucketN12A4Shard236.record30304 = true := by
  decide

def missing30305 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27747523379775668224
theorem maskCheck30305 :
    checkMaskFor missing30305 StrongPackedBucketN12A4Shard236.record30305 = true := by
  decide

def missing30306 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27819580973813596160
theorem maskCheck30306 :
    checkMaskFor missing30306 StrongPackedBucketN12A4Shard236.record30306 = true := by
  decide

def missing30307 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28828387290344587264
theorem maskCheck30307 :
    checkMaskFor missing30307 StrongPackedBucketN12A4Shard236.record30307 = true := by
  decide

def missing30308 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 257973466771226624
theorem maskCheck30308 :
    checkMaskFor missing30308 StrongPackedBucketN12A4Shard236.record30308 = true := by
  decide

def missing30309 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 474146248885010432
theorem maskCheck30309 :
    checkMaskFor missing30309 StrongPackedBucketN12A4Shard236.record30309 = true := by
  decide

def missing30310 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9589431894682894336
theorem maskCheck30310 :
    checkMaskFor missing30310 StrongPackedBucketN12A4Shard236.record30310 = true := by
  decide

def missing30311 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10093835052948389888
theorem maskCheck30311 :
    checkMaskFor missing30311 StrongPackedBucketN12A4Shard236.record30311 = true := by
  decide

def missing30312 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10454123023138029568
theorem maskCheck30312 :
    checkMaskFor missing30312 StrongPackedBucketN12A4Shard236.record30312 = true := by
  decide

def missing30313 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11823217309858660352
theorem maskCheck30313 :
    checkMaskFor missing30313 StrongPackedBucketN12A4Shard236.record30313 = true := by
  decide

def missing30314 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18632659946442850304
theorem maskCheck30314 :
    checkMaskFor missing30314 StrongPackedBucketN12A4Shard236.record30314 = true := by
  decide

def missing30315 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27747945592240734208
theorem maskCheck30315 :
    checkMaskFor missing30315 StrongPackedBucketN12A4Shard236.record30315 = true := by
  decide

def missing30316 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27964118374354518016
theorem maskCheck30316 :
    checkMaskFor missing30316 StrongPackedBucketN12A4Shard236.record30316 = true := by
  decide

def missing30317 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29981731007416500224
theorem maskCheck30317 :
    checkMaskFor missing30317 StrongPackedBucketN12A4Shard236.record30317 = true := by
  decide

def missing30318 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9877803008322961408
theorem maskCheck30318 :
    checkMaskFor missing30318 StrongPackedBucketN12A4Shard236.record30318 = true := by
  decide

def missing30319 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9949860602360889344
theorem maskCheck30319 :
    checkMaskFor missing30319 StrongPackedBucketN12A4Shard236.record30319 = true := by
  decide

def missing30320 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10093975790436745216
theorem maskCheck30320 :
    checkMaskFor missing30320 StrongPackedBucketN12A4Shard236.record30320 = true := by
  decide

def missing30321 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10958666918891880448
theorem maskCheck30321 :
    checkMaskFor missing30321 StrongPackedBucketN12A4Shard236.record30321 = true := by
  decide

def missing30322 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12111588423498727424
theorem maskCheck30322 :
    checkMaskFor missing30322 StrongPackedBucketN12A4Shard236.record30322 = true := by
  decide

def missing30323 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27748086329729089536
theorem maskCheck30323 :
    checkMaskFor missing30323 StrongPackedBucketN12A4Shard236.record30323 = true := by
  decide

def missing30324 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27820143923767017472
theorem maskCheck30324 :
    checkMaskFor missing30324 StrongPackedBucketN12A4Shard236.record30324 = true := by
  decide

def missing30325 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29981871744904855552
theorem maskCheck30325 :
    checkMaskFor missing30325 StrongPackedBucketN12A4Shard236.record30325 = true := by
  decide

def missing30326 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 270428734490673152
theorem maskCheck30326 :
    checkMaskFor missing30326 StrongPackedBucketN12A4Shard236.record30326 = true := by
  decide

def missing30327 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4810057158880133120
theorem maskCheck30327 :
    checkMaskFor missing30327 StrongPackedBucketN12A4Shard236.record30327 = true := by
  decide

def missing30328 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4846085955899097088
theorem maskCheck30328 :
    checkMaskFor missing30328 StrongPackedBucketN12A4Shard236.record30328 = true := by
  decide

def missing30329 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13889314007659053056
theorem maskCheck30329 :
    checkMaskFor missing30329 StrongPackedBucketN12A4Shard236.record30329 = true := by
  decide

def missing30330 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14141515586791800832
theorem maskCheck30330 :
    checkMaskFor missing30330 StrongPackedBucketN12A4Shard236.record30330 = true := by
  decide

def missing30331 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15006206715246936064
theorem maskCheck30331 :
    checkMaskFor missing30331 StrongPackedBucketN12A4Shard236.record30331 = true := by
  decide

def missing30332 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 270569471979028480
theorem maskCheck30332 :
    checkMaskFor missing30332 StrongPackedBucketN12A4Shard236.record30332 = true := by
  decide

def missing30333 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4738140302330560512
theorem maskCheck30333 :
    checkMaskFor missing30333 StrongPackedBucketN12A4Shard236.record30333 = true := by
  decide

def missing30334 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4810197896368488448
theorem maskCheck30334 :
    checkMaskFor missing30334 StrongPackedBucketN12A4Shard236.record30334 = true := by
  decide

def missing30335 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4990341881463308288
theorem maskCheck30335 :
    checkMaskFor missing30335 StrongPackedBucketN12A4Shard236.record30335 = true := by
  decide

def missing30208_30209 : List (BitVec (edgeCount 12)) :=
  [missing30208]
abbrev records30208_30209 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30208]
theorem aligned30208_30209 :
    AlignedValid 12 4 missing30208_30209 records30208_30209 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30208
    maskCheck30208 AlignedValid.nil

def missing30209_30210 : List (BitVec (edgeCount 12)) :=
  [missing30209]
abbrev records30209_30210 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30209]
theorem aligned30209_30210 :
    AlignedValid 12 4 missing30209_30210 records30209_30210 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30209
    maskCheck30209 AlignedValid.nil

def missing30208_30210 : List (BitVec (edgeCount 12)) :=
  missing30208_30209 ++ missing30209_30210
abbrev records30208_30210 : List Blob :=
  records30208_30209 ++ records30209_30210
theorem aligned30208_30210 :
    AlignedValid 12 4 missing30208_30210 records30208_30210 :=
  aligned30208_30209.append aligned30209_30210

def missing30210_30211 : List (BitVec (edgeCount 12)) :=
  [missing30210]
abbrev records30210_30211 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30210]
theorem aligned30210_30211 :
    AlignedValid 12 4 missing30210_30211 records30210_30211 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30210
    maskCheck30210 AlignedValid.nil

def missing30211_30212 : List (BitVec (edgeCount 12)) :=
  [missing30211]
abbrev records30211_30212 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30211]
theorem aligned30211_30212 :
    AlignedValid 12 4 missing30211_30212 records30211_30212 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30211
    maskCheck30211 AlignedValid.nil

def missing30210_30212 : List (BitVec (edgeCount 12)) :=
  missing30210_30211 ++ missing30211_30212
abbrev records30210_30212 : List Blob :=
  records30210_30211 ++ records30211_30212
theorem aligned30210_30212 :
    AlignedValid 12 4 missing30210_30212 records30210_30212 :=
  aligned30210_30211.append aligned30211_30212

def missing30208_30212 : List (BitVec (edgeCount 12)) :=
  missing30208_30210 ++ missing30210_30212
abbrev records30208_30212 : List Blob :=
  records30208_30210 ++ records30210_30212
theorem aligned30208_30212 :
    AlignedValid 12 4 missing30208_30212 records30208_30212 :=
  aligned30208_30210.append aligned30210_30212

def missing30212_30213 : List (BitVec (edgeCount 12)) :=
  [missing30212]
abbrev records30212_30213 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30212]
theorem aligned30212_30213 :
    AlignedValid 12 4 missing30212_30213 records30212_30213 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30212
    maskCheck30212 AlignedValid.nil

def missing30213_30214 : List (BitVec (edgeCount 12)) :=
  [missing30213]
abbrev records30213_30214 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30213]
theorem aligned30213_30214 :
    AlignedValid 12 4 missing30213_30214 records30213_30214 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30213
    maskCheck30213 AlignedValid.nil

def missing30212_30214 : List (BitVec (edgeCount 12)) :=
  missing30212_30213 ++ missing30213_30214
abbrev records30212_30214 : List Blob :=
  records30212_30213 ++ records30213_30214
theorem aligned30212_30214 :
    AlignedValid 12 4 missing30212_30214 records30212_30214 :=
  aligned30212_30213.append aligned30213_30214

def missing30214_30215 : List (BitVec (edgeCount 12)) :=
  [missing30214]
abbrev records30214_30215 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30214]
theorem aligned30214_30215 :
    AlignedValid 12 4 missing30214_30215 records30214_30215 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30214
    maskCheck30214 AlignedValid.nil

def missing30215_30216 : List (BitVec (edgeCount 12)) :=
  [missing30215]
abbrev records30215_30216 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30215]
theorem aligned30215_30216 :
    AlignedValid 12 4 missing30215_30216 records30215_30216 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30215
    maskCheck30215 AlignedValid.nil

def missing30214_30216 : List (BitVec (edgeCount 12)) :=
  missing30214_30215 ++ missing30215_30216
abbrev records30214_30216 : List Blob :=
  records30214_30215 ++ records30215_30216
theorem aligned30214_30216 :
    AlignedValid 12 4 missing30214_30216 records30214_30216 :=
  aligned30214_30215.append aligned30215_30216

def missing30212_30216 : List (BitVec (edgeCount 12)) :=
  missing30212_30214 ++ missing30214_30216
abbrev records30212_30216 : List Blob :=
  records30212_30214 ++ records30214_30216
theorem aligned30212_30216 :
    AlignedValid 12 4 missing30212_30216 records30212_30216 :=
  aligned30212_30214.append aligned30214_30216

def missing30208_30216 : List (BitVec (edgeCount 12)) :=
  missing30208_30212 ++ missing30212_30216
abbrev records30208_30216 : List Blob :=
  records30208_30212 ++ records30212_30216
theorem aligned30208_30216 :
    AlignedValid 12 4 missing30208_30216 records30208_30216 :=
  aligned30208_30212.append aligned30212_30216

def missing30216_30217 : List (BitVec (edgeCount 12)) :=
  [missing30216]
abbrev records30216_30217 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30216]
theorem aligned30216_30217 :
    AlignedValid 12 4 missing30216_30217 records30216_30217 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30216
    maskCheck30216 AlignedValid.nil

def missing30217_30218 : List (BitVec (edgeCount 12)) :=
  [missing30217]
abbrev records30217_30218 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30217]
theorem aligned30217_30218 :
    AlignedValid 12 4 missing30217_30218 records30217_30218 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30217
    maskCheck30217 AlignedValid.nil

def missing30216_30218 : List (BitVec (edgeCount 12)) :=
  missing30216_30217 ++ missing30217_30218
abbrev records30216_30218 : List Blob :=
  records30216_30217 ++ records30217_30218
theorem aligned30216_30218 :
    AlignedValid 12 4 missing30216_30218 records30216_30218 :=
  aligned30216_30217.append aligned30217_30218

def missing30218_30219 : List (BitVec (edgeCount 12)) :=
  [missing30218]
abbrev records30218_30219 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30218]
theorem aligned30218_30219 :
    AlignedValid 12 4 missing30218_30219 records30218_30219 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30218
    maskCheck30218 AlignedValid.nil

def missing30219_30220 : List (BitVec (edgeCount 12)) :=
  [missing30219]
abbrev records30219_30220 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30219]
theorem aligned30219_30220 :
    AlignedValid 12 4 missing30219_30220 records30219_30220 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30219
    maskCheck30219 AlignedValid.nil

def missing30218_30220 : List (BitVec (edgeCount 12)) :=
  missing30218_30219 ++ missing30219_30220
abbrev records30218_30220 : List Blob :=
  records30218_30219 ++ records30219_30220
theorem aligned30218_30220 :
    AlignedValid 12 4 missing30218_30220 records30218_30220 :=
  aligned30218_30219.append aligned30219_30220

def missing30216_30220 : List (BitVec (edgeCount 12)) :=
  missing30216_30218 ++ missing30218_30220
abbrev records30216_30220 : List Blob :=
  records30216_30218 ++ records30218_30220
theorem aligned30216_30220 :
    AlignedValid 12 4 missing30216_30220 records30216_30220 :=
  aligned30216_30218.append aligned30218_30220

def missing30220_30221 : List (BitVec (edgeCount 12)) :=
  [missing30220]
abbrev records30220_30221 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30220]
theorem aligned30220_30221 :
    AlignedValid 12 4 missing30220_30221 records30220_30221 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30220
    maskCheck30220 AlignedValid.nil

def missing30221_30222 : List (BitVec (edgeCount 12)) :=
  [missing30221]
abbrev records30221_30222 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30221]
theorem aligned30221_30222 :
    AlignedValid 12 4 missing30221_30222 records30221_30222 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30221
    maskCheck30221 AlignedValid.nil

def missing30220_30222 : List (BitVec (edgeCount 12)) :=
  missing30220_30221 ++ missing30221_30222
abbrev records30220_30222 : List Blob :=
  records30220_30221 ++ records30221_30222
theorem aligned30220_30222 :
    AlignedValid 12 4 missing30220_30222 records30220_30222 :=
  aligned30220_30221.append aligned30221_30222

def missing30222_30223 : List (BitVec (edgeCount 12)) :=
  [missing30222]
abbrev records30222_30223 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30222]
theorem aligned30222_30223 :
    AlignedValid 12 4 missing30222_30223 records30222_30223 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30222
    maskCheck30222 AlignedValid.nil

def missing30223_30224 : List (BitVec (edgeCount 12)) :=
  [missing30223]
abbrev records30223_30224 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30223]
theorem aligned30223_30224 :
    AlignedValid 12 4 missing30223_30224 records30223_30224 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30223
    maskCheck30223 AlignedValid.nil

def missing30222_30224 : List (BitVec (edgeCount 12)) :=
  missing30222_30223 ++ missing30223_30224
abbrev records30222_30224 : List Blob :=
  records30222_30223 ++ records30223_30224
theorem aligned30222_30224 :
    AlignedValid 12 4 missing30222_30224 records30222_30224 :=
  aligned30222_30223.append aligned30223_30224

def missing30220_30224 : List (BitVec (edgeCount 12)) :=
  missing30220_30222 ++ missing30222_30224
abbrev records30220_30224 : List Blob :=
  records30220_30222 ++ records30222_30224
theorem aligned30220_30224 :
    AlignedValid 12 4 missing30220_30224 records30220_30224 :=
  aligned30220_30222.append aligned30222_30224

def missing30216_30224 : List (BitVec (edgeCount 12)) :=
  missing30216_30220 ++ missing30220_30224
abbrev records30216_30224 : List Blob :=
  records30216_30220 ++ records30220_30224
theorem aligned30216_30224 :
    AlignedValid 12 4 missing30216_30224 records30216_30224 :=
  aligned30216_30220.append aligned30220_30224

def missing30208_30224 : List (BitVec (edgeCount 12)) :=
  missing30208_30216 ++ missing30216_30224
abbrev records30208_30224 : List Blob :=
  records30208_30216 ++ records30216_30224
theorem aligned30208_30224 :
    AlignedValid 12 4 missing30208_30224 records30208_30224 :=
  aligned30208_30216.append aligned30216_30224

def missing30224_30225 : List (BitVec (edgeCount 12)) :=
  [missing30224]
abbrev records30224_30225 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30224]
theorem aligned30224_30225 :
    AlignedValid 12 4 missing30224_30225 records30224_30225 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30224
    maskCheck30224 AlignedValid.nil

def missing30225_30226 : List (BitVec (edgeCount 12)) :=
  [missing30225]
abbrev records30225_30226 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30225]
theorem aligned30225_30226 :
    AlignedValid 12 4 missing30225_30226 records30225_30226 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30225
    maskCheck30225 AlignedValid.nil

def missing30224_30226 : List (BitVec (edgeCount 12)) :=
  missing30224_30225 ++ missing30225_30226
abbrev records30224_30226 : List Blob :=
  records30224_30225 ++ records30225_30226
theorem aligned30224_30226 :
    AlignedValid 12 4 missing30224_30226 records30224_30226 :=
  aligned30224_30225.append aligned30225_30226

def missing30226_30227 : List (BitVec (edgeCount 12)) :=
  [missing30226]
abbrev records30226_30227 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30226]
theorem aligned30226_30227 :
    AlignedValid 12 4 missing30226_30227 records30226_30227 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30226
    maskCheck30226 AlignedValid.nil

def missing30227_30228 : List (BitVec (edgeCount 12)) :=
  [missing30227]
abbrev records30227_30228 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30227]
theorem aligned30227_30228 :
    AlignedValid 12 4 missing30227_30228 records30227_30228 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30227
    maskCheck30227 AlignedValid.nil

def missing30226_30228 : List (BitVec (edgeCount 12)) :=
  missing30226_30227 ++ missing30227_30228
abbrev records30226_30228 : List Blob :=
  records30226_30227 ++ records30227_30228
theorem aligned30226_30228 :
    AlignedValid 12 4 missing30226_30228 records30226_30228 :=
  aligned30226_30227.append aligned30227_30228

def missing30224_30228 : List (BitVec (edgeCount 12)) :=
  missing30224_30226 ++ missing30226_30228
abbrev records30224_30228 : List Blob :=
  records30224_30226 ++ records30226_30228
theorem aligned30224_30228 :
    AlignedValid 12 4 missing30224_30228 records30224_30228 :=
  aligned30224_30226.append aligned30226_30228

def missing30228_30229 : List (BitVec (edgeCount 12)) :=
  [missing30228]
abbrev records30228_30229 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30228]
theorem aligned30228_30229 :
    AlignedValid 12 4 missing30228_30229 records30228_30229 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30228
    maskCheck30228 AlignedValid.nil

def missing30229_30230 : List (BitVec (edgeCount 12)) :=
  [missing30229]
abbrev records30229_30230 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30229]
theorem aligned30229_30230 :
    AlignedValid 12 4 missing30229_30230 records30229_30230 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30229
    maskCheck30229 AlignedValid.nil

def missing30228_30230 : List (BitVec (edgeCount 12)) :=
  missing30228_30229 ++ missing30229_30230
abbrev records30228_30230 : List Blob :=
  records30228_30229 ++ records30229_30230
theorem aligned30228_30230 :
    AlignedValid 12 4 missing30228_30230 records30228_30230 :=
  aligned30228_30229.append aligned30229_30230

def missing30230_30231 : List (BitVec (edgeCount 12)) :=
  [missing30230]
abbrev records30230_30231 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30230]
theorem aligned30230_30231 :
    AlignedValid 12 4 missing30230_30231 records30230_30231 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30230
    maskCheck30230 AlignedValid.nil

def missing30231_30232 : List (BitVec (edgeCount 12)) :=
  [missing30231]
abbrev records30231_30232 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30231]
theorem aligned30231_30232 :
    AlignedValid 12 4 missing30231_30232 records30231_30232 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30231
    maskCheck30231 AlignedValid.nil

def missing30230_30232 : List (BitVec (edgeCount 12)) :=
  missing30230_30231 ++ missing30231_30232
abbrev records30230_30232 : List Blob :=
  records30230_30231 ++ records30231_30232
theorem aligned30230_30232 :
    AlignedValid 12 4 missing30230_30232 records30230_30232 :=
  aligned30230_30231.append aligned30231_30232

def missing30228_30232 : List (BitVec (edgeCount 12)) :=
  missing30228_30230 ++ missing30230_30232
abbrev records30228_30232 : List Blob :=
  records30228_30230 ++ records30230_30232
theorem aligned30228_30232 :
    AlignedValid 12 4 missing30228_30232 records30228_30232 :=
  aligned30228_30230.append aligned30230_30232

def missing30224_30232 : List (BitVec (edgeCount 12)) :=
  missing30224_30228 ++ missing30228_30232
abbrev records30224_30232 : List Blob :=
  records30224_30228 ++ records30228_30232
theorem aligned30224_30232 :
    AlignedValid 12 4 missing30224_30232 records30224_30232 :=
  aligned30224_30228.append aligned30228_30232

def missing30232_30233 : List (BitVec (edgeCount 12)) :=
  [missing30232]
abbrev records30232_30233 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30232]
theorem aligned30232_30233 :
    AlignedValid 12 4 missing30232_30233 records30232_30233 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30232
    maskCheck30232 AlignedValid.nil

def missing30233_30234 : List (BitVec (edgeCount 12)) :=
  [missing30233]
abbrev records30233_30234 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30233]
theorem aligned30233_30234 :
    AlignedValid 12 4 missing30233_30234 records30233_30234 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30233
    maskCheck30233 AlignedValid.nil

def missing30232_30234 : List (BitVec (edgeCount 12)) :=
  missing30232_30233 ++ missing30233_30234
abbrev records30232_30234 : List Blob :=
  records30232_30233 ++ records30233_30234
theorem aligned30232_30234 :
    AlignedValid 12 4 missing30232_30234 records30232_30234 :=
  aligned30232_30233.append aligned30233_30234

def missing30234_30235 : List (BitVec (edgeCount 12)) :=
  [missing30234]
abbrev records30234_30235 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30234]
theorem aligned30234_30235 :
    AlignedValid 12 4 missing30234_30235 records30234_30235 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30234
    maskCheck30234 AlignedValid.nil

def missing30235_30236 : List (BitVec (edgeCount 12)) :=
  [missing30235]
abbrev records30235_30236 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30235]
theorem aligned30235_30236 :
    AlignedValid 12 4 missing30235_30236 records30235_30236 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30235
    maskCheck30235 AlignedValid.nil

def missing30234_30236 : List (BitVec (edgeCount 12)) :=
  missing30234_30235 ++ missing30235_30236
abbrev records30234_30236 : List Blob :=
  records30234_30235 ++ records30235_30236
theorem aligned30234_30236 :
    AlignedValid 12 4 missing30234_30236 records30234_30236 :=
  aligned30234_30235.append aligned30235_30236

def missing30232_30236 : List (BitVec (edgeCount 12)) :=
  missing30232_30234 ++ missing30234_30236
abbrev records30232_30236 : List Blob :=
  records30232_30234 ++ records30234_30236
theorem aligned30232_30236 :
    AlignedValid 12 4 missing30232_30236 records30232_30236 :=
  aligned30232_30234.append aligned30234_30236

def missing30236_30237 : List (BitVec (edgeCount 12)) :=
  [missing30236]
abbrev records30236_30237 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30236]
theorem aligned30236_30237 :
    AlignedValid 12 4 missing30236_30237 records30236_30237 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30236
    maskCheck30236 AlignedValid.nil

def missing30237_30238 : List (BitVec (edgeCount 12)) :=
  [missing30237]
abbrev records30237_30238 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30237]
theorem aligned30237_30238 :
    AlignedValid 12 4 missing30237_30238 records30237_30238 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30237
    maskCheck30237 AlignedValid.nil

def missing30236_30238 : List (BitVec (edgeCount 12)) :=
  missing30236_30237 ++ missing30237_30238
abbrev records30236_30238 : List Blob :=
  records30236_30237 ++ records30237_30238
theorem aligned30236_30238 :
    AlignedValid 12 4 missing30236_30238 records30236_30238 :=
  aligned30236_30237.append aligned30237_30238

def missing30238_30239 : List (BitVec (edgeCount 12)) :=
  [missing30238]
abbrev records30238_30239 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30238]
theorem aligned30238_30239 :
    AlignedValid 12 4 missing30238_30239 records30238_30239 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30238
    maskCheck30238 AlignedValid.nil

def missing30239_30240 : List (BitVec (edgeCount 12)) :=
  [missing30239]
abbrev records30239_30240 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30239]
theorem aligned30239_30240 :
    AlignedValid 12 4 missing30239_30240 records30239_30240 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30239
    maskCheck30239 AlignedValid.nil

def missing30238_30240 : List (BitVec (edgeCount 12)) :=
  missing30238_30239 ++ missing30239_30240
abbrev records30238_30240 : List Blob :=
  records30238_30239 ++ records30239_30240
theorem aligned30238_30240 :
    AlignedValid 12 4 missing30238_30240 records30238_30240 :=
  aligned30238_30239.append aligned30239_30240

def missing30236_30240 : List (BitVec (edgeCount 12)) :=
  missing30236_30238 ++ missing30238_30240
abbrev records30236_30240 : List Blob :=
  records30236_30238 ++ records30238_30240
theorem aligned30236_30240 :
    AlignedValid 12 4 missing30236_30240 records30236_30240 :=
  aligned30236_30238.append aligned30238_30240

def missing30232_30240 : List (BitVec (edgeCount 12)) :=
  missing30232_30236 ++ missing30236_30240
abbrev records30232_30240 : List Blob :=
  records30232_30236 ++ records30236_30240
theorem aligned30232_30240 :
    AlignedValid 12 4 missing30232_30240 records30232_30240 :=
  aligned30232_30236.append aligned30236_30240

def missing30224_30240 : List (BitVec (edgeCount 12)) :=
  missing30224_30232 ++ missing30232_30240
abbrev records30224_30240 : List Blob :=
  records30224_30232 ++ records30232_30240
theorem aligned30224_30240 :
    AlignedValid 12 4 missing30224_30240 records30224_30240 :=
  aligned30224_30232.append aligned30232_30240

def missing30208_30240 : List (BitVec (edgeCount 12)) :=
  missing30208_30224 ++ missing30224_30240
abbrev records30208_30240 : List Blob :=
  records30208_30224 ++ records30224_30240
theorem aligned30208_30240 :
    AlignedValid 12 4 missing30208_30240 records30208_30240 :=
  aligned30208_30224.append aligned30224_30240

def missing30240_30241 : List (BitVec (edgeCount 12)) :=
  [missing30240]
abbrev records30240_30241 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30240]
theorem aligned30240_30241 :
    AlignedValid 12 4 missing30240_30241 records30240_30241 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30240
    maskCheck30240 AlignedValid.nil

def missing30241_30242 : List (BitVec (edgeCount 12)) :=
  [missing30241]
abbrev records30241_30242 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30241]
theorem aligned30241_30242 :
    AlignedValid 12 4 missing30241_30242 records30241_30242 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30241
    maskCheck30241 AlignedValid.nil

def missing30240_30242 : List (BitVec (edgeCount 12)) :=
  missing30240_30241 ++ missing30241_30242
abbrev records30240_30242 : List Blob :=
  records30240_30241 ++ records30241_30242
theorem aligned30240_30242 :
    AlignedValid 12 4 missing30240_30242 records30240_30242 :=
  aligned30240_30241.append aligned30241_30242

def missing30242_30243 : List (BitVec (edgeCount 12)) :=
  [missing30242]
abbrev records30242_30243 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30242]
theorem aligned30242_30243 :
    AlignedValid 12 4 missing30242_30243 records30242_30243 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30242
    maskCheck30242 AlignedValid.nil

def missing30243_30244 : List (BitVec (edgeCount 12)) :=
  [missing30243]
abbrev records30243_30244 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30243]
theorem aligned30243_30244 :
    AlignedValid 12 4 missing30243_30244 records30243_30244 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30243
    maskCheck30243 AlignedValid.nil

def missing30242_30244 : List (BitVec (edgeCount 12)) :=
  missing30242_30243 ++ missing30243_30244
abbrev records30242_30244 : List Blob :=
  records30242_30243 ++ records30243_30244
theorem aligned30242_30244 :
    AlignedValid 12 4 missing30242_30244 records30242_30244 :=
  aligned30242_30243.append aligned30243_30244

def missing30240_30244 : List (BitVec (edgeCount 12)) :=
  missing30240_30242 ++ missing30242_30244
abbrev records30240_30244 : List Blob :=
  records30240_30242 ++ records30242_30244
theorem aligned30240_30244 :
    AlignedValid 12 4 missing30240_30244 records30240_30244 :=
  aligned30240_30242.append aligned30242_30244

def missing30244_30245 : List (BitVec (edgeCount 12)) :=
  [missing30244]
abbrev records30244_30245 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30244]
theorem aligned30244_30245 :
    AlignedValid 12 4 missing30244_30245 records30244_30245 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30244
    maskCheck30244 AlignedValid.nil

def missing30245_30246 : List (BitVec (edgeCount 12)) :=
  [missing30245]
abbrev records30245_30246 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30245]
theorem aligned30245_30246 :
    AlignedValid 12 4 missing30245_30246 records30245_30246 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30245
    maskCheck30245 AlignedValid.nil

def missing30244_30246 : List (BitVec (edgeCount 12)) :=
  missing30244_30245 ++ missing30245_30246
abbrev records30244_30246 : List Blob :=
  records30244_30245 ++ records30245_30246
theorem aligned30244_30246 :
    AlignedValid 12 4 missing30244_30246 records30244_30246 :=
  aligned30244_30245.append aligned30245_30246

def missing30246_30247 : List (BitVec (edgeCount 12)) :=
  [missing30246]
abbrev records30246_30247 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30246]
theorem aligned30246_30247 :
    AlignedValid 12 4 missing30246_30247 records30246_30247 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30246
    maskCheck30246 AlignedValid.nil

def missing30247_30248 : List (BitVec (edgeCount 12)) :=
  [missing30247]
abbrev records30247_30248 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30247]
theorem aligned30247_30248 :
    AlignedValid 12 4 missing30247_30248 records30247_30248 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30247
    maskCheck30247 AlignedValid.nil

def missing30246_30248 : List (BitVec (edgeCount 12)) :=
  missing30246_30247 ++ missing30247_30248
abbrev records30246_30248 : List Blob :=
  records30246_30247 ++ records30247_30248
theorem aligned30246_30248 :
    AlignedValid 12 4 missing30246_30248 records30246_30248 :=
  aligned30246_30247.append aligned30247_30248

def missing30244_30248 : List (BitVec (edgeCount 12)) :=
  missing30244_30246 ++ missing30246_30248
abbrev records30244_30248 : List Blob :=
  records30244_30246 ++ records30246_30248
theorem aligned30244_30248 :
    AlignedValid 12 4 missing30244_30248 records30244_30248 :=
  aligned30244_30246.append aligned30246_30248

def missing30240_30248 : List (BitVec (edgeCount 12)) :=
  missing30240_30244 ++ missing30244_30248
abbrev records30240_30248 : List Blob :=
  records30240_30244 ++ records30244_30248
theorem aligned30240_30248 :
    AlignedValid 12 4 missing30240_30248 records30240_30248 :=
  aligned30240_30244.append aligned30244_30248

def missing30248_30249 : List (BitVec (edgeCount 12)) :=
  [missing30248]
abbrev records30248_30249 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30248]
theorem aligned30248_30249 :
    AlignedValid 12 4 missing30248_30249 records30248_30249 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30248
    maskCheck30248 AlignedValid.nil

def missing30249_30250 : List (BitVec (edgeCount 12)) :=
  [missing30249]
abbrev records30249_30250 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30249]
theorem aligned30249_30250 :
    AlignedValid 12 4 missing30249_30250 records30249_30250 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30249
    maskCheck30249 AlignedValid.nil

def missing30248_30250 : List (BitVec (edgeCount 12)) :=
  missing30248_30249 ++ missing30249_30250
abbrev records30248_30250 : List Blob :=
  records30248_30249 ++ records30249_30250
theorem aligned30248_30250 :
    AlignedValid 12 4 missing30248_30250 records30248_30250 :=
  aligned30248_30249.append aligned30249_30250

def missing30250_30251 : List (BitVec (edgeCount 12)) :=
  [missing30250]
abbrev records30250_30251 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30250]
theorem aligned30250_30251 :
    AlignedValid 12 4 missing30250_30251 records30250_30251 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30250
    maskCheck30250 AlignedValid.nil

def missing30251_30252 : List (BitVec (edgeCount 12)) :=
  [missing30251]
abbrev records30251_30252 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30251]
theorem aligned30251_30252 :
    AlignedValid 12 4 missing30251_30252 records30251_30252 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30251
    maskCheck30251 AlignedValid.nil

def missing30250_30252 : List (BitVec (edgeCount 12)) :=
  missing30250_30251 ++ missing30251_30252
abbrev records30250_30252 : List Blob :=
  records30250_30251 ++ records30251_30252
theorem aligned30250_30252 :
    AlignedValid 12 4 missing30250_30252 records30250_30252 :=
  aligned30250_30251.append aligned30251_30252

def missing30248_30252 : List (BitVec (edgeCount 12)) :=
  missing30248_30250 ++ missing30250_30252
abbrev records30248_30252 : List Blob :=
  records30248_30250 ++ records30250_30252
theorem aligned30248_30252 :
    AlignedValid 12 4 missing30248_30252 records30248_30252 :=
  aligned30248_30250.append aligned30250_30252

def missing30252_30253 : List (BitVec (edgeCount 12)) :=
  [missing30252]
abbrev records30252_30253 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30252]
theorem aligned30252_30253 :
    AlignedValid 12 4 missing30252_30253 records30252_30253 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30252
    maskCheck30252 AlignedValid.nil

def missing30253_30254 : List (BitVec (edgeCount 12)) :=
  [missing30253]
abbrev records30253_30254 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30253]
theorem aligned30253_30254 :
    AlignedValid 12 4 missing30253_30254 records30253_30254 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30253
    maskCheck30253 AlignedValid.nil

def missing30252_30254 : List (BitVec (edgeCount 12)) :=
  missing30252_30253 ++ missing30253_30254
abbrev records30252_30254 : List Blob :=
  records30252_30253 ++ records30253_30254
theorem aligned30252_30254 :
    AlignedValid 12 4 missing30252_30254 records30252_30254 :=
  aligned30252_30253.append aligned30253_30254

def missing30254_30255 : List (BitVec (edgeCount 12)) :=
  [missing30254]
abbrev records30254_30255 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30254]
theorem aligned30254_30255 :
    AlignedValid 12 4 missing30254_30255 records30254_30255 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30254
    maskCheck30254 AlignedValid.nil

def missing30255_30256 : List (BitVec (edgeCount 12)) :=
  [missing30255]
abbrev records30255_30256 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30255]
theorem aligned30255_30256 :
    AlignedValid 12 4 missing30255_30256 records30255_30256 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30255
    maskCheck30255 AlignedValid.nil

def missing30254_30256 : List (BitVec (edgeCount 12)) :=
  missing30254_30255 ++ missing30255_30256
abbrev records30254_30256 : List Blob :=
  records30254_30255 ++ records30255_30256
theorem aligned30254_30256 :
    AlignedValid 12 4 missing30254_30256 records30254_30256 :=
  aligned30254_30255.append aligned30255_30256

def missing30252_30256 : List (BitVec (edgeCount 12)) :=
  missing30252_30254 ++ missing30254_30256
abbrev records30252_30256 : List Blob :=
  records30252_30254 ++ records30254_30256
theorem aligned30252_30256 :
    AlignedValid 12 4 missing30252_30256 records30252_30256 :=
  aligned30252_30254.append aligned30254_30256

def missing30248_30256 : List (BitVec (edgeCount 12)) :=
  missing30248_30252 ++ missing30252_30256
abbrev records30248_30256 : List Blob :=
  records30248_30252 ++ records30252_30256
theorem aligned30248_30256 :
    AlignedValid 12 4 missing30248_30256 records30248_30256 :=
  aligned30248_30252.append aligned30252_30256

def missing30240_30256 : List (BitVec (edgeCount 12)) :=
  missing30240_30248 ++ missing30248_30256
abbrev records30240_30256 : List Blob :=
  records30240_30248 ++ records30248_30256
theorem aligned30240_30256 :
    AlignedValid 12 4 missing30240_30256 records30240_30256 :=
  aligned30240_30248.append aligned30248_30256

def missing30256_30257 : List (BitVec (edgeCount 12)) :=
  [missing30256]
abbrev records30256_30257 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30256]
theorem aligned30256_30257 :
    AlignedValid 12 4 missing30256_30257 records30256_30257 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30256
    maskCheck30256 AlignedValid.nil

def missing30257_30258 : List (BitVec (edgeCount 12)) :=
  [missing30257]
abbrev records30257_30258 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30257]
theorem aligned30257_30258 :
    AlignedValid 12 4 missing30257_30258 records30257_30258 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30257
    maskCheck30257 AlignedValid.nil

def missing30256_30258 : List (BitVec (edgeCount 12)) :=
  missing30256_30257 ++ missing30257_30258
abbrev records30256_30258 : List Blob :=
  records30256_30257 ++ records30257_30258
theorem aligned30256_30258 :
    AlignedValid 12 4 missing30256_30258 records30256_30258 :=
  aligned30256_30257.append aligned30257_30258

def missing30258_30259 : List (BitVec (edgeCount 12)) :=
  [missing30258]
abbrev records30258_30259 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30258]
theorem aligned30258_30259 :
    AlignedValid 12 4 missing30258_30259 records30258_30259 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30258
    maskCheck30258 AlignedValid.nil

def missing30259_30260 : List (BitVec (edgeCount 12)) :=
  [missing30259]
abbrev records30259_30260 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30259]
theorem aligned30259_30260 :
    AlignedValid 12 4 missing30259_30260 records30259_30260 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30259
    maskCheck30259 AlignedValid.nil

def missing30258_30260 : List (BitVec (edgeCount 12)) :=
  missing30258_30259 ++ missing30259_30260
abbrev records30258_30260 : List Blob :=
  records30258_30259 ++ records30259_30260
theorem aligned30258_30260 :
    AlignedValid 12 4 missing30258_30260 records30258_30260 :=
  aligned30258_30259.append aligned30259_30260

def missing30256_30260 : List (BitVec (edgeCount 12)) :=
  missing30256_30258 ++ missing30258_30260
abbrev records30256_30260 : List Blob :=
  records30256_30258 ++ records30258_30260
theorem aligned30256_30260 :
    AlignedValid 12 4 missing30256_30260 records30256_30260 :=
  aligned30256_30258.append aligned30258_30260

def missing30260_30261 : List (BitVec (edgeCount 12)) :=
  [missing30260]
abbrev records30260_30261 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30260]
theorem aligned30260_30261 :
    AlignedValid 12 4 missing30260_30261 records30260_30261 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30260
    maskCheck30260 AlignedValid.nil

def missing30261_30262 : List (BitVec (edgeCount 12)) :=
  [missing30261]
abbrev records30261_30262 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30261]
theorem aligned30261_30262 :
    AlignedValid 12 4 missing30261_30262 records30261_30262 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30261
    maskCheck30261 AlignedValid.nil

def missing30260_30262 : List (BitVec (edgeCount 12)) :=
  missing30260_30261 ++ missing30261_30262
abbrev records30260_30262 : List Blob :=
  records30260_30261 ++ records30261_30262
theorem aligned30260_30262 :
    AlignedValid 12 4 missing30260_30262 records30260_30262 :=
  aligned30260_30261.append aligned30261_30262

def missing30262_30263 : List (BitVec (edgeCount 12)) :=
  [missing30262]
abbrev records30262_30263 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30262]
theorem aligned30262_30263 :
    AlignedValid 12 4 missing30262_30263 records30262_30263 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30262
    maskCheck30262 AlignedValid.nil

def missing30263_30264 : List (BitVec (edgeCount 12)) :=
  [missing30263]
abbrev records30263_30264 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30263]
theorem aligned30263_30264 :
    AlignedValid 12 4 missing30263_30264 records30263_30264 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30263
    maskCheck30263 AlignedValid.nil

def missing30262_30264 : List (BitVec (edgeCount 12)) :=
  missing30262_30263 ++ missing30263_30264
abbrev records30262_30264 : List Blob :=
  records30262_30263 ++ records30263_30264
theorem aligned30262_30264 :
    AlignedValid 12 4 missing30262_30264 records30262_30264 :=
  aligned30262_30263.append aligned30263_30264

def missing30260_30264 : List (BitVec (edgeCount 12)) :=
  missing30260_30262 ++ missing30262_30264
abbrev records30260_30264 : List Blob :=
  records30260_30262 ++ records30262_30264
theorem aligned30260_30264 :
    AlignedValid 12 4 missing30260_30264 records30260_30264 :=
  aligned30260_30262.append aligned30262_30264

def missing30256_30264 : List (BitVec (edgeCount 12)) :=
  missing30256_30260 ++ missing30260_30264
abbrev records30256_30264 : List Blob :=
  records30256_30260 ++ records30260_30264
theorem aligned30256_30264 :
    AlignedValid 12 4 missing30256_30264 records30256_30264 :=
  aligned30256_30260.append aligned30260_30264

def missing30264_30265 : List (BitVec (edgeCount 12)) :=
  [missing30264]
abbrev records30264_30265 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30264]
theorem aligned30264_30265 :
    AlignedValid 12 4 missing30264_30265 records30264_30265 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30264
    maskCheck30264 AlignedValid.nil

def missing30265_30266 : List (BitVec (edgeCount 12)) :=
  [missing30265]
abbrev records30265_30266 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30265]
theorem aligned30265_30266 :
    AlignedValid 12 4 missing30265_30266 records30265_30266 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30265
    maskCheck30265 AlignedValid.nil

def missing30264_30266 : List (BitVec (edgeCount 12)) :=
  missing30264_30265 ++ missing30265_30266
abbrev records30264_30266 : List Blob :=
  records30264_30265 ++ records30265_30266
theorem aligned30264_30266 :
    AlignedValid 12 4 missing30264_30266 records30264_30266 :=
  aligned30264_30265.append aligned30265_30266

def missing30266_30267 : List (BitVec (edgeCount 12)) :=
  [missing30266]
abbrev records30266_30267 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30266]
theorem aligned30266_30267 :
    AlignedValid 12 4 missing30266_30267 records30266_30267 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30266
    maskCheck30266 AlignedValid.nil

def missing30267_30268 : List (BitVec (edgeCount 12)) :=
  [missing30267]
abbrev records30267_30268 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30267]
theorem aligned30267_30268 :
    AlignedValid 12 4 missing30267_30268 records30267_30268 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30267
    maskCheck30267 AlignedValid.nil

def missing30266_30268 : List (BitVec (edgeCount 12)) :=
  missing30266_30267 ++ missing30267_30268
abbrev records30266_30268 : List Blob :=
  records30266_30267 ++ records30267_30268
theorem aligned30266_30268 :
    AlignedValid 12 4 missing30266_30268 records30266_30268 :=
  aligned30266_30267.append aligned30267_30268

def missing30264_30268 : List (BitVec (edgeCount 12)) :=
  missing30264_30266 ++ missing30266_30268
abbrev records30264_30268 : List Blob :=
  records30264_30266 ++ records30266_30268
theorem aligned30264_30268 :
    AlignedValid 12 4 missing30264_30268 records30264_30268 :=
  aligned30264_30266.append aligned30266_30268

def missing30268_30269 : List (BitVec (edgeCount 12)) :=
  [missing30268]
abbrev records30268_30269 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30268]
theorem aligned30268_30269 :
    AlignedValid 12 4 missing30268_30269 records30268_30269 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30268
    maskCheck30268 AlignedValid.nil

def missing30269_30270 : List (BitVec (edgeCount 12)) :=
  [missing30269]
abbrev records30269_30270 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30269]
theorem aligned30269_30270 :
    AlignedValid 12 4 missing30269_30270 records30269_30270 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30269
    maskCheck30269 AlignedValid.nil

def missing30268_30270 : List (BitVec (edgeCount 12)) :=
  missing30268_30269 ++ missing30269_30270
abbrev records30268_30270 : List Blob :=
  records30268_30269 ++ records30269_30270
theorem aligned30268_30270 :
    AlignedValid 12 4 missing30268_30270 records30268_30270 :=
  aligned30268_30269.append aligned30269_30270

def missing30270_30271 : List (BitVec (edgeCount 12)) :=
  [missing30270]
abbrev records30270_30271 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30270]
theorem aligned30270_30271 :
    AlignedValid 12 4 missing30270_30271 records30270_30271 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30270
    maskCheck30270 AlignedValid.nil

def missing30271_30272 : List (BitVec (edgeCount 12)) :=
  [missing30271]
abbrev records30271_30272 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30271]
theorem aligned30271_30272 :
    AlignedValid 12 4 missing30271_30272 records30271_30272 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30271
    maskCheck30271 AlignedValid.nil

def missing30270_30272 : List (BitVec (edgeCount 12)) :=
  missing30270_30271 ++ missing30271_30272
abbrev records30270_30272 : List Blob :=
  records30270_30271 ++ records30271_30272
theorem aligned30270_30272 :
    AlignedValid 12 4 missing30270_30272 records30270_30272 :=
  aligned30270_30271.append aligned30271_30272

def missing30268_30272 : List (BitVec (edgeCount 12)) :=
  missing30268_30270 ++ missing30270_30272
abbrev records30268_30272 : List Blob :=
  records30268_30270 ++ records30270_30272
theorem aligned30268_30272 :
    AlignedValid 12 4 missing30268_30272 records30268_30272 :=
  aligned30268_30270.append aligned30270_30272

def missing30264_30272 : List (BitVec (edgeCount 12)) :=
  missing30264_30268 ++ missing30268_30272
abbrev records30264_30272 : List Blob :=
  records30264_30268 ++ records30268_30272
theorem aligned30264_30272 :
    AlignedValid 12 4 missing30264_30272 records30264_30272 :=
  aligned30264_30268.append aligned30268_30272

def missing30256_30272 : List (BitVec (edgeCount 12)) :=
  missing30256_30264 ++ missing30264_30272
abbrev records30256_30272 : List Blob :=
  records30256_30264 ++ records30264_30272
theorem aligned30256_30272 :
    AlignedValid 12 4 missing30256_30272 records30256_30272 :=
  aligned30256_30264.append aligned30264_30272

def missing30240_30272 : List (BitVec (edgeCount 12)) :=
  missing30240_30256 ++ missing30256_30272
abbrev records30240_30272 : List Blob :=
  records30240_30256 ++ records30256_30272
theorem aligned30240_30272 :
    AlignedValid 12 4 missing30240_30272 records30240_30272 :=
  aligned30240_30256.append aligned30256_30272

def missing30208_30272 : List (BitVec (edgeCount 12)) :=
  missing30208_30240 ++ missing30240_30272
abbrev records30208_30272 : List Blob :=
  records30208_30240 ++ records30240_30272
theorem aligned30208_30272 :
    AlignedValid 12 4 missing30208_30272 records30208_30272 :=
  aligned30208_30240.append aligned30240_30272

def missing30272_30273 : List (BitVec (edgeCount 12)) :=
  [missing30272]
abbrev records30272_30273 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30272]
theorem aligned30272_30273 :
    AlignedValid 12 4 missing30272_30273 records30272_30273 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30272
    maskCheck30272 AlignedValid.nil

def missing30273_30274 : List (BitVec (edgeCount 12)) :=
  [missing30273]
abbrev records30273_30274 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30273]
theorem aligned30273_30274 :
    AlignedValid 12 4 missing30273_30274 records30273_30274 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30273
    maskCheck30273 AlignedValid.nil

def missing30272_30274 : List (BitVec (edgeCount 12)) :=
  missing30272_30273 ++ missing30273_30274
abbrev records30272_30274 : List Blob :=
  records30272_30273 ++ records30273_30274
theorem aligned30272_30274 :
    AlignedValid 12 4 missing30272_30274 records30272_30274 :=
  aligned30272_30273.append aligned30273_30274

def missing30274_30275 : List (BitVec (edgeCount 12)) :=
  [missing30274]
abbrev records30274_30275 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30274]
theorem aligned30274_30275 :
    AlignedValid 12 4 missing30274_30275 records30274_30275 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30274
    maskCheck30274 AlignedValid.nil

def missing30275_30276 : List (BitVec (edgeCount 12)) :=
  [missing30275]
abbrev records30275_30276 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30275]
theorem aligned30275_30276 :
    AlignedValid 12 4 missing30275_30276 records30275_30276 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30275
    maskCheck30275 AlignedValid.nil

def missing30274_30276 : List (BitVec (edgeCount 12)) :=
  missing30274_30275 ++ missing30275_30276
abbrev records30274_30276 : List Blob :=
  records30274_30275 ++ records30275_30276
theorem aligned30274_30276 :
    AlignedValid 12 4 missing30274_30276 records30274_30276 :=
  aligned30274_30275.append aligned30275_30276

def missing30272_30276 : List (BitVec (edgeCount 12)) :=
  missing30272_30274 ++ missing30274_30276
abbrev records30272_30276 : List Blob :=
  records30272_30274 ++ records30274_30276
theorem aligned30272_30276 :
    AlignedValid 12 4 missing30272_30276 records30272_30276 :=
  aligned30272_30274.append aligned30274_30276

def missing30276_30277 : List (BitVec (edgeCount 12)) :=
  [missing30276]
abbrev records30276_30277 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30276]
theorem aligned30276_30277 :
    AlignedValid 12 4 missing30276_30277 records30276_30277 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30276
    maskCheck30276 AlignedValid.nil

def missing30277_30278 : List (BitVec (edgeCount 12)) :=
  [missing30277]
abbrev records30277_30278 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30277]
theorem aligned30277_30278 :
    AlignedValid 12 4 missing30277_30278 records30277_30278 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30277
    maskCheck30277 AlignedValid.nil

def missing30276_30278 : List (BitVec (edgeCount 12)) :=
  missing30276_30277 ++ missing30277_30278
abbrev records30276_30278 : List Blob :=
  records30276_30277 ++ records30277_30278
theorem aligned30276_30278 :
    AlignedValid 12 4 missing30276_30278 records30276_30278 :=
  aligned30276_30277.append aligned30277_30278

def missing30278_30279 : List (BitVec (edgeCount 12)) :=
  [missing30278]
abbrev records30278_30279 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30278]
theorem aligned30278_30279 :
    AlignedValid 12 4 missing30278_30279 records30278_30279 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30278
    maskCheck30278 AlignedValid.nil

def missing30279_30280 : List (BitVec (edgeCount 12)) :=
  [missing30279]
abbrev records30279_30280 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30279]
theorem aligned30279_30280 :
    AlignedValid 12 4 missing30279_30280 records30279_30280 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30279
    maskCheck30279 AlignedValid.nil

def missing30278_30280 : List (BitVec (edgeCount 12)) :=
  missing30278_30279 ++ missing30279_30280
abbrev records30278_30280 : List Blob :=
  records30278_30279 ++ records30279_30280
theorem aligned30278_30280 :
    AlignedValid 12 4 missing30278_30280 records30278_30280 :=
  aligned30278_30279.append aligned30279_30280

def missing30276_30280 : List (BitVec (edgeCount 12)) :=
  missing30276_30278 ++ missing30278_30280
abbrev records30276_30280 : List Blob :=
  records30276_30278 ++ records30278_30280
theorem aligned30276_30280 :
    AlignedValid 12 4 missing30276_30280 records30276_30280 :=
  aligned30276_30278.append aligned30278_30280

def missing30272_30280 : List (BitVec (edgeCount 12)) :=
  missing30272_30276 ++ missing30276_30280
abbrev records30272_30280 : List Blob :=
  records30272_30276 ++ records30276_30280
theorem aligned30272_30280 :
    AlignedValid 12 4 missing30272_30280 records30272_30280 :=
  aligned30272_30276.append aligned30276_30280

def missing30280_30281 : List (BitVec (edgeCount 12)) :=
  [missing30280]
abbrev records30280_30281 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30280]
theorem aligned30280_30281 :
    AlignedValid 12 4 missing30280_30281 records30280_30281 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30280
    maskCheck30280 AlignedValid.nil

def missing30281_30282 : List (BitVec (edgeCount 12)) :=
  [missing30281]
abbrev records30281_30282 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30281]
theorem aligned30281_30282 :
    AlignedValid 12 4 missing30281_30282 records30281_30282 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30281
    maskCheck30281 AlignedValid.nil

def missing30280_30282 : List (BitVec (edgeCount 12)) :=
  missing30280_30281 ++ missing30281_30282
abbrev records30280_30282 : List Blob :=
  records30280_30281 ++ records30281_30282
theorem aligned30280_30282 :
    AlignedValid 12 4 missing30280_30282 records30280_30282 :=
  aligned30280_30281.append aligned30281_30282

def missing30282_30283 : List (BitVec (edgeCount 12)) :=
  [missing30282]
abbrev records30282_30283 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30282]
theorem aligned30282_30283 :
    AlignedValid 12 4 missing30282_30283 records30282_30283 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30282
    maskCheck30282 AlignedValid.nil

def missing30283_30284 : List (BitVec (edgeCount 12)) :=
  [missing30283]
abbrev records30283_30284 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30283]
theorem aligned30283_30284 :
    AlignedValid 12 4 missing30283_30284 records30283_30284 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30283
    maskCheck30283 AlignedValid.nil

def missing30282_30284 : List (BitVec (edgeCount 12)) :=
  missing30282_30283 ++ missing30283_30284
abbrev records30282_30284 : List Blob :=
  records30282_30283 ++ records30283_30284
theorem aligned30282_30284 :
    AlignedValid 12 4 missing30282_30284 records30282_30284 :=
  aligned30282_30283.append aligned30283_30284

def missing30280_30284 : List (BitVec (edgeCount 12)) :=
  missing30280_30282 ++ missing30282_30284
abbrev records30280_30284 : List Blob :=
  records30280_30282 ++ records30282_30284
theorem aligned30280_30284 :
    AlignedValid 12 4 missing30280_30284 records30280_30284 :=
  aligned30280_30282.append aligned30282_30284

def missing30284_30285 : List (BitVec (edgeCount 12)) :=
  [missing30284]
abbrev records30284_30285 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30284]
theorem aligned30284_30285 :
    AlignedValid 12 4 missing30284_30285 records30284_30285 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30284
    maskCheck30284 AlignedValid.nil

def missing30285_30286 : List (BitVec (edgeCount 12)) :=
  [missing30285]
abbrev records30285_30286 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30285]
theorem aligned30285_30286 :
    AlignedValid 12 4 missing30285_30286 records30285_30286 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30285
    maskCheck30285 AlignedValid.nil

def missing30284_30286 : List (BitVec (edgeCount 12)) :=
  missing30284_30285 ++ missing30285_30286
abbrev records30284_30286 : List Blob :=
  records30284_30285 ++ records30285_30286
theorem aligned30284_30286 :
    AlignedValid 12 4 missing30284_30286 records30284_30286 :=
  aligned30284_30285.append aligned30285_30286

def missing30286_30287 : List (BitVec (edgeCount 12)) :=
  [missing30286]
abbrev records30286_30287 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30286]
theorem aligned30286_30287 :
    AlignedValid 12 4 missing30286_30287 records30286_30287 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30286
    maskCheck30286 AlignedValid.nil

def missing30287_30288 : List (BitVec (edgeCount 12)) :=
  [missing30287]
abbrev records30287_30288 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30287]
theorem aligned30287_30288 :
    AlignedValid 12 4 missing30287_30288 records30287_30288 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30287
    maskCheck30287 AlignedValid.nil

def missing30286_30288 : List (BitVec (edgeCount 12)) :=
  missing30286_30287 ++ missing30287_30288
abbrev records30286_30288 : List Blob :=
  records30286_30287 ++ records30287_30288
theorem aligned30286_30288 :
    AlignedValid 12 4 missing30286_30288 records30286_30288 :=
  aligned30286_30287.append aligned30287_30288

def missing30284_30288 : List (BitVec (edgeCount 12)) :=
  missing30284_30286 ++ missing30286_30288
abbrev records30284_30288 : List Blob :=
  records30284_30286 ++ records30286_30288
theorem aligned30284_30288 :
    AlignedValid 12 4 missing30284_30288 records30284_30288 :=
  aligned30284_30286.append aligned30286_30288

def missing30280_30288 : List (BitVec (edgeCount 12)) :=
  missing30280_30284 ++ missing30284_30288
abbrev records30280_30288 : List Blob :=
  records30280_30284 ++ records30284_30288
theorem aligned30280_30288 :
    AlignedValid 12 4 missing30280_30288 records30280_30288 :=
  aligned30280_30284.append aligned30284_30288

def missing30272_30288 : List (BitVec (edgeCount 12)) :=
  missing30272_30280 ++ missing30280_30288
abbrev records30272_30288 : List Blob :=
  records30272_30280 ++ records30280_30288
theorem aligned30272_30288 :
    AlignedValid 12 4 missing30272_30288 records30272_30288 :=
  aligned30272_30280.append aligned30280_30288

def missing30288_30289 : List (BitVec (edgeCount 12)) :=
  [missing30288]
abbrev records30288_30289 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30288]
theorem aligned30288_30289 :
    AlignedValid 12 4 missing30288_30289 records30288_30289 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30288
    maskCheck30288 AlignedValid.nil

def missing30289_30290 : List (BitVec (edgeCount 12)) :=
  [missing30289]
abbrev records30289_30290 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30289]
theorem aligned30289_30290 :
    AlignedValid 12 4 missing30289_30290 records30289_30290 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30289
    maskCheck30289 AlignedValid.nil

def missing30288_30290 : List (BitVec (edgeCount 12)) :=
  missing30288_30289 ++ missing30289_30290
abbrev records30288_30290 : List Blob :=
  records30288_30289 ++ records30289_30290
theorem aligned30288_30290 :
    AlignedValid 12 4 missing30288_30290 records30288_30290 :=
  aligned30288_30289.append aligned30289_30290

def missing30290_30291 : List (BitVec (edgeCount 12)) :=
  [missing30290]
abbrev records30290_30291 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30290]
theorem aligned30290_30291 :
    AlignedValid 12 4 missing30290_30291 records30290_30291 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30290
    maskCheck30290 AlignedValid.nil

def missing30291_30292 : List (BitVec (edgeCount 12)) :=
  [missing30291]
abbrev records30291_30292 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30291]
theorem aligned30291_30292 :
    AlignedValid 12 4 missing30291_30292 records30291_30292 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30291
    maskCheck30291 AlignedValid.nil

def missing30290_30292 : List (BitVec (edgeCount 12)) :=
  missing30290_30291 ++ missing30291_30292
abbrev records30290_30292 : List Blob :=
  records30290_30291 ++ records30291_30292
theorem aligned30290_30292 :
    AlignedValid 12 4 missing30290_30292 records30290_30292 :=
  aligned30290_30291.append aligned30291_30292

def missing30288_30292 : List (BitVec (edgeCount 12)) :=
  missing30288_30290 ++ missing30290_30292
abbrev records30288_30292 : List Blob :=
  records30288_30290 ++ records30290_30292
theorem aligned30288_30292 :
    AlignedValid 12 4 missing30288_30292 records30288_30292 :=
  aligned30288_30290.append aligned30290_30292

def missing30292_30293 : List (BitVec (edgeCount 12)) :=
  [missing30292]
abbrev records30292_30293 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30292]
theorem aligned30292_30293 :
    AlignedValid 12 4 missing30292_30293 records30292_30293 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30292
    maskCheck30292 AlignedValid.nil

def missing30293_30294 : List (BitVec (edgeCount 12)) :=
  [missing30293]
abbrev records30293_30294 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30293]
theorem aligned30293_30294 :
    AlignedValid 12 4 missing30293_30294 records30293_30294 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30293
    maskCheck30293 AlignedValid.nil

def missing30292_30294 : List (BitVec (edgeCount 12)) :=
  missing30292_30293 ++ missing30293_30294
abbrev records30292_30294 : List Blob :=
  records30292_30293 ++ records30293_30294
theorem aligned30292_30294 :
    AlignedValid 12 4 missing30292_30294 records30292_30294 :=
  aligned30292_30293.append aligned30293_30294

def missing30294_30295 : List (BitVec (edgeCount 12)) :=
  [missing30294]
abbrev records30294_30295 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30294]
theorem aligned30294_30295 :
    AlignedValid 12 4 missing30294_30295 records30294_30295 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30294
    maskCheck30294 AlignedValid.nil

def missing30295_30296 : List (BitVec (edgeCount 12)) :=
  [missing30295]
abbrev records30295_30296 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30295]
theorem aligned30295_30296 :
    AlignedValid 12 4 missing30295_30296 records30295_30296 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30295
    maskCheck30295 AlignedValid.nil

def missing30294_30296 : List (BitVec (edgeCount 12)) :=
  missing30294_30295 ++ missing30295_30296
abbrev records30294_30296 : List Blob :=
  records30294_30295 ++ records30295_30296
theorem aligned30294_30296 :
    AlignedValid 12 4 missing30294_30296 records30294_30296 :=
  aligned30294_30295.append aligned30295_30296

def missing30292_30296 : List (BitVec (edgeCount 12)) :=
  missing30292_30294 ++ missing30294_30296
abbrev records30292_30296 : List Blob :=
  records30292_30294 ++ records30294_30296
theorem aligned30292_30296 :
    AlignedValid 12 4 missing30292_30296 records30292_30296 :=
  aligned30292_30294.append aligned30294_30296

def missing30288_30296 : List (BitVec (edgeCount 12)) :=
  missing30288_30292 ++ missing30292_30296
abbrev records30288_30296 : List Blob :=
  records30288_30292 ++ records30292_30296
theorem aligned30288_30296 :
    AlignedValid 12 4 missing30288_30296 records30288_30296 :=
  aligned30288_30292.append aligned30292_30296

def missing30296_30297 : List (BitVec (edgeCount 12)) :=
  [missing30296]
abbrev records30296_30297 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30296]
theorem aligned30296_30297 :
    AlignedValid 12 4 missing30296_30297 records30296_30297 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30296
    maskCheck30296 AlignedValid.nil

def missing30297_30298 : List (BitVec (edgeCount 12)) :=
  [missing30297]
abbrev records30297_30298 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30297]
theorem aligned30297_30298 :
    AlignedValid 12 4 missing30297_30298 records30297_30298 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30297
    maskCheck30297 AlignedValid.nil

def missing30296_30298 : List (BitVec (edgeCount 12)) :=
  missing30296_30297 ++ missing30297_30298
abbrev records30296_30298 : List Blob :=
  records30296_30297 ++ records30297_30298
theorem aligned30296_30298 :
    AlignedValid 12 4 missing30296_30298 records30296_30298 :=
  aligned30296_30297.append aligned30297_30298

def missing30298_30299 : List (BitVec (edgeCount 12)) :=
  [missing30298]
abbrev records30298_30299 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30298]
theorem aligned30298_30299 :
    AlignedValid 12 4 missing30298_30299 records30298_30299 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30298
    maskCheck30298 AlignedValid.nil

def missing30299_30300 : List (BitVec (edgeCount 12)) :=
  [missing30299]
abbrev records30299_30300 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30299]
theorem aligned30299_30300 :
    AlignedValid 12 4 missing30299_30300 records30299_30300 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30299
    maskCheck30299 AlignedValid.nil

def missing30298_30300 : List (BitVec (edgeCount 12)) :=
  missing30298_30299 ++ missing30299_30300
abbrev records30298_30300 : List Blob :=
  records30298_30299 ++ records30299_30300
theorem aligned30298_30300 :
    AlignedValid 12 4 missing30298_30300 records30298_30300 :=
  aligned30298_30299.append aligned30299_30300

def missing30296_30300 : List (BitVec (edgeCount 12)) :=
  missing30296_30298 ++ missing30298_30300
abbrev records30296_30300 : List Blob :=
  records30296_30298 ++ records30298_30300
theorem aligned30296_30300 :
    AlignedValid 12 4 missing30296_30300 records30296_30300 :=
  aligned30296_30298.append aligned30298_30300

def missing30300_30301 : List (BitVec (edgeCount 12)) :=
  [missing30300]
abbrev records30300_30301 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30300]
theorem aligned30300_30301 :
    AlignedValid 12 4 missing30300_30301 records30300_30301 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30300
    maskCheck30300 AlignedValid.nil

def missing30301_30302 : List (BitVec (edgeCount 12)) :=
  [missing30301]
abbrev records30301_30302 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30301]
theorem aligned30301_30302 :
    AlignedValid 12 4 missing30301_30302 records30301_30302 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30301
    maskCheck30301 AlignedValid.nil

def missing30300_30302 : List (BitVec (edgeCount 12)) :=
  missing30300_30301 ++ missing30301_30302
abbrev records30300_30302 : List Blob :=
  records30300_30301 ++ records30301_30302
theorem aligned30300_30302 :
    AlignedValid 12 4 missing30300_30302 records30300_30302 :=
  aligned30300_30301.append aligned30301_30302

def missing30302_30303 : List (BitVec (edgeCount 12)) :=
  [missing30302]
abbrev records30302_30303 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30302]
theorem aligned30302_30303 :
    AlignedValid 12 4 missing30302_30303 records30302_30303 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30302
    maskCheck30302 AlignedValid.nil

def missing30303_30304 : List (BitVec (edgeCount 12)) :=
  [missing30303]
abbrev records30303_30304 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30303]
theorem aligned30303_30304 :
    AlignedValid 12 4 missing30303_30304 records30303_30304 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30303
    maskCheck30303 AlignedValid.nil

def missing30302_30304 : List (BitVec (edgeCount 12)) :=
  missing30302_30303 ++ missing30303_30304
abbrev records30302_30304 : List Blob :=
  records30302_30303 ++ records30303_30304
theorem aligned30302_30304 :
    AlignedValid 12 4 missing30302_30304 records30302_30304 :=
  aligned30302_30303.append aligned30303_30304

def missing30300_30304 : List (BitVec (edgeCount 12)) :=
  missing30300_30302 ++ missing30302_30304
abbrev records30300_30304 : List Blob :=
  records30300_30302 ++ records30302_30304
theorem aligned30300_30304 :
    AlignedValid 12 4 missing30300_30304 records30300_30304 :=
  aligned30300_30302.append aligned30302_30304

def missing30296_30304 : List (BitVec (edgeCount 12)) :=
  missing30296_30300 ++ missing30300_30304
abbrev records30296_30304 : List Blob :=
  records30296_30300 ++ records30300_30304
theorem aligned30296_30304 :
    AlignedValid 12 4 missing30296_30304 records30296_30304 :=
  aligned30296_30300.append aligned30300_30304

def missing30288_30304 : List (BitVec (edgeCount 12)) :=
  missing30288_30296 ++ missing30296_30304
abbrev records30288_30304 : List Blob :=
  records30288_30296 ++ records30296_30304
theorem aligned30288_30304 :
    AlignedValid 12 4 missing30288_30304 records30288_30304 :=
  aligned30288_30296.append aligned30296_30304

def missing30272_30304 : List (BitVec (edgeCount 12)) :=
  missing30272_30288 ++ missing30288_30304
abbrev records30272_30304 : List Blob :=
  records30272_30288 ++ records30288_30304
theorem aligned30272_30304 :
    AlignedValid 12 4 missing30272_30304 records30272_30304 :=
  aligned30272_30288.append aligned30288_30304

def missing30304_30305 : List (BitVec (edgeCount 12)) :=
  [missing30304]
abbrev records30304_30305 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30304]
theorem aligned30304_30305 :
    AlignedValid 12 4 missing30304_30305 records30304_30305 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30304
    maskCheck30304 AlignedValid.nil

def missing30305_30306 : List (BitVec (edgeCount 12)) :=
  [missing30305]
abbrev records30305_30306 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30305]
theorem aligned30305_30306 :
    AlignedValid 12 4 missing30305_30306 records30305_30306 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30305
    maskCheck30305 AlignedValid.nil

def missing30304_30306 : List (BitVec (edgeCount 12)) :=
  missing30304_30305 ++ missing30305_30306
abbrev records30304_30306 : List Blob :=
  records30304_30305 ++ records30305_30306
theorem aligned30304_30306 :
    AlignedValid 12 4 missing30304_30306 records30304_30306 :=
  aligned30304_30305.append aligned30305_30306

def missing30306_30307 : List (BitVec (edgeCount 12)) :=
  [missing30306]
abbrev records30306_30307 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30306]
theorem aligned30306_30307 :
    AlignedValid 12 4 missing30306_30307 records30306_30307 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30306
    maskCheck30306 AlignedValid.nil

def missing30307_30308 : List (BitVec (edgeCount 12)) :=
  [missing30307]
abbrev records30307_30308 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30307]
theorem aligned30307_30308 :
    AlignedValid 12 4 missing30307_30308 records30307_30308 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30307
    maskCheck30307 AlignedValid.nil

def missing30306_30308 : List (BitVec (edgeCount 12)) :=
  missing30306_30307 ++ missing30307_30308
abbrev records30306_30308 : List Blob :=
  records30306_30307 ++ records30307_30308
theorem aligned30306_30308 :
    AlignedValid 12 4 missing30306_30308 records30306_30308 :=
  aligned30306_30307.append aligned30307_30308

def missing30304_30308 : List (BitVec (edgeCount 12)) :=
  missing30304_30306 ++ missing30306_30308
abbrev records30304_30308 : List Blob :=
  records30304_30306 ++ records30306_30308
theorem aligned30304_30308 :
    AlignedValid 12 4 missing30304_30308 records30304_30308 :=
  aligned30304_30306.append aligned30306_30308

def missing30308_30309 : List (BitVec (edgeCount 12)) :=
  [missing30308]
abbrev records30308_30309 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30308]
theorem aligned30308_30309 :
    AlignedValid 12 4 missing30308_30309 records30308_30309 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30308
    maskCheck30308 AlignedValid.nil

def missing30309_30310 : List (BitVec (edgeCount 12)) :=
  [missing30309]
abbrev records30309_30310 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30309]
theorem aligned30309_30310 :
    AlignedValid 12 4 missing30309_30310 records30309_30310 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30309
    maskCheck30309 AlignedValid.nil

def missing30308_30310 : List (BitVec (edgeCount 12)) :=
  missing30308_30309 ++ missing30309_30310
abbrev records30308_30310 : List Blob :=
  records30308_30309 ++ records30309_30310
theorem aligned30308_30310 :
    AlignedValid 12 4 missing30308_30310 records30308_30310 :=
  aligned30308_30309.append aligned30309_30310

def missing30310_30311 : List (BitVec (edgeCount 12)) :=
  [missing30310]
abbrev records30310_30311 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30310]
theorem aligned30310_30311 :
    AlignedValid 12 4 missing30310_30311 records30310_30311 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30310
    maskCheck30310 AlignedValid.nil

def missing30311_30312 : List (BitVec (edgeCount 12)) :=
  [missing30311]
abbrev records30311_30312 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30311]
theorem aligned30311_30312 :
    AlignedValid 12 4 missing30311_30312 records30311_30312 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30311
    maskCheck30311 AlignedValid.nil

def missing30310_30312 : List (BitVec (edgeCount 12)) :=
  missing30310_30311 ++ missing30311_30312
abbrev records30310_30312 : List Blob :=
  records30310_30311 ++ records30311_30312
theorem aligned30310_30312 :
    AlignedValid 12 4 missing30310_30312 records30310_30312 :=
  aligned30310_30311.append aligned30311_30312

def missing30308_30312 : List (BitVec (edgeCount 12)) :=
  missing30308_30310 ++ missing30310_30312
abbrev records30308_30312 : List Blob :=
  records30308_30310 ++ records30310_30312
theorem aligned30308_30312 :
    AlignedValid 12 4 missing30308_30312 records30308_30312 :=
  aligned30308_30310.append aligned30310_30312

def missing30304_30312 : List (BitVec (edgeCount 12)) :=
  missing30304_30308 ++ missing30308_30312
abbrev records30304_30312 : List Blob :=
  records30304_30308 ++ records30308_30312
theorem aligned30304_30312 :
    AlignedValid 12 4 missing30304_30312 records30304_30312 :=
  aligned30304_30308.append aligned30308_30312

def missing30312_30313 : List (BitVec (edgeCount 12)) :=
  [missing30312]
abbrev records30312_30313 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30312]
theorem aligned30312_30313 :
    AlignedValid 12 4 missing30312_30313 records30312_30313 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30312
    maskCheck30312 AlignedValid.nil

def missing30313_30314 : List (BitVec (edgeCount 12)) :=
  [missing30313]
abbrev records30313_30314 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30313]
theorem aligned30313_30314 :
    AlignedValid 12 4 missing30313_30314 records30313_30314 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30313
    maskCheck30313 AlignedValid.nil

def missing30312_30314 : List (BitVec (edgeCount 12)) :=
  missing30312_30313 ++ missing30313_30314
abbrev records30312_30314 : List Blob :=
  records30312_30313 ++ records30313_30314
theorem aligned30312_30314 :
    AlignedValid 12 4 missing30312_30314 records30312_30314 :=
  aligned30312_30313.append aligned30313_30314

def missing30314_30315 : List (BitVec (edgeCount 12)) :=
  [missing30314]
abbrev records30314_30315 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30314]
theorem aligned30314_30315 :
    AlignedValid 12 4 missing30314_30315 records30314_30315 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30314
    maskCheck30314 AlignedValid.nil

def missing30315_30316 : List (BitVec (edgeCount 12)) :=
  [missing30315]
abbrev records30315_30316 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30315]
theorem aligned30315_30316 :
    AlignedValid 12 4 missing30315_30316 records30315_30316 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30315
    maskCheck30315 AlignedValid.nil

def missing30314_30316 : List (BitVec (edgeCount 12)) :=
  missing30314_30315 ++ missing30315_30316
abbrev records30314_30316 : List Blob :=
  records30314_30315 ++ records30315_30316
theorem aligned30314_30316 :
    AlignedValid 12 4 missing30314_30316 records30314_30316 :=
  aligned30314_30315.append aligned30315_30316

def missing30312_30316 : List (BitVec (edgeCount 12)) :=
  missing30312_30314 ++ missing30314_30316
abbrev records30312_30316 : List Blob :=
  records30312_30314 ++ records30314_30316
theorem aligned30312_30316 :
    AlignedValid 12 4 missing30312_30316 records30312_30316 :=
  aligned30312_30314.append aligned30314_30316

def missing30316_30317 : List (BitVec (edgeCount 12)) :=
  [missing30316]
abbrev records30316_30317 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30316]
theorem aligned30316_30317 :
    AlignedValid 12 4 missing30316_30317 records30316_30317 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30316
    maskCheck30316 AlignedValid.nil

def missing30317_30318 : List (BitVec (edgeCount 12)) :=
  [missing30317]
abbrev records30317_30318 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30317]
theorem aligned30317_30318 :
    AlignedValid 12 4 missing30317_30318 records30317_30318 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30317
    maskCheck30317 AlignedValid.nil

def missing30316_30318 : List (BitVec (edgeCount 12)) :=
  missing30316_30317 ++ missing30317_30318
abbrev records30316_30318 : List Blob :=
  records30316_30317 ++ records30317_30318
theorem aligned30316_30318 :
    AlignedValid 12 4 missing30316_30318 records30316_30318 :=
  aligned30316_30317.append aligned30317_30318

def missing30318_30319 : List (BitVec (edgeCount 12)) :=
  [missing30318]
abbrev records30318_30319 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30318]
theorem aligned30318_30319 :
    AlignedValid 12 4 missing30318_30319 records30318_30319 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30318
    maskCheck30318 AlignedValid.nil

def missing30319_30320 : List (BitVec (edgeCount 12)) :=
  [missing30319]
abbrev records30319_30320 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30319]
theorem aligned30319_30320 :
    AlignedValid 12 4 missing30319_30320 records30319_30320 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30319
    maskCheck30319 AlignedValid.nil

def missing30318_30320 : List (BitVec (edgeCount 12)) :=
  missing30318_30319 ++ missing30319_30320
abbrev records30318_30320 : List Blob :=
  records30318_30319 ++ records30319_30320
theorem aligned30318_30320 :
    AlignedValid 12 4 missing30318_30320 records30318_30320 :=
  aligned30318_30319.append aligned30319_30320

def missing30316_30320 : List (BitVec (edgeCount 12)) :=
  missing30316_30318 ++ missing30318_30320
abbrev records30316_30320 : List Blob :=
  records30316_30318 ++ records30318_30320
theorem aligned30316_30320 :
    AlignedValid 12 4 missing30316_30320 records30316_30320 :=
  aligned30316_30318.append aligned30318_30320

def missing30312_30320 : List (BitVec (edgeCount 12)) :=
  missing30312_30316 ++ missing30316_30320
abbrev records30312_30320 : List Blob :=
  records30312_30316 ++ records30316_30320
theorem aligned30312_30320 :
    AlignedValid 12 4 missing30312_30320 records30312_30320 :=
  aligned30312_30316.append aligned30316_30320

def missing30304_30320 : List (BitVec (edgeCount 12)) :=
  missing30304_30312 ++ missing30312_30320
abbrev records30304_30320 : List Blob :=
  records30304_30312 ++ records30312_30320
theorem aligned30304_30320 :
    AlignedValid 12 4 missing30304_30320 records30304_30320 :=
  aligned30304_30312.append aligned30312_30320

def missing30320_30321 : List (BitVec (edgeCount 12)) :=
  [missing30320]
abbrev records30320_30321 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30320]
theorem aligned30320_30321 :
    AlignedValid 12 4 missing30320_30321 records30320_30321 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30320
    maskCheck30320 AlignedValid.nil

def missing30321_30322 : List (BitVec (edgeCount 12)) :=
  [missing30321]
abbrev records30321_30322 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30321]
theorem aligned30321_30322 :
    AlignedValid 12 4 missing30321_30322 records30321_30322 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30321
    maskCheck30321 AlignedValid.nil

def missing30320_30322 : List (BitVec (edgeCount 12)) :=
  missing30320_30321 ++ missing30321_30322
abbrev records30320_30322 : List Blob :=
  records30320_30321 ++ records30321_30322
theorem aligned30320_30322 :
    AlignedValid 12 4 missing30320_30322 records30320_30322 :=
  aligned30320_30321.append aligned30321_30322

def missing30322_30323 : List (BitVec (edgeCount 12)) :=
  [missing30322]
abbrev records30322_30323 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30322]
theorem aligned30322_30323 :
    AlignedValid 12 4 missing30322_30323 records30322_30323 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30322
    maskCheck30322 AlignedValid.nil

def missing30323_30324 : List (BitVec (edgeCount 12)) :=
  [missing30323]
abbrev records30323_30324 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30323]
theorem aligned30323_30324 :
    AlignedValid 12 4 missing30323_30324 records30323_30324 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30323
    maskCheck30323 AlignedValid.nil

def missing30322_30324 : List (BitVec (edgeCount 12)) :=
  missing30322_30323 ++ missing30323_30324
abbrev records30322_30324 : List Blob :=
  records30322_30323 ++ records30323_30324
theorem aligned30322_30324 :
    AlignedValid 12 4 missing30322_30324 records30322_30324 :=
  aligned30322_30323.append aligned30323_30324

def missing30320_30324 : List (BitVec (edgeCount 12)) :=
  missing30320_30322 ++ missing30322_30324
abbrev records30320_30324 : List Blob :=
  records30320_30322 ++ records30322_30324
theorem aligned30320_30324 :
    AlignedValid 12 4 missing30320_30324 records30320_30324 :=
  aligned30320_30322.append aligned30322_30324

def missing30324_30325 : List (BitVec (edgeCount 12)) :=
  [missing30324]
abbrev records30324_30325 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30324]
theorem aligned30324_30325 :
    AlignedValid 12 4 missing30324_30325 records30324_30325 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30324
    maskCheck30324 AlignedValid.nil

def missing30325_30326 : List (BitVec (edgeCount 12)) :=
  [missing30325]
abbrev records30325_30326 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30325]
theorem aligned30325_30326 :
    AlignedValid 12 4 missing30325_30326 records30325_30326 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30325
    maskCheck30325 AlignedValid.nil

def missing30324_30326 : List (BitVec (edgeCount 12)) :=
  missing30324_30325 ++ missing30325_30326
abbrev records30324_30326 : List Blob :=
  records30324_30325 ++ records30325_30326
theorem aligned30324_30326 :
    AlignedValid 12 4 missing30324_30326 records30324_30326 :=
  aligned30324_30325.append aligned30325_30326

def missing30326_30327 : List (BitVec (edgeCount 12)) :=
  [missing30326]
abbrev records30326_30327 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30326]
theorem aligned30326_30327 :
    AlignedValid 12 4 missing30326_30327 records30326_30327 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30326
    maskCheck30326 AlignedValid.nil

def missing30327_30328 : List (BitVec (edgeCount 12)) :=
  [missing30327]
abbrev records30327_30328 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30327]
theorem aligned30327_30328 :
    AlignedValid 12 4 missing30327_30328 records30327_30328 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30327
    maskCheck30327 AlignedValid.nil

def missing30326_30328 : List (BitVec (edgeCount 12)) :=
  missing30326_30327 ++ missing30327_30328
abbrev records30326_30328 : List Blob :=
  records30326_30327 ++ records30327_30328
theorem aligned30326_30328 :
    AlignedValid 12 4 missing30326_30328 records30326_30328 :=
  aligned30326_30327.append aligned30327_30328

def missing30324_30328 : List (BitVec (edgeCount 12)) :=
  missing30324_30326 ++ missing30326_30328
abbrev records30324_30328 : List Blob :=
  records30324_30326 ++ records30326_30328
theorem aligned30324_30328 :
    AlignedValid 12 4 missing30324_30328 records30324_30328 :=
  aligned30324_30326.append aligned30326_30328

def missing30320_30328 : List (BitVec (edgeCount 12)) :=
  missing30320_30324 ++ missing30324_30328
abbrev records30320_30328 : List Blob :=
  records30320_30324 ++ records30324_30328
theorem aligned30320_30328 :
    AlignedValid 12 4 missing30320_30328 records30320_30328 :=
  aligned30320_30324.append aligned30324_30328

def missing30328_30329 : List (BitVec (edgeCount 12)) :=
  [missing30328]
abbrev records30328_30329 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30328]
theorem aligned30328_30329 :
    AlignedValid 12 4 missing30328_30329 records30328_30329 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30328
    maskCheck30328 AlignedValid.nil

def missing30329_30330 : List (BitVec (edgeCount 12)) :=
  [missing30329]
abbrev records30329_30330 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30329]
theorem aligned30329_30330 :
    AlignedValid 12 4 missing30329_30330 records30329_30330 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30329
    maskCheck30329 AlignedValid.nil

def missing30328_30330 : List (BitVec (edgeCount 12)) :=
  missing30328_30329 ++ missing30329_30330
abbrev records30328_30330 : List Blob :=
  records30328_30329 ++ records30329_30330
theorem aligned30328_30330 :
    AlignedValid 12 4 missing30328_30330 records30328_30330 :=
  aligned30328_30329.append aligned30329_30330

def missing30330_30331 : List (BitVec (edgeCount 12)) :=
  [missing30330]
abbrev records30330_30331 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30330]
theorem aligned30330_30331 :
    AlignedValid 12 4 missing30330_30331 records30330_30331 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30330
    maskCheck30330 AlignedValid.nil

def missing30331_30332 : List (BitVec (edgeCount 12)) :=
  [missing30331]
abbrev records30331_30332 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30331]
theorem aligned30331_30332 :
    AlignedValid 12 4 missing30331_30332 records30331_30332 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30331
    maskCheck30331 AlignedValid.nil

def missing30330_30332 : List (BitVec (edgeCount 12)) :=
  missing30330_30331 ++ missing30331_30332
abbrev records30330_30332 : List Blob :=
  records30330_30331 ++ records30331_30332
theorem aligned30330_30332 :
    AlignedValid 12 4 missing30330_30332 records30330_30332 :=
  aligned30330_30331.append aligned30331_30332

def missing30328_30332 : List (BitVec (edgeCount 12)) :=
  missing30328_30330 ++ missing30330_30332
abbrev records30328_30332 : List Blob :=
  records30328_30330 ++ records30330_30332
theorem aligned30328_30332 :
    AlignedValid 12 4 missing30328_30332 records30328_30332 :=
  aligned30328_30330.append aligned30330_30332

def missing30332_30333 : List (BitVec (edgeCount 12)) :=
  [missing30332]
abbrev records30332_30333 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30332]
theorem aligned30332_30333 :
    AlignedValid 12 4 missing30332_30333 records30332_30333 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30332
    maskCheck30332 AlignedValid.nil

def missing30333_30334 : List (BitVec (edgeCount 12)) :=
  [missing30333]
abbrev records30333_30334 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30333]
theorem aligned30333_30334 :
    AlignedValid 12 4 missing30333_30334 records30333_30334 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30333
    maskCheck30333 AlignedValid.nil

def missing30332_30334 : List (BitVec (edgeCount 12)) :=
  missing30332_30333 ++ missing30333_30334
abbrev records30332_30334 : List Blob :=
  records30332_30333 ++ records30333_30334
theorem aligned30332_30334 :
    AlignedValid 12 4 missing30332_30334 records30332_30334 :=
  aligned30332_30333.append aligned30333_30334

def missing30334_30335 : List (BitVec (edgeCount 12)) :=
  [missing30334]
abbrev records30334_30335 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30334]
theorem aligned30334_30335 :
    AlignedValid 12 4 missing30334_30335 records30334_30335 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30334
    maskCheck30334 AlignedValid.nil

def missing30335_30336 : List (BitVec (edgeCount 12)) :=
  [missing30335]
abbrev records30335_30336 : List Blob :=
  [StrongPackedBucketN12A4Shard236.record30335]
theorem aligned30335_30336 :
    AlignedValid 12 4 missing30335_30336 records30335_30336 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard236.check30335
    maskCheck30335 AlignedValid.nil

def missing30334_30336 : List (BitVec (edgeCount 12)) :=
  missing30334_30335 ++ missing30335_30336
abbrev records30334_30336 : List Blob :=
  records30334_30335 ++ records30335_30336
theorem aligned30334_30336 :
    AlignedValid 12 4 missing30334_30336 records30334_30336 :=
  aligned30334_30335.append aligned30335_30336

def missing30332_30336 : List (BitVec (edgeCount 12)) :=
  missing30332_30334 ++ missing30334_30336
abbrev records30332_30336 : List Blob :=
  records30332_30334 ++ records30334_30336
theorem aligned30332_30336 :
    AlignedValid 12 4 missing30332_30336 records30332_30336 :=
  aligned30332_30334.append aligned30334_30336

def missing30328_30336 : List (BitVec (edgeCount 12)) :=
  missing30328_30332 ++ missing30332_30336
abbrev records30328_30336 : List Blob :=
  records30328_30332 ++ records30332_30336
theorem aligned30328_30336 :
    AlignedValid 12 4 missing30328_30336 records30328_30336 :=
  aligned30328_30332.append aligned30332_30336

def missing30320_30336 : List (BitVec (edgeCount 12)) :=
  missing30320_30328 ++ missing30328_30336
abbrev records30320_30336 : List Blob :=
  records30320_30328 ++ records30328_30336
theorem aligned30320_30336 :
    AlignedValid 12 4 missing30320_30336 records30320_30336 :=
  aligned30320_30328.append aligned30328_30336

def missing30304_30336 : List (BitVec (edgeCount 12)) :=
  missing30304_30320 ++ missing30320_30336
abbrev records30304_30336 : List Blob :=
  records30304_30320 ++ records30320_30336
theorem aligned30304_30336 :
    AlignedValid 12 4 missing30304_30336 records30304_30336 :=
  aligned30304_30320.append aligned30320_30336

def missing30272_30336 : List (BitVec (edgeCount 12)) :=
  missing30272_30304 ++ missing30304_30336
abbrev records30272_30336 : List Blob :=
  records30272_30304 ++ records30304_30336
theorem aligned30272_30336 :
    AlignedValid 12 4 missing30272_30336 records30272_30336 :=
  aligned30272_30304.append aligned30304_30336

def missing30208_30336 : List (BitVec (edgeCount 12)) :=
  missing30208_30272 ++ missing30272_30336
abbrev records30208_30336 : List Blob :=
  records30208_30272 ++ records30272_30336
theorem aligned30208_30336 :
    AlignedValid 12 4 missing30208_30336 records30208_30336 :=
  aligned30208_30272.append aligned30272_30336

abbrev missing : List (BitVec (edgeCount 12)) := missing30208_30336
abbrev records : List Blob := records30208_30336
theorem aligned : AlignedValid 12 4 missing records := aligned30208_30336

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard236
