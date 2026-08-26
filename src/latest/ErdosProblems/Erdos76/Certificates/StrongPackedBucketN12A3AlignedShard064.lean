/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A3Shard064

/-! Decode-only alignment checks for n=12, a=3, records 8192--8319. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard064

open PackedBucketCertificate

def missing8192 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32335951702809116672
theorem maskCheck8192 :
    checkMaskFor missing8192 StrongPackedBucketN12A3Shard064.record8192 = true := by
  decide

def missing8193 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32444038093866008576
theorem maskCheck8193 :
    checkMaskFor missing8193 StrongPackedBucketN12A3Shard064.record8193 = true := by
  decide

def missing8194 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32876383658093576192
theorem maskCheck8194 :
    checkMaskFor missing8194 StrongPackedBucketN12A3Shard064.record8194 = true := by
  decide

def missing8195 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37163810503350288384
theorem maskCheck8195 :
    checkMaskFor missing8195 StrongPackedBucketN12A3Shard064.record8195 = true := by
  decide

def missing8196 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37379983285464072192
theorem maskCheck8196 :
    checkMaskFor missing8196 StrongPackedBucketN12A3Shard064.record8196 = true := by
  decide

def missing8197 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37596156067577856000
theorem maskCheck8197 :
    checkMaskFor missing8197 StrongPackedBucketN12A3Shard064.record8197 = true := by
  decide

def missing8198 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41631381333701820416
theorem maskCheck8198 :
    checkMaskFor missing8198 StrongPackedBucketN12A3Shard064.record8198 = true := by
  decide

def missing8199 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41703438927739748352
theorem maskCheck8199 :
    checkMaskFor missing8199 StrongPackedBucketN12A3Shard064.record8199 = true := by
  decide

def missing8200 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41739467724758712320
theorem maskCheck8200 :
    checkMaskFor missing8200 StrongPackedBucketN12A3Shard064.record8200 = true := by
  decide

def missing8201 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41955640506872496128
theorem maskCheck8201 :
    checkMaskFor missing8201 StrongPackedBucketN12A3Shard064.record8201 = true := by
  decide

def missing8202 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42135784491967315968
theorem maskCheck8202 :
    checkMaskFor missing8202 StrongPackedBucketN12A3Shard064.record8202 = true := by
  decide

def missing8203 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42171813288986279936
theorem maskCheck8203 :
    checkMaskFor missing8203 StrongPackedBucketN12A3Shard064.record8203 = true := by
  decide

def missing8204 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50782695776518668288
theorem maskCheck8204 :
    checkMaskFor missing8204 StrongPackedBucketN12A3Shard064.record8204 = true := by
  decide

def missing8205 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50890782167575560192
theorem maskCheck8205 :
    checkMaskFor missing8205 StrongPackedBucketN12A3Shard064.record8205 = true := by
  decide

def missing8206 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51323127731803127808
theorem maskCheck8206 :
    checkMaskFor missing8206 StrongPackedBucketN12A3Shard064.record8206 = true := by
  decide

def missing8207 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55466439388983984128
theorem maskCheck8207 :
    checkMaskFor missing8207 StrongPackedBucketN12A3Shard064.record8207 = true := by
  decide

def missing8208 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60006067813373444096
theorem maskCheck8208 :
    checkMaskFor missing8208 StrongPackedBucketN12A3Shard064.record8208 = true := by
  decide

def missing8209 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60042096610392408064
theorem maskCheck8209 :
    checkMaskFor missing8209 StrongPackedBucketN12A3Shard064.record8209 = true := by
  decide

def missing8210 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 69193411053209255936
theorem maskCheck8210 :
    checkMaskFor missing8210 StrongPackedBucketN12A3Shard064.record8210 = true := by
  decide

def missing8211 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 558623100827074560
theorem maskCheck8211 :
    checkMaskFor missing8211 StrongPackedBucketN12A3Shard064.record8211 = true := by
  decide

def missing8212 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 846853476978786304
theorem maskCheck8212 :
    checkMaskFor missing8212 StrongPackedBucketN12A3Shard064.record8212 = true := by
  decide

def missing8213 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 990968665054642176
theorem maskCheck8213 :
    checkMaskFor missing8213 StrongPackedBucketN12A3Shard064.record8213 = true := by
  decide

def missing8214 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1063026259092570112
theorem maskCheck8214 :
    checkMaskFor missing8214 StrongPackedBucketN12A3Shard064.record8214 = true := by
  decide

def missing8215 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1099055056111534080
theorem maskCheck8215 :
    checkMaskFor missing8215 StrongPackedBucketN12A3Shard064.record8215 = true := by
  decide

def missing8216 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1855659793509777408
theorem maskCheck8216 :
    checkMaskFor missing8216 StrongPackedBucketN12A3Shard064.record8216 = true := by
  decide

def missing8217 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1927717387547705344
theorem maskCheck8217 :
    checkMaskFor missing8217 StrongPackedBucketN12A3Shard064.record8217 = true := by
  decide

def missing8218 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1963746184566669312
theorem maskCheck8218 :
    checkMaskFor missing8218 StrongPackedBucketN12A3Shard064.record8218 = true := by
  decide

def missing8219 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2071832575623561216
theorem maskCheck8219 :
    checkMaskFor missing8219 StrongPackedBucketN12A3Shard064.record8219 = true := by
  decide

def missing8220 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2107861372642525184
theorem maskCheck8220 :
    checkMaskFor missing8220 StrongPackedBucketN12A3Shard064.record8220 = true := by
  decide

def missing8221 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2179918966680453120
theorem maskCheck8221 :
    checkMaskFor missing8221 StrongPackedBucketN12A3Shard064.record8221 = true := by
  decide

def missing8222 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4089445208685543424
theorem maskCheck8222 :
    checkMaskFor missing8222 StrongPackedBucketN12A3Shard064.record8222 = true := by
  decide

def missing8223 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4125474005704507392
theorem maskCheck8223 :
    checkMaskFor missing8223 StrongPackedBucketN12A3Shard064.record8223 = true := by
  decide

def missing8224 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4197531599742435328
theorem maskCheck8224 :
    checkMaskFor missing8224 StrongPackedBucketN12A3Shard064.record8224 = true := by
  decide

def missing8225 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4341646787818291200
theorem maskCheck8225 :
    checkMaskFor missing8225 StrongPackedBucketN12A3Shard064.record8225 = true := by
  decide

def missing8226 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4882078743102750720
theorem maskCheck8226 :
    checkMaskFor missing8226 StrongPackedBucketN12A3Shard064.record8226 = true := by
  decide

def missing8227 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5026193931178606592
theorem maskCheck8227 :
    checkMaskFor missing8227 StrongPackedBucketN12A3Shard064.record8227 = true := by
  decide

def missing8228 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5098251525216534528
theorem maskCheck8228 :
    checkMaskFor missing8228 StrongPackedBucketN12A3Shard064.record8228 = true := by
  decide

def missing8229 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5134280322235498496
theorem maskCheck8229 :
    checkMaskFor missing8229 StrongPackedBucketN12A3Shard064.record8229 = true := by
  decide

def missing8230 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5314424307330318336
theorem maskCheck8230 :
    checkMaskFor missing8230 StrongPackedBucketN12A3Shard064.record8230 = true := by
  decide

def missing8231 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5386481901368246272
theorem maskCheck8231 :
    checkMaskFor missing8231 StrongPackedBucketN12A3Shard064.record8231 = true := by
  decide

def missing8232 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5422510698387210240
theorem maskCheck8232 :
    checkMaskFor missing8232 StrongPackedBucketN12A3Shard064.record8232 = true := by
  decide

def missing8233 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5530597089444102144
theorem maskCheck8233 :
    checkMaskFor missing8233 StrongPackedBucketN12A3Shard064.record8233 = true := by
  decide

def missing8234 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5566625886463066112
theorem maskCheck8234 :
    checkMaskFor missing8234 StrongPackedBucketN12A3Shard064.record8234 = true := by
  decide

def missing8235 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5638683480500994048
theorem maskCheck8235 :
    checkMaskFor missing8235 StrongPackedBucketN12A3Shard064.record8235 = true := by
  decide

def missing8236 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6395288217899237376
theorem maskCheck8236 :
    checkMaskFor missing8236 StrongPackedBucketN12A3Shard064.record8236 = true := by
  decide

def missing8237 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6431317014918201344
theorem maskCheck8237 :
    checkMaskFor missing8237 StrongPackedBucketN12A3Shard064.record8237 = true := by
  decide

def missing8238 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6503374608956129280
theorem maskCheck8238 :
    checkMaskFor missing8238 StrongPackedBucketN12A3Shard064.record8238 = true := by
  decide

def missing8239 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6647489797031985152
theorem maskCheck8239 :
    checkMaskFor missing8239 StrongPackedBucketN12A3Shard064.record8239 = true := by
  decide

def missing8240 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8665102430093967360
theorem maskCheck8240 :
    checkMaskFor missing8240 StrongPackedBucketN12A3Shard064.record8240 = true := by
  decide

def missing8241 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9493764761530138624
theorem maskCheck8241 :
    checkMaskFor missing8241 StrongPackedBucketN12A3Shard064.record8241 = true := by
  decide

def missing8242 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9637879949605994496
theorem maskCheck8242 :
    checkMaskFor missing8242 StrongPackedBucketN12A3Shard064.record8242 = true := by
  decide

def missing8243 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9745966340662886400
theorem maskCheck8243 :
    checkMaskFor missing8243 StrongPackedBucketN12A3Shard064.record8243 = true := by
  decide

def missing8244 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9926110325757706240
theorem maskCheck8244 :
    checkMaskFor missing8244 StrongPackedBucketN12A3Shard064.record8244 = true := by
  decide

def missing8245 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10034196716814598144
theorem maskCheck8245 :
    checkMaskFor missing8245 StrongPackedBucketN12A3Shard064.record8245 = true := by
  decide

def missing8246 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10178311904890454016
theorem maskCheck8246 :
    checkMaskFor missing8246 StrongPackedBucketN12A3Shard064.record8246 = true := by
  decide

def missing8247 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11043003033345589248
theorem maskCheck8247 :
    checkMaskFor missing8247 StrongPackedBucketN12A3Shard064.record8247 = true := by
  decide

def missing8248 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13961335591881670656
theorem maskCheck8248 :
    checkMaskFor missing8248 StrongPackedBucketN12A3Shard064.record8248 = true := by
  decide

def missing8249 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14069421982938562560
theorem maskCheck8249 :
    checkMaskFor missing8249 StrongPackedBucketN12A3Shard064.record8249 = true := by
  decide

def missing8250 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14213537171014418432
theorem maskCheck8250 :
    checkMaskFor missing8250 StrongPackedBucketN12A3Shard064.record8250 = true := by
  decide

def missing8251 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14501767547166130176
theorem maskCheck8251 :
    checkMaskFor missing8251 StrongPackedBucketN12A3Shard064.record8251 = true := by
  decide

def missing8252 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18717136798384914432
theorem maskCheck8252 :
    checkMaskFor missing8252 StrongPackedBucketN12A3Shard064.record8252 = true := by
  decide

def missing8253 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18861251986460770304
theorem maskCheck8253 :
    checkMaskFor missing8253 StrongPackedBucketN12A3Shard064.record8253 = true := by
  decide

def missing8254 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18969338377517662208
theorem maskCheck8254 :
    checkMaskFor missing8254 StrongPackedBucketN12A3Shard064.record8254 = true := by
  decide

def missing8255 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19149482362612482048
theorem maskCheck8255 :
    checkMaskFor missing8255 StrongPackedBucketN12A3Shard064.record8255 = true := by
  decide

def missing8256 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19257568753669373952
theorem maskCheck8256 :
    checkMaskFor missing8256 StrongPackedBucketN12A3Shard064.record8256 = true := by
  decide

def missing8257 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19401683941745229824
theorem maskCheck8257 :
    checkMaskFor missing8257 StrongPackedBucketN12A3Shard064.record8257 = true := by
  decide

def missing8258 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20266375070200365056
theorem maskCheck8258 :
    checkMaskFor missing8258 StrongPackedBucketN12A3Shard064.record8258 = true := by
  decide

def missing8259 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23184707628736446464
theorem maskCheck8259 :
    checkMaskFor missing8259 StrongPackedBucketN12A3Shard064.record8259 = true := by
  decide

def missing8260 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23256765222774374400
theorem maskCheck8260 :
    checkMaskFor missing8260 StrongPackedBucketN12A3Shard064.record8260 = true := by
  decide

def missing8261 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23292794019793338368
theorem maskCheck8261 :
    checkMaskFor missing8261 StrongPackedBucketN12A3Shard064.record8261 = true := by
  decide

def missing8262 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23400880410850230272
theorem maskCheck8262 :
    checkMaskFor missing8262 StrongPackedBucketN12A3Shard064.record8262 = true := by
  decide

def missing8263 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23436909207869194240
theorem maskCheck8263 :
    checkMaskFor missing8263 StrongPackedBucketN12A3Shard064.record8263 = true := by
  decide

def missing8264 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23508966801907122176
theorem maskCheck8264 :
    checkMaskFor missing8264 StrongPackedBucketN12A3Shard064.record8264 = true := by
  decide

def missing8265 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23689110787001942016
theorem maskCheck8265 :
    checkMaskFor missing8265 StrongPackedBucketN12A3Shard064.record8265 = true := by
  decide

def missing8266 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23725139584020905984
theorem maskCheck8266 :
    checkMaskFor missing8266 StrongPackedBucketN12A3Shard064.record8266 = true := by
  decide

def missing8267 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23797197178058833920
theorem maskCheck8267 :
    checkMaskFor missing8267 StrongPackedBucketN12A3Shard064.record8267 = true := by
  decide

def missing8268 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27796393647163834368
theorem maskCheck8268 :
    checkMaskFor missing8268 StrongPackedBucketN12A3Shard064.record8268 = true := by
  decide

def missing8269 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27904480038220726272
theorem maskCheck8269 :
    checkMaskFor missing8269 StrongPackedBucketN12A3Shard064.record8269 = true := by
  decide

def missing8270 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28048595226296582144
theorem maskCheck8270 :
    checkMaskFor missing8270 StrongPackedBucketN12A3Shard064.record8270 = true := by
  decide

def missing8271 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28336825602448293888
theorem maskCheck8271 :
    checkMaskFor missing8271 StrongPackedBucketN12A3Shard064.record8271 = true := by
  decide

def missing8272 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32372050868572258304
theorem maskCheck8272 :
    checkMaskFor missing8272 StrongPackedBucketN12A3Shard064.record8272 = true := by
  decide

def missing8273 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37163880872094466048
theorem maskCheck8273 :
    checkMaskFor missing8273 StrongPackedBucketN12A3Shard064.record8273 = true := by
  decide

def missing8274 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37307996060170321920
theorem maskCheck8274 :
    checkMaskFor missing8274 StrongPackedBucketN12A3Shard064.record8274 = true := by
  decide

def missing8275 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37380053654208249856
theorem maskCheck8275 :
    checkMaskFor missing8275 StrongPackedBucketN12A3Shard064.record8275 = true := by
  decide

def missing8276 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37416082451227213824
theorem maskCheck8276 :
    checkMaskFor missing8276 StrongPackedBucketN12A3Shard064.record8276 = true := by
  decide

def missing8277 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37596226436322033664
theorem maskCheck8277 :
    checkMaskFor missing8277 StrongPackedBucketN12A3Shard064.record8277 = true := by
  decide

def missing8278 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37668284030359961600
theorem maskCheck8278 :
    checkMaskFor missing8278 StrongPackedBucketN12A3Shard064.record8278 = true := by
  decide

def missing8279 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37704312827378925568
theorem maskCheck8279 :
    checkMaskFor missing8279 StrongPackedBucketN12A3Shard064.record8279 = true := by
  decide

def missing8280 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37812399218435817472
theorem maskCheck8280 :
    checkMaskFor missing8280 StrongPackedBucketN12A3Shard064.record8280 = true := by
  decide

def missing8281 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37848428015454781440
theorem maskCheck8281 :
    checkMaskFor missing8281 StrongPackedBucketN12A3Shard064.record8281 = true := by
  decide

def missing8282 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41631451702445998080
theorem maskCheck8282 :
    checkMaskFor missing8282 StrongPackedBucketN12A3Shard064.record8282 = true := by
  decide

def missing8283 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41703509296483926016
theorem maskCheck8283 :
    checkMaskFor missing8283 StrongPackedBucketN12A3Shard064.record8283 = true := by
  decide

def missing8284 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41739538093502889984
theorem maskCheck8284 :
    checkMaskFor missing8284 StrongPackedBucketN12A3Shard064.record8284 = true := by
  decide

def missing8285 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41847624484559781888
theorem maskCheck8285 :
    checkMaskFor missing8285 StrongPackedBucketN12A3Shard064.record8285 = true := by
  decide

def missing8286 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41883653281578745856
theorem maskCheck8286 :
    checkMaskFor missing8286 StrongPackedBucketN12A3Shard064.record8286 = true := by
  decide

def missing8287 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41955710875616673792
theorem maskCheck8287 :
    checkMaskFor missing8287 StrongPackedBucketN12A3Shard064.record8287 = true := by
  decide

def missing8288 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42135854860711493632
theorem maskCheck8288 :
    checkMaskFor missing8288 StrongPackedBucketN12A3Shard064.record8288 = true := by
  decide

def missing8289 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42171883657730457600
theorem maskCheck8289 :
    checkMaskFor missing8289 StrongPackedBucketN12A3Shard064.record8289 = true := by
  decide

def missing8290 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42243941251768385536
theorem maskCheck8290 :
    checkMaskFor missing8290 StrongPackedBucketN12A3Shard064.record8290 = true := by
  decide

def missing8291 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42388056439844241408
theorem maskCheck8291 :
    checkMaskFor missing8291 StrongPackedBucketN12A3Shard064.record8291 = true := by
  decide

def missing8292 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46243137720873385984
theorem maskCheck8292 :
    checkMaskFor missing8292 StrongPackedBucketN12A3Shard064.record8292 = true := by
  decide

def missing8293 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46351224111930277888
theorem maskCheck8293 :
    checkMaskFor missing8293 StrongPackedBucketN12A3Shard064.record8293 = true := by
  decide

def missing8294 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46495339300006133760
theorem maskCheck8294 :
    checkMaskFor missing8294 StrongPackedBucketN12A3Shard064.record8294 = true := by
  decide

def missing8295 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46783569676157845504
theorem maskCheck8295 :
    checkMaskFor missing8295 StrongPackedBucketN12A3Shard064.record8295 = true := by
  decide

def missing8296 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50818794942281809920
theorem maskCheck8296 :
    checkMaskFor missing8296 StrongPackedBucketN12A3Shard064.record8296 = true := by
  decide

def missing8297 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55466509757728161792
theorem maskCheck8297 :
    checkMaskFor missing8297 StrongPackedBucketN12A3Shard064.record8297 = true := by
  decide

def missing8298 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55538567351766089728
theorem maskCheck8298 :
    checkMaskFor missing8298 StrongPackedBucketN12A3Shard064.record8298 = true := by
  decide

def missing8299 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55574596148785053696
theorem maskCheck8299 :
    checkMaskFor missing8299 StrongPackedBucketN12A3Shard064.record8299 = true := by
  decide

def missing8300 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55682682539841945600
theorem maskCheck8300 :
    checkMaskFor missing8300 StrongPackedBucketN12A3Shard064.record8300 = true := by
  decide

def missing8301 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55718711336860909568
theorem maskCheck8301 :
    checkMaskFor missing8301 StrongPackedBucketN12A3Shard064.record8301 = true := by
  decide

def missing8302 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55970912915993657344
theorem maskCheck8302 :
    checkMaskFor missing8302 StrongPackedBucketN12A3Shard064.record8302 = true := by
  decide

def missing8303 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56006941713012621312
theorem maskCheck8303 :
    checkMaskFor missing8303 StrongPackedBucketN12A3Shard064.record8303 = true := by
  decide

def missing8304 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60006138182117621760
theorem maskCheck8304 :
    checkMaskFor missing8304 StrongPackedBucketN12A3Shard064.record8304 = true := by
  decide

def missing8305 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60042166979136585728
theorem maskCheck8305 :
    checkMaskFor missing8305 StrongPackedBucketN12A3Shard064.record8305 = true := by
  decide

def missing8306 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60114224573174513664
theorem maskCheck8306 :
    checkMaskFor missing8306 StrongPackedBucketN12A3Shard064.record8306 = true := by
  decide

def missing8307 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60258339761250369536
theorem maskCheck8307 :
    checkMaskFor missing8307 StrongPackedBucketN12A3Shard064.record8307 = true := by
  decide

def missing8308 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60546570137402081280
theorem maskCheck8308 :
    checkMaskFor missing8308 StrongPackedBucketN12A3Shard064.record8308 = true := by
  decide

def missing8309 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64653852997563973632
theorem maskCheck8309 :
    checkMaskFor missing8309 StrongPackedBucketN12A3Shard064.record8309 = true := by
  decide

def missing8310 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 558869391431696384
theorem maskCheck8310 :
    checkMaskFor missing8310 StrongPackedBucketN12A3Shard064.record8310 = true := by
  decide

def missing8311 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 847099767583408128
theorem maskCheck8311 :
    checkMaskFor missing8311 StrongPackedBucketN12A3Shard064.record8311 = true := by
  decide

def missing8312 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1063272549697191936
theorem maskCheck8312 :
    checkMaskFor missing8312 StrongPackedBucketN12A3Shard064.record8312 = true := by
  decide

def missing8313 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1855906084114399232
theorem maskCheck8313 :
    checkMaskFor missing8313 StrongPackedBucketN12A3Shard064.record8313 = true := by
  decide

def missing8314 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1927963678152327168
theorem maskCheck8314 :
    checkMaskFor missing8314 StrongPackedBucketN12A3Shard064.record8314 = true := by
  decide

def missing8315 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2180165257285074944
theorem maskCheck8315 :
    checkMaskFor missing8315 StrongPackedBucketN12A3Shard064.record8315 = true := by
  decide

def missing8316 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4089691499290165248
theorem maskCheck8316 :
    checkMaskFor missing8316 StrongPackedBucketN12A3Shard064.record8316 = true := by
  decide

def missing8317 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4197777890347057152
theorem maskCheck8317 :
    checkMaskFor missing8317 StrongPackedBucketN12A3Shard064.record8317 = true := by
  decide

def missing8318 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4882325033707372544
theorem maskCheck8318 :
    checkMaskFor missing8318 StrongPackedBucketN12A3Shard064.record8318 = true := by
  decide

def missing8319 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5098497815821156352
theorem maskCheck8319 :
    checkMaskFor missing8319 StrongPackedBucketN12A3Shard064.record8319 = true := by
  decide

def missing8192_8193 : List (BitVec (edgeCount 12)) :=
  [missing8192]
abbrev records8192_8193 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8192]
theorem aligned8192_8193 :
    AlignedValid 12 3 missing8192_8193 records8192_8193 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8192
    maskCheck8192 AlignedValid.nil

def missing8193_8194 : List (BitVec (edgeCount 12)) :=
  [missing8193]
abbrev records8193_8194 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8193]
theorem aligned8193_8194 :
    AlignedValid 12 3 missing8193_8194 records8193_8194 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8193
    maskCheck8193 AlignedValid.nil

def missing8192_8194 : List (BitVec (edgeCount 12)) :=
  missing8192_8193 ++ missing8193_8194
abbrev records8192_8194 : List Blob :=
  records8192_8193 ++ records8193_8194
theorem aligned8192_8194 :
    AlignedValid 12 3 missing8192_8194 records8192_8194 :=
  aligned8192_8193.append aligned8193_8194

def missing8194_8195 : List (BitVec (edgeCount 12)) :=
  [missing8194]
abbrev records8194_8195 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8194]
theorem aligned8194_8195 :
    AlignedValid 12 3 missing8194_8195 records8194_8195 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8194
    maskCheck8194 AlignedValid.nil

def missing8195_8196 : List (BitVec (edgeCount 12)) :=
  [missing8195]
abbrev records8195_8196 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8195]
theorem aligned8195_8196 :
    AlignedValid 12 3 missing8195_8196 records8195_8196 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8195
    maskCheck8195 AlignedValid.nil

def missing8194_8196 : List (BitVec (edgeCount 12)) :=
  missing8194_8195 ++ missing8195_8196
abbrev records8194_8196 : List Blob :=
  records8194_8195 ++ records8195_8196
theorem aligned8194_8196 :
    AlignedValid 12 3 missing8194_8196 records8194_8196 :=
  aligned8194_8195.append aligned8195_8196

def missing8192_8196 : List (BitVec (edgeCount 12)) :=
  missing8192_8194 ++ missing8194_8196
abbrev records8192_8196 : List Blob :=
  records8192_8194 ++ records8194_8196
theorem aligned8192_8196 :
    AlignedValid 12 3 missing8192_8196 records8192_8196 :=
  aligned8192_8194.append aligned8194_8196

def missing8196_8197 : List (BitVec (edgeCount 12)) :=
  [missing8196]
abbrev records8196_8197 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8196]
theorem aligned8196_8197 :
    AlignedValid 12 3 missing8196_8197 records8196_8197 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8196
    maskCheck8196 AlignedValid.nil

def missing8197_8198 : List (BitVec (edgeCount 12)) :=
  [missing8197]
abbrev records8197_8198 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8197]
theorem aligned8197_8198 :
    AlignedValid 12 3 missing8197_8198 records8197_8198 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8197
    maskCheck8197 AlignedValid.nil

def missing8196_8198 : List (BitVec (edgeCount 12)) :=
  missing8196_8197 ++ missing8197_8198
abbrev records8196_8198 : List Blob :=
  records8196_8197 ++ records8197_8198
theorem aligned8196_8198 :
    AlignedValid 12 3 missing8196_8198 records8196_8198 :=
  aligned8196_8197.append aligned8197_8198

def missing8198_8199 : List (BitVec (edgeCount 12)) :=
  [missing8198]
abbrev records8198_8199 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8198]
theorem aligned8198_8199 :
    AlignedValid 12 3 missing8198_8199 records8198_8199 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8198
    maskCheck8198 AlignedValid.nil

def missing8199_8200 : List (BitVec (edgeCount 12)) :=
  [missing8199]
abbrev records8199_8200 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8199]
theorem aligned8199_8200 :
    AlignedValid 12 3 missing8199_8200 records8199_8200 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8199
    maskCheck8199 AlignedValid.nil

def missing8198_8200 : List (BitVec (edgeCount 12)) :=
  missing8198_8199 ++ missing8199_8200
abbrev records8198_8200 : List Blob :=
  records8198_8199 ++ records8199_8200
theorem aligned8198_8200 :
    AlignedValid 12 3 missing8198_8200 records8198_8200 :=
  aligned8198_8199.append aligned8199_8200

def missing8196_8200 : List (BitVec (edgeCount 12)) :=
  missing8196_8198 ++ missing8198_8200
abbrev records8196_8200 : List Blob :=
  records8196_8198 ++ records8198_8200
theorem aligned8196_8200 :
    AlignedValid 12 3 missing8196_8200 records8196_8200 :=
  aligned8196_8198.append aligned8198_8200

def missing8192_8200 : List (BitVec (edgeCount 12)) :=
  missing8192_8196 ++ missing8196_8200
abbrev records8192_8200 : List Blob :=
  records8192_8196 ++ records8196_8200
theorem aligned8192_8200 :
    AlignedValid 12 3 missing8192_8200 records8192_8200 :=
  aligned8192_8196.append aligned8196_8200

def missing8200_8201 : List (BitVec (edgeCount 12)) :=
  [missing8200]
abbrev records8200_8201 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8200]
theorem aligned8200_8201 :
    AlignedValid 12 3 missing8200_8201 records8200_8201 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8200
    maskCheck8200 AlignedValid.nil

def missing8201_8202 : List (BitVec (edgeCount 12)) :=
  [missing8201]
abbrev records8201_8202 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8201]
theorem aligned8201_8202 :
    AlignedValid 12 3 missing8201_8202 records8201_8202 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8201
    maskCheck8201 AlignedValid.nil

def missing8200_8202 : List (BitVec (edgeCount 12)) :=
  missing8200_8201 ++ missing8201_8202
abbrev records8200_8202 : List Blob :=
  records8200_8201 ++ records8201_8202
theorem aligned8200_8202 :
    AlignedValid 12 3 missing8200_8202 records8200_8202 :=
  aligned8200_8201.append aligned8201_8202

def missing8202_8203 : List (BitVec (edgeCount 12)) :=
  [missing8202]
abbrev records8202_8203 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8202]
theorem aligned8202_8203 :
    AlignedValid 12 3 missing8202_8203 records8202_8203 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8202
    maskCheck8202 AlignedValid.nil

def missing8203_8204 : List (BitVec (edgeCount 12)) :=
  [missing8203]
abbrev records8203_8204 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8203]
theorem aligned8203_8204 :
    AlignedValid 12 3 missing8203_8204 records8203_8204 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8203
    maskCheck8203 AlignedValid.nil

def missing8202_8204 : List (BitVec (edgeCount 12)) :=
  missing8202_8203 ++ missing8203_8204
abbrev records8202_8204 : List Blob :=
  records8202_8203 ++ records8203_8204
theorem aligned8202_8204 :
    AlignedValid 12 3 missing8202_8204 records8202_8204 :=
  aligned8202_8203.append aligned8203_8204

def missing8200_8204 : List (BitVec (edgeCount 12)) :=
  missing8200_8202 ++ missing8202_8204
abbrev records8200_8204 : List Blob :=
  records8200_8202 ++ records8202_8204
theorem aligned8200_8204 :
    AlignedValid 12 3 missing8200_8204 records8200_8204 :=
  aligned8200_8202.append aligned8202_8204

def missing8204_8205 : List (BitVec (edgeCount 12)) :=
  [missing8204]
abbrev records8204_8205 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8204]
theorem aligned8204_8205 :
    AlignedValid 12 3 missing8204_8205 records8204_8205 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8204
    maskCheck8204 AlignedValid.nil

def missing8205_8206 : List (BitVec (edgeCount 12)) :=
  [missing8205]
abbrev records8205_8206 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8205]
theorem aligned8205_8206 :
    AlignedValid 12 3 missing8205_8206 records8205_8206 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8205
    maskCheck8205 AlignedValid.nil

def missing8204_8206 : List (BitVec (edgeCount 12)) :=
  missing8204_8205 ++ missing8205_8206
abbrev records8204_8206 : List Blob :=
  records8204_8205 ++ records8205_8206
theorem aligned8204_8206 :
    AlignedValid 12 3 missing8204_8206 records8204_8206 :=
  aligned8204_8205.append aligned8205_8206

def missing8206_8207 : List (BitVec (edgeCount 12)) :=
  [missing8206]
abbrev records8206_8207 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8206]
theorem aligned8206_8207 :
    AlignedValid 12 3 missing8206_8207 records8206_8207 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8206
    maskCheck8206 AlignedValid.nil

def missing8207_8208 : List (BitVec (edgeCount 12)) :=
  [missing8207]
abbrev records8207_8208 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8207]
theorem aligned8207_8208 :
    AlignedValid 12 3 missing8207_8208 records8207_8208 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8207
    maskCheck8207 AlignedValid.nil

def missing8206_8208 : List (BitVec (edgeCount 12)) :=
  missing8206_8207 ++ missing8207_8208
abbrev records8206_8208 : List Blob :=
  records8206_8207 ++ records8207_8208
theorem aligned8206_8208 :
    AlignedValid 12 3 missing8206_8208 records8206_8208 :=
  aligned8206_8207.append aligned8207_8208

def missing8204_8208 : List (BitVec (edgeCount 12)) :=
  missing8204_8206 ++ missing8206_8208
abbrev records8204_8208 : List Blob :=
  records8204_8206 ++ records8206_8208
theorem aligned8204_8208 :
    AlignedValid 12 3 missing8204_8208 records8204_8208 :=
  aligned8204_8206.append aligned8206_8208

def missing8200_8208 : List (BitVec (edgeCount 12)) :=
  missing8200_8204 ++ missing8204_8208
abbrev records8200_8208 : List Blob :=
  records8200_8204 ++ records8204_8208
theorem aligned8200_8208 :
    AlignedValid 12 3 missing8200_8208 records8200_8208 :=
  aligned8200_8204.append aligned8204_8208

def missing8192_8208 : List (BitVec (edgeCount 12)) :=
  missing8192_8200 ++ missing8200_8208
abbrev records8192_8208 : List Blob :=
  records8192_8200 ++ records8200_8208
theorem aligned8192_8208 :
    AlignedValid 12 3 missing8192_8208 records8192_8208 :=
  aligned8192_8200.append aligned8200_8208

def missing8208_8209 : List (BitVec (edgeCount 12)) :=
  [missing8208]
abbrev records8208_8209 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8208]
theorem aligned8208_8209 :
    AlignedValid 12 3 missing8208_8209 records8208_8209 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8208
    maskCheck8208 AlignedValid.nil

def missing8209_8210 : List (BitVec (edgeCount 12)) :=
  [missing8209]
abbrev records8209_8210 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8209]
theorem aligned8209_8210 :
    AlignedValid 12 3 missing8209_8210 records8209_8210 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8209
    maskCheck8209 AlignedValid.nil

def missing8208_8210 : List (BitVec (edgeCount 12)) :=
  missing8208_8209 ++ missing8209_8210
abbrev records8208_8210 : List Blob :=
  records8208_8209 ++ records8209_8210
theorem aligned8208_8210 :
    AlignedValid 12 3 missing8208_8210 records8208_8210 :=
  aligned8208_8209.append aligned8209_8210

def missing8210_8211 : List (BitVec (edgeCount 12)) :=
  [missing8210]
abbrev records8210_8211 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8210]
theorem aligned8210_8211 :
    AlignedValid 12 3 missing8210_8211 records8210_8211 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8210
    maskCheck8210 AlignedValid.nil

def missing8211_8212 : List (BitVec (edgeCount 12)) :=
  [missing8211]
abbrev records8211_8212 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8211]
theorem aligned8211_8212 :
    AlignedValid 12 3 missing8211_8212 records8211_8212 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8211
    maskCheck8211 AlignedValid.nil

def missing8210_8212 : List (BitVec (edgeCount 12)) :=
  missing8210_8211 ++ missing8211_8212
abbrev records8210_8212 : List Blob :=
  records8210_8211 ++ records8211_8212
theorem aligned8210_8212 :
    AlignedValid 12 3 missing8210_8212 records8210_8212 :=
  aligned8210_8211.append aligned8211_8212

def missing8208_8212 : List (BitVec (edgeCount 12)) :=
  missing8208_8210 ++ missing8210_8212
abbrev records8208_8212 : List Blob :=
  records8208_8210 ++ records8210_8212
theorem aligned8208_8212 :
    AlignedValid 12 3 missing8208_8212 records8208_8212 :=
  aligned8208_8210.append aligned8210_8212

def missing8212_8213 : List (BitVec (edgeCount 12)) :=
  [missing8212]
abbrev records8212_8213 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8212]
theorem aligned8212_8213 :
    AlignedValid 12 3 missing8212_8213 records8212_8213 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8212
    maskCheck8212 AlignedValid.nil

def missing8213_8214 : List (BitVec (edgeCount 12)) :=
  [missing8213]
abbrev records8213_8214 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8213]
theorem aligned8213_8214 :
    AlignedValid 12 3 missing8213_8214 records8213_8214 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8213
    maskCheck8213 AlignedValid.nil

def missing8212_8214 : List (BitVec (edgeCount 12)) :=
  missing8212_8213 ++ missing8213_8214
abbrev records8212_8214 : List Blob :=
  records8212_8213 ++ records8213_8214
theorem aligned8212_8214 :
    AlignedValid 12 3 missing8212_8214 records8212_8214 :=
  aligned8212_8213.append aligned8213_8214

def missing8214_8215 : List (BitVec (edgeCount 12)) :=
  [missing8214]
abbrev records8214_8215 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8214]
theorem aligned8214_8215 :
    AlignedValid 12 3 missing8214_8215 records8214_8215 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8214
    maskCheck8214 AlignedValid.nil

def missing8215_8216 : List (BitVec (edgeCount 12)) :=
  [missing8215]
abbrev records8215_8216 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8215]
theorem aligned8215_8216 :
    AlignedValid 12 3 missing8215_8216 records8215_8216 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8215
    maskCheck8215 AlignedValid.nil

def missing8214_8216 : List (BitVec (edgeCount 12)) :=
  missing8214_8215 ++ missing8215_8216
abbrev records8214_8216 : List Blob :=
  records8214_8215 ++ records8215_8216
theorem aligned8214_8216 :
    AlignedValid 12 3 missing8214_8216 records8214_8216 :=
  aligned8214_8215.append aligned8215_8216

def missing8212_8216 : List (BitVec (edgeCount 12)) :=
  missing8212_8214 ++ missing8214_8216
abbrev records8212_8216 : List Blob :=
  records8212_8214 ++ records8214_8216
theorem aligned8212_8216 :
    AlignedValid 12 3 missing8212_8216 records8212_8216 :=
  aligned8212_8214.append aligned8214_8216

def missing8208_8216 : List (BitVec (edgeCount 12)) :=
  missing8208_8212 ++ missing8212_8216
abbrev records8208_8216 : List Blob :=
  records8208_8212 ++ records8212_8216
theorem aligned8208_8216 :
    AlignedValid 12 3 missing8208_8216 records8208_8216 :=
  aligned8208_8212.append aligned8212_8216

def missing8216_8217 : List (BitVec (edgeCount 12)) :=
  [missing8216]
abbrev records8216_8217 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8216]
theorem aligned8216_8217 :
    AlignedValid 12 3 missing8216_8217 records8216_8217 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8216
    maskCheck8216 AlignedValid.nil

def missing8217_8218 : List (BitVec (edgeCount 12)) :=
  [missing8217]
abbrev records8217_8218 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8217]
theorem aligned8217_8218 :
    AlignedValid 12 3 missing8217_8218 records8217_8218 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8217
    maskCheck8217 AlignedValid.nil

def missing8216_8218 : List (BitVec (edgeCount 12)) :=
  missing8216_8217 ++ missing8217_8218
abbrev records8216_8218 : List Blob :=
  records8216_8217 ++ records8217_8218
theorem aligned8216_8218 :
    AlignedValid 12 3 missing8216_8218 records8216_8218 :=
  aligned8216_8217.append aligned8217_8218

def missing8218_8219 : List (BitVec (edgeCount 12)) :=
  [missing8218]
abbrev records8218_8219 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8218]
theorem aligned8218_8219 :
    AlignedValid 12 3 missing8218_8219 records8218_8219 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8218
    maskCheck8218 AlignedValid.nil

def missing8219_8220 : List (BitVec (edgeCount 12)) :=
  [missing8219]
abbrev records8219_8220 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8219]
theorem aligned8219_8220 :
    AlignedValid 12 3 missing8219_8220 records8219_8220 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8219
    maskCheck8219 AlignedValid.nil

def missing8218_8220 : List (BitVec (edgeCount 12)) :=
  missing8218_8219 ++ missing8219_8220
abbrev records8218_8220 : List Blob :=
  records8218_8219 ++ records8219_8220
theorem aligned8218_8220 :
    AlignedValid 12 3 missing8218_8220 records8218_8220 :=
  aligned8218_8219.append aligned8219_8220

def missing8216_8220 : List (BitVec (edgeCount 12)) :=
  missing8216_8218 ++ missing8218_8220
abbrev records8216_8220 : List Blob :=
  records8216_8218 ++ records8218_8220
theorem aligned8216_8220 :
    AlignedValid 12 3 missing8216_8220 records8216_8220 :=
  aligned8216_8218.append aligned8218_8220

def missing8220_8221 : List (BitVec (edgeCount 12)) :=
  [missing8220]
abbrev records8220_8221 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8220]
theorem aligned8220_8221 :
    AlignedValid 12 3 missing8220_8221 records8220_8221 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8220
    maskCheck8220 AlignedValid.nil

def missing8221_8222 : List (BitVec (edgeCount 12)) :=
  [missing8221]
abbrev records8221_8222 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8221]
theorem aligned8221_8222 :
    AlignedValid 12 3 missing8221_8222 records8221_8222 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8221
    maskCheck8221 AlignedValid.nil

def missing8220_8222 : List (BitVec (edgeCount 12)) :=
  missing8220_8221 ++ missing8221_8222
abbrev records8220_8222 : List Blob :=
  records8220_8221 ++ records8221_8222
theorem aligned8220_8222 :
    AlignedValid 12 3 missing8220_8222 records8220_8222 :=
  aligned8220_8221.append aligned8221_8222

def missing8222_8223 : List (BitVec (edgeCount 12)) :=
  [missing8222]
abbrev records8222_8223 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8222]
theorem aligned8222_8223 :
    AlignedValid 12 3 missing8222_8223 records8222_8223 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8222
    maskCheck8222 AlignedValid.nil

def missing8223_8224 : List (BitVec (edgeCount 12)) :=
  [missing8223]
abbrev records8223_8224 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8223]
theorem aligned8223_8224 :
    AlignedValid 12 3 missing8223_8224 records8223_8224 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8223
    maskCheck8223 AlignedValid.nil

def missing8222_8224 : List (BitVec (edgeCount 12)) :=
  missing8222_8223 ++ missing8223_8224
abbrev records8222_8224 : List Blob :=
  records8222_8223 ++ records8223_8224
theorem aligned8222_8224 :
    AlignedValid 12 3 missing8222_8224 records8222_8224 :=
  aligned8222_8223.append aligned8223_8224

def missing8220_8224 : List (BitVec (edgeCount 12)) :=
  missing8220_8222 ++ missing8222_8224
abbrev records8220_8224 : List Blob :=
  records8220_8222 ++ records8222_8224
theorem aligned8220_8224 :
    AlignedValid 12 3 missing8220_8224 records8220_8224 :=
  aligned8220_8222.append aligned8222_8224

def missing8216_8224 : List (BitVec (edgeCount 12)) :=
  missing8216_8220 ++ missing8220_8224
abbrev records8216_8224 : List Blob :=
  records8216_8220 ++ records8220_8224
theorem aligned8216_8224 :
    AlignedValid 12 3 missing8216_8224 records8216_8224 :=
  aligned8216_8220.append aligned8220_8224

def missing8208_8224 : List (BitVec (edgeCount 12)) :=
  missing8208_8216 ++ missing8216_8224
abbrev records8208_8224 : List Blob :=
  records8208_8216 ++ records8216_8224
theorem aligned8208_8224 :
    AlignedValid 12 3 missing8208_8224 records8208_8224 :=
  aligned8208_8216.append aligned8216_8224

def missing8192_8224 : List (BitVec (edgeCount 12)) :=
  missing8192_8208 ++ missing8208_8224
abbrev records8192_8224 : List Blob :=
  records8192_8208 ++ records8208_8224
theorem aligned8192_8224 :
    AlignedValid 12 3 missing8192_8224 records8192_8224 :=
  aligned8192_8208.append aligned8208_8224

def missing8224_8225 : List (BitVec (edgeCount 12)) :=
  [missing8224]
abbrev records8224_8225 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8224]
theorem aligned8224_8225 :
    AlignedValid 12 3 missing8224_8225 records8224_8225 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8224
    maskCheck8224 AlignedValid.nil

def missing8225_8226 : List (BitVec (edgeCount 12)) :=
  [missing8225]
abbrev records8225_8226 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8225]
theorem aligned8225_8226 :
    AlignedValid 12 3 missing8225_8226 records8225_8226 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8225
    maskCheck8225 AlignedValid.nil

def missing8224_8226 : List (BitVec (edgeCount 12)) :=
  missing8224_8225 ++ missing8225_8226
abbrev records8224_8226 : List Blob :=
  records8224_8225 ++ records8225_8226
theorem aligned8224_8226 :
    AlignedValid 12 3 missing8224_8226 records8224_8226 :=
  aligned8224_8225.append aligned8225_8226

def missing8226_8227 : List (BitVec (edgeCount 12)) :=
  [missing8226]
abbrev records8226_8227 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8226]
theorem aligned8226_8227 :
    AlignedValid 12 3 missing8226_8227 records8226_8227 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8226
    maskCheck8226 AlignedValid.nil

def missing8227_8228 : List (BitVec (edgeCount 12)) :=
  [missing8227]
abbrev records8227_8228 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8227]
theorem aligned8227_8228 :
    AlignedValid 12 3 missing8227_8228 records8227_8228 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8227
    maskCheck8227 AlignedValid.nil

def missing8226_8228 : List (BitVec (edgeCount 12)) :=
  missing8226_8227 ++ missing8227_8228
abbrev records8226_8228 : List Blob :=
  records8226_8227 ++ records8227_8228
theorem aligned8226_8228 :
    AlignedValid 12 3 missing8226_8228 records8226_8228 :=
  aligned8226_8227.append aligned8227_8228

def missing8224_8228 : List (BitVec (edgeCount 12)) :=
  missing8224_8226 ++ missing8226_8228
abbrev records8224_8228 : List Blob :=
  records8224_8226 ++ records8226_8228
theorem aligned8224_8228 :
    AlignedValid 12 3 missing8224_8228 records8224_8228 :=
  aligned8224_8226.append aligned8226_8228

def missing8228_8229 : List (BitVec (edgeCount 12)) :=
  [missing8228]
abbrev records8228_8229 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8228]
theorem aligned8228_8229 :
    AlignedValid 12 3 missing8228_8229 records8228_8229 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8228
    maskCheck8228 AlignedValid.nil

def missing8229_8230 : List (BitVec (edgeCount 12)) :=
  [missing8229]
abbrev records8229_8230 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8229]
theorem aligned8229_8230 :
    AlignedValid 12 3 missing8229_8230 records8229_8230 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8229
    maskCheck8229 AlignedValid.nil

def missing8228_8230 : List (BitVec (edgeCount 12)) :=
  missing8228_8229 ++ missing8229_8230
abbrev records8228_8230 : List Blob :=
  records8228_8229 ++ records8229_8230
theorem aligned8228_8230 :
    AlignedValid 12 3 missing8228_8230 records8228_8230 :=
  aligned8228_8229.append aligned8229_8230

def missing8230_8231 : List (BitVec (edgeCount 12)) :=
  [missing8230]
abbrev records8230_8231 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8230]
theorem aligned8230_8231 :
    AlignedValid 12 3 missing8230_8231 records8230_8231 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8230
    maskCheck8230 AlignedValid.nil

def missing8231_8232 : List (BitVec (edgeCount 12)) :=
  [missing8231]
abbrev records8231_8232 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8231]
theorem aligned8231_8232 :
    AlignedValid 12 3 missing8231_8232 records8231_8232 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8231
    maskCheck8231 AlignedValid.nil

def missing8230_8232 : List (BitVec (edgeCount 12)) :=
  missing8230_8231 ++ missing8231_8232
abbrev records8230_8232 : List Blob :=
  records8230_8231 ++ records8231_8232
theorem aligned8230_8232 :
    AlignedValid 12 3 missing8230_8232 records8230_8232 :=
  aligned8230_8231.append aligned8231_8232

def missing8228_8232 : List (BitVec (edgeCount 12)) :=
  missing8228_8230 ++ missing8230_8232
abbrev records8228_8232 : List Blob :=
  records8228_8230 ++ records8230_8232
theorem aligned8228_8232 :
    AlignedValid 12 3 missing8228_8232 records8228_8232 :=
  aligned8228_8230.append aligned8230_8232

def missing8224_8232 : List (BitVec (edgeCount 12)) :=
  missing8224_8228 ++ missing8228_8232
abbrev records8224_8232 : List Blob :=
  records8224_8228 ++ records8228_8232
theorem aligned8224_8232 :
    AlignedValid 12 3 missing8224_8232 records8224_8232 :=
  aligned8224_8228.append aligned8228_8232

def missing8232_8233 : List (BitVec (edgeCount 12)) :=
  [missing8232]
abbrev records8232_8233 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8232]
theorem aligned8232_8233 :
    AlignedValid 12 3 missing8232_8233 records8232_8233 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8232
    maskCheck8232 AlignedValid.nil

def missing8233_8234 : List (BitVec (edgeCount 12)) :=
  [missing8233]
abbrev records8233_8234 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8233]
theorem aligned8233_8234 :
    AlignedValid 12 3 missing8233_8234 records8233_8234 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8233
    maskCheck8233 AlignedValid.nil

def missing8232_8234 : List (BitVec (edgeCount 12)) :=
  missing8232_8233 ++ missing8233_8234
abbrev records8232_8234 : List Blob :=
  records8232_8233 ++ records8233_8234
theorem aligned8232_8234 :
    AlignedValid 12 3 missing8232_8234 records8232_8234 :=
  aligned8232_8233.append aligned8233_8234

def missing8234_8235 : List (BitVec (edgeCount 12)) :=
  [missing8234]
abbrev records8234_8235 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8234]
theorem aligned8234_8235 :
    AlignedValid 12 3 missing8234_8235 records8234_8235 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8234
    maskCheck8234 AlignedValid.nil

def missing8235_8236 : List (BitVec (edgeCount 12)) :=
  [missing8235]
abbrev records8235_8236 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8235]
theorem aligned8235_8236 :
    AlignedValid 12 3 missing8235_8236 records8235_8236 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8235
    maskCheck8235 AlignedValid.nil

def missing8234_8236 : List (BitVec (edgeCount 12)) :=
  missing8234_8235 ++ missing8235_8236
abbrev records8234_8236 : List Blob :=
  records8234_8235 ++ records8235_8236
theorem aligned8234_8236 :
    AlignedValid 12 3 missing8234_8236 records8234_8236 :=
  aligned8234_8235.append aligned8235_8236

def missing8232_8236 : List (BitVec (edgeCount 12)) :=
  missing8232_8234 ++ missing8234_8236
abbrev records8232_8236 : List Blob :=
  records8232_8234 ++ records8234_8236
theorem aligned8232_8236 :
    AlignedValid 12 3 missing8232_8236 records8232_8236 :=
  aligned8232_8234.append aligned8234_8236

def missing8236_8237 : List (BitVec (edgeCount 12)) :=
  [missing8236]
abbrev records8236_8237 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8236]
theorem aligned8236_8237 :
    AlignedValid 12 3 missing8236_8237 records8236_8237 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8236
    maskCheck8236 AlignedValid.nil

def missing8237_8238 : List (BitVec (edgeCount 12)) :=
  [missing8237]
abbrev records8237_8238 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8237]
theorem aligned8237_8238 :
    AlignedValid 12 3 missing8237_8238 records8237_8238 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8237
    maskCheck8237 AlignedValid.nil

def missing8236_8238 : List (BitVec (edgeCount 12)) :=
  missing8236_8237 ++ missing8237_8238
abbrev records8236_8238 : List Blob :=
  records8236_8237 ++ records8237_8238
theorem aligned8236_8238 :
    AlignedValid 12 3 missing8236_8238 records8236_8238 :=
  aligned8236_8237.append aligned8237_8238

def missing8238_8239 : List (BitVec (edgeCount 12)) :=
  [missing8238]
abbrev records8238_8239 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8238]
theorem aligned8238_8239 :
    AlignedValid 12 3 missing8238_8239 records8238_8239 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8238
    maskCheck8238 AlignedValid.nil

def missing8239_8240 : List (BitVec (edgeCount 12)) :=
  [missing8239]
abbrev records8239_8240 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8239]
theorem aligned8239_8240 :
    AlignedValid 12 3 missing8239_8240 records8239_8240 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8239
    maskCheck8239 AlignedValid.nil

def missing8238_8240 : List (BitVec (edgeCount 12)) :=
  missing8238_8239 ++ missing8239_8240
abbrev records8238_8240 : List Blob :=
  records8238_8239 ++ records8239_8240
theorem aligned8238_8240 :
    AlignedValid 12 3 missing8238_8240 records8238_8240 :=
  aligned8238_8239.append aligned8239_8240

def missing8236_8240 : List (BitVec (edgeCount 12)) :=
  missing8236_8238 ++ missing8238_8240
abbrev records8236_8240 : List Blob :=
  records8236_8238 ++ records8238_8240
theorem aligned8236_8240 :
    AlignedValid 12 3 missing8236_8240 records8236_8240 :=
  aligned8236_8238.append aligned8238_8240

def missing8232_8240 : List (BitVec (edgeCount 12)) :=
  missing8232_8236 ++ missing8236_8240
abbrev records8232_8240 : List Blob :=
  records8232_8236 ++ records8236_8240
theorem aligned8232_8240 :
    AlignedValid 12 3 missing8232_8240 records8232_8240 :=
  aligned8232_8236.append aligned8236_8240

def missing8224_8240 : List (BitVec (edgeCount 12)) :=
  missing8224_8232 ++ missing8232_8240
abbrev records8224_8240 : List Blob :=
  records8224_8232 ++ records8232_8240
theorem aligned8224_8240 :
    AlignedValid 12 3 missing8224_8240 records8224_8240 :=
  aligned8224_8232.append aligned8232_8240

def missing8240_8241 : List (BitVec (edgeCount 12)) :=
  [missing8240]
abbrev records8240_8241 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8240]
theorem aligned8240_8241 :
    AlignedValid 12 3 missing8240_8241 records8240_8241 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8240
    maskCheck8240 AlignedValid.nil

def missing8241_8242 : List (BitVec (edgeCount 12)) :=
  [missing8241]
abbrev records8241_8242 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8241]
theorem aligned8241_8242 :
    AlignedValid 12 3 missing8241_8242 records8241_8242 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8241
    maskCheck8241 AlignedValid.nil

def missing8240_8242 : List (BitVec (edgeCount 12)) :=
  missing8240_8241 ++ missing8241_8242
abbrev records8240_8242 : List Blob :=
  records8240_8241 ++ records8241_8242
theorem aligned8240_8242 :
    AlignedValid 12 3 missing8240_8242 records8240_8242 :=
  aligned8240_8241.append aligned8241_8242

def missing8242_8243 : List (BitVec (edgeCount 12)) :=
  [missing8242]
abbrev records8242_8243 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8242]
theorem aligned8242_8243 :
    AlignedValid 12 3 missing8242_8243 records8242_8243 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8242
    maskCheck8242 AlignedValid.nil

def missing8243_8244 : List (BitVec (edgeCount 12)) :=
  [missing8243]
abbrev records8243_8244 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8243]
theorem aligned8243_8244 :
    AlignedValid 12 3 missing8243_8244 records8243_8244 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8243
    maskCheck8243 AlignedValid.nil

def missing8242_8244 : List (BitVec (edgeCount 12)) :=
  missing8242_8243 ++ missing8243_8244
abbrev records8242_8244 : List Blob :=
  records8242_8243 ++ records8243_8244
theorem aligned8242_8244 :
    AlignedValid 12 3 missing8242_8244 records8242_8244 :=
  aligned8242_8243.append aligned8243_8244

def missing8240_8244 : List (BitVec (edgeCount 12)) :=
  missing8240_8242 ++ missing8242_8244
abbrev records8240_8244 : List Blob :=
  records8240_8242 ++ records8242_8244
theorem aligned8240_8244 :
    AlignedValid 12 3 missing8240_8244 records8240_8244 :=
  aligned8240_8242.append aligned8242_8244

def missing8244_8245 : List (BitVec (edgeCount 12)) :=
  [missing8244]
abbrev records8244_8245 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8244]
theorem aligned8244_8245 :
    AlignedValid 12 3 missing8244_8245 records8244_8245 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8244
    maskCheck8244 AlignedValid.nil

def missing8245_8246 : List (BitVec (edgeCount 12)) :=
  [missing8245]
abbrev records8245_8246 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8245]
theorem aligned8245_8246 :
    AlignedValid 12 3 missing8245_8246 records8245_8246 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8245
    maskCheck8245 AlignedValid.nil

def missing8244_8246 : List (BitVec (edgeCount 12)) :=
  missing8244_8245 ++ missing8245_8246
abbrev records8244_8246 : List Blob :=
  records8244_8245 ++ records8245_8246
theorem aligned8244_8246 :
    AlignedValid 12 3 missing8244_8246 records8244_8246 :=
  aligned8244_8245.append aligned8245_8246

def missing8246_8247 : List (BitVec (edgeCount 12)) :=
  [missing8246]
abbrev records8246_8247 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8246]
theorem aligned8246_8247 :
    AlignedValid 12 3 missing8246_8247 records8246_8247 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8246
    maskCheck8246 AlignedValid.nil

def missing8247_8248 : List (BitVec (edgeCount 12)) :=
  [missing8247]
abbrev records8247_8248 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8247]
theorem aligned8247_8248 :
    AlignedValid 12 3 missing8247_8248 records8247_8248 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8247
    maskCheck8247 AlignedValid.nil

def missing8246_8248 : List (BitVec (edgeCount 12)) :=
  missing8246_8247 ++ missing8247_8248
abbrev records8246_8248 : List Blob :=
  records8246_8247 ++ records8247_8248
theorem aligned8246_8248 :
    AlignedValid 12 3 missing8246_8248 records8246_8248 :=
  aligned8246_8247.append aligned8247_8248

def missing8244_8248 : List (BitVec (edgeCount 12)) :=
  missing8244_8246 ++ missing8246_8248
abbrev records8244_8248 : List Blob :=
  records8244_8246 ++ records8246_8248
theorem aligned8244_8248 :
    AlignedValid 12 3 missing8244_8248 records8244_8248 :=
  aligned8244_8246.append aligned8246_8248

def missing8240_8248 : List (BitVec (edgeCount 12)) :=
  missing8240_8244 ++ missing8244_8248
abbrev records8240_8248 : List Blob :=
  records8240_8244 ++ records8244_8248
theorem aligned8240_8248 :
    AlignedValid 12 3 missing8240_8248 records8240_8248 :=
  aligned8240_8244.append aligned8244_8248

def missing8248_8249 : List (BitVec (edgeCount 12)) :=
  [missing8248]
abbrev records8248_8249 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8248]
theorem aligned8248_8249 :
    AlignedValid 12 3 missing8248_8249 records8248_8249 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8248
    maskCheck8248 AlignedValid.nil

def missing8249_8250 : List (BitVec (edgeCount 12)) :=
  [missing8249]
abbrev records8249_8250 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8249]
theorem aligned8249_8250 :
    AlignedValid 12 3 missing8249_8250 records8249_8250 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8249
    maskCheck8249 AlignedValid.nil

def missing8248_8250 : List (BitVec (edgeCount 12)) :=
  missing8248_8249 ++ missing8249_8250
abbrev records8248_8250 : List Blob :=
  records8248_8249 ++ records8249_8250
theorem aligned8248_8250 :
    AlignedValid 12 3 missing8248_8250 records8248_8250 :=
  aligned8248_8249.append aligned8249_8250

def missing8250_8251 : List (BitVec (edgeCount 12)) :=
  [missing8250]
abbrev records8250_8251 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8250]
theorem aligned8250_8251 :
    AlignedValid 12 3 missing8250_8251 records8250_8251 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8250
    maskCheck8250 AlignedValid.nil

def missing8251_8252 : List (BitVec (edgeCount 12)) :=
  [missing8251]
abbrev records8251_8252 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8251]
theorem aligned8251_8252 :
    AlignedValid 12 3 missing8251_8252 records8251_8252 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8251
    maskCheck8251 AlignedValid.nil

def missing8250_8252 : List (BitVec (edgeCount 12)) :=
  missing8250_8251 ++ missing8251_8252
abbrev records8250_8252 : List Blob :=
  records8250_8251 ++ records8251_8252
theorem aligned8250_8252 :
    AlignedValid 12 3 missing8250_8252 records8250_8252 :=
  aligned8250_8251.append aligned8251_8252

def missing8248_8252 : List (BitVec (edgeCount 12)) :=
  missing8248_8250 ++ missing8250_8252
abbrev records8248_8252 : List Blob :=
  records8248_8250 ++ records8250_8252
theorem aligned8248_8252 :
    AlignedValid 12 3 missing8248_8252 records8248_8252 :=
  aligned8248_8250.append aligned8250_8252

def missing8252_8253 : List (BitVec (edgeCount 12)) :=
  [missing8252]
abbrev records8252_8253 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8252]
theorem aligned8252_8253 :
    AlignedValid 12 3 missing8252_8253 records8252_8253 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8252
    maskCheck8252 AlignedValid.nil

def missing8253_8254 : List (BitVec (edgeCount 12)) :=
  [missing8253]
abbrev records8253_8254 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8253]
theorem aligned8253_8254 :
    AlignedValid 12 3 missing8253_8254 records8253_8254 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8253
    maskCheck8253 AlignedValid.nil

def missing8252_8254 : List (BitVec (edgeCount 12)) :=
  missing8252_8253 ++ missing8253_8254
abbrev records8252_8254 : List Blob :=
  records8252_8253 ++ records8253_8254
theorem aligned8252_8254 :
    AlignedValid 12 3 missing8252_8254 records8252_8254 :=
  aligned8252_8253.append aligned8253_8254

def missing8254_8255 : List (BitVec (edgeCount 12)) :=
  [missing8254]
abbrev records8254_8255 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8254]
theorem aligned8254_8255 :
    AlignedValid 12 3 missing8254_8255 records8254_8255 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8254
    maskCheck8254 AlignedValid.nil

def missing8255_8256 : List (BitVec (edgeCount 12)) :=
  [missing8255]
abbrev records8255_8256 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8255]
theorem aligned8255_8256 :
    AlignedValid 12 3 missing8255_8256 records8255_8256 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8255
    maskCheck8255 AlignedValid.nil

def missing8254_8256 : List (BitVec (edgeCount 12)) :=
  missing8254_8255 ++ missing8255_8256
abbrev records8254_8256 : List Blob :=
  records8254_8255 ++ records8255_8256
theorem aligned8254_8256 :
    AlignedValid 12 3 missing8254_8256 records8254_8256 :=
  aligned8254_8255.append aligned8255_8256

def missing8252_8256 : List (BitVec (edgeCount 12)) :=
  missing8252_8254 ++ missing8254_8256
abbrev records8252_8256 : List Blob :=
  records8252_8254 ++ records8254_8256
theorem aligned8252_8256 :
    AlignedValid 12 3 missing8252_8256 records8252_8256 :=
  aligned8252_8254.append aligned8254_8256

def missing8248_8256 : List (BitVec (edgeCount 12)) :=
  missing8248_8252 ++ missing8252_8256
abbrev records8248_8256 : List Blob :=
  records8248_8252 ++ records8252_8256
theorem aligned8248_8256 :
    AlignedValid 12 3 missing8248_8256 records8248_8256 :=
  aligned8248_8252.append aligned8252_8256

def missing8240_8256 : List (BitVec (edgeCount 12)) :=
  missing8240_8248 ++ missing8248_8256
abbrev records8240_8256 : List Blob :=
  records8240_8248 ++ records8248_8256
theorem aligned8240_8256 :
    AlignedValid 12 3 missing8240_8256 records8240_8256 :=
  aligned8240_8248.append aligned8248_8256

def missing8224_8256 : List (BitVec (edgeCount 12)) :=
  missing8224_8240 ++ missing8240_8256
abbrev records8224_8256 : List Blob :=
  records8224_8240 ++ records8240_8256
theorem aligned8224_8256 :
    AlignedValid 12 3 missing8224_8256 records8224_8256 :=
  aligned8224_8240.append aligned8240_8256

def missing8192_8256 : List (BitVec (edgeCount 12)) :=
  missing8192_8224 ++ missing8224_8256
abbrev records8192_8256 : List Blob :=
  records8192_8224 ++ records8224_8256
theorem aligned8192_8256 :
    AlignedValid 12 3 missing8192_8256 records8192_8256 :=
  aligned8192_8224.append aligned8224_8256

def missing8256_8257 : List (BitVec (edgeCount 12)) :=
  [missing8256]
abbrev records8256_8257 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8256]
theorem aligned8256_8257 :
    AlignedValid 12 3 missing8256_8257 records8256_8257 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8256
    maskCheck8256 AlignedValid.nil

def missing8257_8258 : List (BitVec (edgeCount 12)) :=
  [missing8257]
abbrev records8257_8258 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8257]
theorem aligned8257_8258 :
    AlignedValid 12 3 missing8257_8258 records8257_8258 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8257
    maskCheck8257 AlignedValid.nil

def missing8256_8258 : List (BitVec (edgeCount 12)) :=
  missing8256_8257 ++ missing8257_8258
abbrev records8256_8258 : List Blob :=
  records8256_8257 ++ records8257_8258
theorem aligned8256_8258 :
    AlignedValid 12 3 missing8256_8258 records8256_8258 :=
  aligned8256_8257.append aligned8257_8258

def missing8258_8259 : List (BitVec (edgeCount 12)) :=
  [missing8258]
abbrev records8258_8259 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8258]
theorem aligned8258_8259 :
    AlignedValid 12 3 missing8258_8259 records8258_8259 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8258
    maskCheck8258 AlignedValid.nil

def missing8259_8260 : List (BitVec (edgeCount 12)) :=
  [missing8259]
abbrev records8259_8260 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8259]
theorem aligned8259_8260 :
    AlignedValid 12 3 missing8259_8260 records8259_8260 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8259
    maskCheck8259 AlignedValid.nil

def missing8258_8260 : List (BitVec (edgeCount 12)) :=
  missing8258_8259 ++ missing8259_8260
abbrev records8258_8260 : List Blob :=
  records8258_8259 ++ records8259_8260
theorem aligned8258_8260 :
    AlignedValid 12 3 missing8258_8260 records8258_8260 :=
  aligned8258_8259.append aligned8259_8260

def missing8256_8260 : List (BitVec (edgeCount 12)) :=
  missing8256_8258 ++ missing8258_8260
abbrev records8256_8260 : List Blob :=
  records8256_8258 ++ records8258_8260
theorem aligned8256_8260 :
    AlignedValid 12 3 missing8256_8260 records8256_8260 :=
  aligned8256_8258.append aligned8258_8260

def missing8260_8261 : List (BitVec (edgeCount 12)) :=
  [missing8260]
abbrev records8260_8261 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8260]
theorem aligned8260_8261 :
    AlignedValid 12 3 missing8260_8261 records8260_8261 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8260
    maskCheck8260 AlignedValid.nil

def missing8261_8262 : List (BitVec (edgeCount 12)) :=
  [missing8261]
abbrev records8261_8262 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8261]
theorem aligned8261_8262 :
    AlignedValid 12 3 missing8261_8262 records8261_8262 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8261
    maskCheck8261 AlignedValid.nil

def missing8260_8262 : List (BitVec (edgeCount 12)) :=
  missing8260_8261 ++ missing8261_8262
abbrev records8260_8262 : List Blob :=
  records8260_8261 ++ records8261_8262
theorem aligned8260_8262 :
    AlignedValid 12 3 missing8260_8262 records8260_8262 :=
  aligned8260_8261.append aligned8261_8262

def missing8262_8263 : List (BitVec (edgeCount 12)) :=
  [missing8262]
abbrev records8262_8263 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8262]
theorem aligned8262_8263 :
    AlignedValid 12 3 missing8262_8263 records8262_8263 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8262
    maskCheck8262 AlignedValid.nil

def missing8263_8264 : List (BitVec (edgeCount 12)) :=
  [missing8263]
abbrev records8263_8264 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8263]
theorem aligned8263_8264 :
    AlignedValid 12 3 missing8263_8264 records8263_8264 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8263
    maskCheck8263 AlignedValid.nil

def missing8262_8264 : List (BitVec (edgeCount 12)) :=
  missing8262_8263 ++ missing8263_8264
abbrev records8262_8264 : List Blob :=
  records8262_8263 ++ records8263_8264
theorem aligned8262_8264 :
    AlignedValid 12 3 missing8262_8264 records8262_8264 :=
  aligned8262_8263.append aligned8263_8264

def missing8260_8264 : List (BitVec (edgeCount 12)) :=
  missing8260_8262 ++ missing8262_8264
abbrev records8260_8264 : List Blob :=
  records8260_8262 ++ records8262_8264
theorem aligned8260_8264 :
    AlignedValid 12 3 missing8260_8264 records8260_8264 :=
  aligned8260_8262.append aligned8262_8264

def missing8256_8264 : List (BitVec (edgeCount 12)) :=
  missing8256_8260 ++ missing8260_8264
abbrev records8256_8264 : List Blob :=
  records8256_8260 ++ records8260_8264
theorem aligned8256_8264 :
    AlignedValid 12 3 missing8256_8264 records8256_8264 :=
  aligned8256_8260.append aligned8260_8264

def missing8264_8265 : List (BitVec (edgeCount 12)) :=
  [missing8264]
abbrev records8264_8265 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8264]
theorem aligned8264_8265 :
    AlignedValid 12 3 missing8264_8265 records8264_8265 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8264
    maskCheck8264 AlignedValid.nil

def missing8265_8266 : List (BitVec (edgeCount 12)) :=
  [missing8265]
abbrev records8265_8266 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8265]
theorem aligned8265_8266 :
    AlignedValid 12 3 missing8265_8266 records8265_8266 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8265
    maskCheck8265 AlignedValid.nil

def missing8264_8266 : List (BitVec (edgeCount 12)) :=
  missing8264_8265 ++ missing8265_8266
abbrev records8264_8266 : List Blob :=
  records8264_8265 ++ records8265_8266
theorem aligned8264_8266 :
    AlignedValid 12 3 missing8264_8266 records8264_8266 :=
  aligned8264_8265.append aligned8265_8266

def missing8266_8267 : List (BitVec (edgeCount 12)) :=
  [missing8266]
abbrev records8266_8267 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8266]
theorem aligned8266_8267 :
    AlignedValid 12 3 missing8266_8267 records8266_8267 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8266
    maskCheck8266 AlignedValid.nil

def missing8267_8268 : List (BitVec (edgeCount 12)) :=
  [missing8267]
abbrev records8267_8268 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8267]
theorem aligned8267_8268 :
    AlignedValid 12 3 missing8267_8268 records8267_8268 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8267
    maskCheck8267 AlignedValid.nil

def missing8266_8268 : List (BitVec (edgeCount 12)) :=
  missing8266_8267 ++ missing8267_8268
abbrev records8266_8268 : List Blob :=
  records8266_8267 ++ records8267_8268
theorem aligned8266_8268 :
    AlignedValid 12 3 missing8266_8268 records8266_8268 :=
  aligned8266_8267.append aligned8267_8268

def missing8264_8268 : List (BitVec (edgeCount 12)) :=
  missing8264_8266 ++ missing8266_8268
abbrev records8264_8268 : List Blob :=
  records8264_8266 ++ records8266_8268
theorem aligned8264_8268 :
    AlignedValid 12 3 missing8264_8268 records8264_8268 :=
  aligned8264_8266.append aligned8266_8268

def missing8268_8269 : List (BitVec (edgeCount 12)) :=
  [missing8268]
abbrev records8268_8269 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8268]
theorem aligned8268_8269 :
    AlignedValid 12 3 missing8268_8269 records8268_8269 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8268
    maskCheck8268 AlignedValid.nil

def missing8269_8270 : List (BitVec (edgeCount 12)) :=
  [missing8269]
abbrev records8269_8270 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8269]
theorem aligned8269_8270 :
    AlignedValid 12 3 missing8269_8270 records8269_8270 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8269
    maskCheck8269 AlignedValid.nil

def missing8268_8270 : List (BitVec (edgeCount 12)) :=
  missing8268_8269 ++ missing8269_8270
abbrev records8268_8270 : List Blob :=
  records8268_8269 ++ records8269_8270
theorem aligned8268_8270 :
    AlignedValid 12 3 missing8268_8270 records8268_8270 :=
  aligned8268_8269.append aligned8269_8270

def missing8270_8271 : List (BitVec (edgeCount 12)) :=
  [missing8270]
abbrev records8270_8271 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8270]
theorem aligned8270_8271 :
    AlignedValid 12 3 missing8270_8271 records8270_8271 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8270
    maskCheck8270 AlignedValid.nil

def missing8271_8272 : List (BitVec (edgeCount 12)) :=
  [missing8271]
abbrev records8271_8272 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8271]
theorem aligned8271_8272 :
    AlignedValid 12 3 missing8271_8272 records8271_8272 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8271
    maskCheck8271 AlignedValid.nil

def missing8270_8272 : List (BitVec (edgeCount 12)) :=
  missing8270_8271 ++ missing8271_8272
abbrev records8270_8272 : List Blob :=
  records8270_8271 ++ records8271_8272
theorem aligned8270_8272 :
    AlignedValid 12 3 missing8270_8272 records8270_8272 :=
  aligned8270_8271.append aligned8271_8272

def missing8268_8272 : List (BitVec (edgeCount 12)) :=
  missing8268_8270 ++ missing8270_8272
abbrev records8268_8272 : List Blob :=
  records8268_8270 ++ records8270_8272
theorem aligned8268_8272 :
    AlignedValid 12 3 missing8268_8272 records8268_8272 :=
  aligned8268_8270.append aligned8270_8272

def missing8264_8272 : List (BitVec (edgeCount 12)) :=
  missing8264_8268 ++ missing8268_8272
abbrev records8264_8272 : List Blob :=
  records8264_8268 ++ records8268_8272
theorem aligned8264_8272 :
    AlignedValid 12 3 missing8264_8272 records8264_8272 :=
  aligned8264_8268.append aligned8268_8272

def missing8256_8272 : List (BitVec (edgeCount 12)) :=
  missing8256_8264 ++ missing8264_8272
abbrev records8256_8272 : List Blob :=
  records8256_8264 ++ records8264_8272
theorem aligned8256_8272 :
    AlignedValid 12 3 missing8256_8272 records8256_8272 :=
  aligned8256_8264.append aligned8264_8272

def missing8272_8273 : List (BitVec (edgeCount 12)) :=
  [missing8272]
abbrev records8272_8273 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8272]
theorem aligned8272_8273 :
    AlignedValid 12 3 missing8272_8273 records8272_8273 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8272
    maskCheck8272 AlignedValid.nil

def missing8273_8274 : List (BitVec (edgeCount 12)) :=
  [missing8273]
abbrev records8273_8274 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8273]
theorem aligned8273_8274 :
    AlignedValid 12 3 missing8273_8274 records8273_8274 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8273
    maskCheck8273 AlignedValid.nil

def missing8272_8274 : List (BitVec (edgeCount 12)) :=
  missing8272_8273 ++ missing8273_8274
abbrev records8272_8274 : List Blob :=
  records8272_8273 ++ records8273_8274
theorem aligned8272_8274 :
    AlignedValid 12 3 missing8272_8274 records8272_8274 :=
  aligned8272_8273.append aligned8273_8274

def missing8274_8275 : List (BitVec (edgeCount 12)) :=
  [missing8274]
abbrev records8274_8275 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8274]
theorem aligned8274_8275 :
    AlignedValid 12 3 missing8274_8275 records8274_8275 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8274
    maskCheck8274 AlignedValid.nil

def missing8275_8276 : List (BitVec (edgeCount 12)) :=
  [missing8275]
abbrev records8275_8276 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8275]
theorem aligned8275_8276 :
    AlignedValid 12 3 missing8275_8276 records8275_8276 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8275
    maskCheck8275 AlignedValid.nil

def missing8274_8276 : List (BitVec (edgeCount 12)) :=
  missing8274_8275 ++ missing8275_8276
abbrev records8274_8276 : List Blob :=
  records8274_8275 ++ records8275_8276
theorem aligned8274_8276 :
    AlignedValid 12 3 missing8274_8276 records8274_8276 :=
  aligned8274_8275.append aligned8275_8276

def missing8272_8276 : List (BitVec (edgeCount 12)) :=
  missing8272_8274 ++ missing8274_8276
abbrev records8272_8276 : List Blob :=
  records8272_8274 ++ records8274_8276
theorem aligned8272_8276 :
    AlignedValid 12 3 missing8272_8276 records8272_8276 :=
  aligned8272_8274.append aligned8274_8276

def missing8276_8277 : List (BitVec (edgeCount 12)) :=
  [missing8276]
abbrev records8276_8277 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8276]
theorem aligned8276_8277 :
    AlignedValid 12 3 missing8276_8277 records8276_8277 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8276
    maskCheck8276 AlignedValid.nil

def missing8277_8278 : List (BitVec (edgeCount 12)) :=
  [missing8277]
abbrev records8277_8278 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8277]
theorem aligned8277_8278 :
    AlignedValid 12 3 missing8277_8278 records8277_8278 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8277
    maskCheck8277 AlignedValid.nil

def missing8276_8278 : List (BitVec (edgeCount 12)) :=
  missing8276_8277 ++ missing8277_8278
abbrev records8276_8278 : List Blob :=
  records8276_8277 ++ records8277_8278
theorem aligned8276_8278 :
    AlignedValid 12 3 missing8276_8278 records8276_8278 :=
  aligned8276_8277.append aligned8277_8278

def missing8278_8279 : List (BitVec (edgeCount 12)) :=
  [missing8278]
abbrev records8278_8279 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8278]
theorem aligned8278_8279 :
    AlignedValid 12 3 missing8278_8279 records8278_8279 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8278
    maskCheck8278 AlignedValid.nil

def missing8279_8280 : List (BitVec (edgeCount 12)) :=
  [missing8279]
abbrev records8279_8280 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8279]
theorem aligned8279_8280 :
    AlignedValid 12 3 missing8279_8280 records8279_8280 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8279
    maskCheck8279 AlignedValid.nil

def missing8278_8280 : List (BitVec (edgeCount 12)) :=
  missing8278_8279 ++ missing8279_8280
abbrev records8278_8280 : List Blob :=
  records8278_8279 ++ records8279_8280
theorem aligned8278_8280 :
    AlignedValid 12 3 missing8278_8280 records8278_8280 :=
  aligned8278_8279.append aligned8279_8280

def missing8276_8280 : List (BitVec (edgeCount 12)) :=
  missing8276_8278 ++ missing8278_8280
abbrev records8276_8280 : List Blob :=
  records8276_8278 ++ records8278_8280
theorem aligned8276_8280 :
    AlignedValid 12 3 missing8276_8280 records8276_8280 :=
  aligned8276_8278.append aligned8278_8280

def missing8272_8280 : List (BitVec (edgeCount 12)) :=
  missing8272_8276 ++ missing8276_8280
abbrev records8272_8280 : List Blob :=
  records8272_8276 ++ records8276_8280
theorem aligned8272_8280 :
    AlignedValid 12 3 missing8272_8280 records8272_8280 :=
  aligned8272_8276.append aligned8276_8280

def missing8280_8281 : List (BitVec (edgeCount 12)) :=
  [missing8280]
abbrev records8280_8281 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8280]
theorem aligned8280_8281 :
    AlignedValid 12 3 missing8280_8281 records8280_8281 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8280
    maskCheck8280 AlignedValid.nil

def missing8281_8282 : List (BitVec (edgeCount 12)) :=
  [missing8281]
abbrev records8281_8282 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8281]
theorem aligned8281_8282 :
    AlignedValid 12 3 missing8281_8282 records8281_8282 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8281
    maskCheck8281 AlignedValid.nil

def missing8280_8282 : List (BitVec (edgeCount 12)) :=
  missing8280_8281 ++ missing8281_8282
abbrev records8280_8282 : List Blob :=
  records8280_8281 ++ records8281_8282
theorem aligned8280_8282 :
    AlignedValid 12 3 missing8280_8282 records8280_8282 :=
  aligned8280_8281.append aligned8281_8282

def missing8282_8283 : List (BitVec (edgeCount 12)) :=
  [missing8282]
abbrev records8282_8283 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8282]
theorem aligned8282_8283 :
    AlignedValid 12 3 missing8282_8283 records8282_8283 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8282
    maskCheck8282 AlignedValid.nil

def missing8283_8284 : List (BitVec (edgeCount 12)) :=
  [missing8283]
abbrev records8283_8284 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8283]
theorem aligned8283_8284 :
    AlignedValid 12 3 missing8283_8284 records8283_8284 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8283
    maskCheck8283 AlignedValid.nil

def missing8282_8284 : List (BitVec (edgeCount 12)) :=
  missing8282_8283 ++ missing8283_8284
abbrev records8282_8284 : List Blob :=
  records8282_8283 ++ records8283_8284
theorem aligned8282_8284 :
    AlignedValid 12 3 missing8282_8284 records8282_8284 :=
  aligned8282_8283.append aligned8283_8284

def missing8280_8284 : List (BitVec (edgeCount 12)) :=
  missing8280_8282 ++ missing8282_8284
abbrev records8280_8284 : List Blob :=
  records8280_8282 ++ records8282_8284
theorem aligned8280_8284 :
    AlignedValid 12 3 missing8280_8284 records8280_8284 :=
  aligned8280_8282.append aligned8282_8284

def missing8284_8285 : List (BitVec (edgeCount 12)) :=
  [missing8284]
abbrev records8284_8285 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8284]
theorem aligned8284_8285 :
    AlignedValid 12 3 missing8284_8285 records8284_8285 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8284
    maskCheck8284 AlignedValid.nil

def missing8285_8286 : List (BitVec (edgeCount 12)) :=
  [missing8285]
abbrev records8285_8286 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8285]
theorem aligned8285_8286 :
    AlignedValid 12 3 missing8285_8286 records8285_8286 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8285
    maskCheck8285 AlignedValid.nil

def missing8284_8286 : List (BitVec (edgeCount 12)) :=
  missing8284_8285 ++ missing8285_8286
abbrev records8284_8286 : List Blob :=
  records8284_8285 ++ records8285_8286
theorem aligned8284_8286 :
    AlignedValid 12 3 missing8284_8286 records8284_8286 :=
  aligned8284_8285.append aligned8285_8286

def missing8286_8287 : List (BitVec (edgeCount 12)) :=
  [missing8286]
abbrev records8286_8287 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8286]
theorem aligned8286_8287 :
    AlignedValid 12 3 missing8286_8287 records8286_8287 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8286
    maskCheck8286 AlignedValid.nil

def missing8287_8288 : List (BitVec (edgeCount 12)) :=
  [missing8287]
abbrev records8287_8288 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8287]
theorem aligned8287_8288 :
    AlignedValid 12 3 missing8287_8288 records8287_8288 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8287
    maskCheck8287 AlignedValid.nil

def missing8286_8288 : List (BitVec (edgeCount 12)) :=
  missing8286_8287 ++ missing8287_8288
abbrev records8286_8288 : List Blob :=
  records8286_8287 ++ records8287_8288
theorem aligned8286_8288 :
    AlignedValid 12 3 missing8286_8288 records8286_8288 :=
  aligned8286_8287.append aligned8287_8288

def missing8284_8288 : List (BitVec (edgeCount 12)) :=
  missing8284_8286 ++ missing8286_8288
abbrev records8284_8288 : List Blob :=
  records8284_8286 ++ records8286_8288
theorem aligned8284_8288 :
    AlignedValid 12 3 missing8284_8288 records8284_8288 :=
  aligned8284_8286.append aligned8286_8288

def missing8280_8288 : List (BitVec (edgeCount 12)) :=
  missing8280_8284 ++ missing8284_8288
abbrev records8280_8288 : List Blob :=
  records8280_8284 ++ records8284_8288
theorem aligned8280_8288 :
    AlignedValid 12 3 missing8280_8288 records8280_8288 :=
  aligned8280_8284.append aligned8284_8288

def missing8272_8288 : List (BitVec (edgeCount 12)) :=
  missing8272_8280 ++ missing8280_8288
abbrev records8272_8288 : List Blob :=
  records8272_8280 ++ records8280_8288
theorem aligned8272_8288 :
    AlignedValid 12 3 missing8272_8288 records8272_8288 :=
  aligned8272_8280.append aligned8280_8288

def missing8256_8288 : List (BitVec (edgeCount 12)) :=
  missing8256_8272 ++ missing8272_8288
abbrev records8256_8288 : List Blob :=
  records8256_8272 ++ records8272_8288
theorem aligned8256_8288 :
    AlignedValid 12 3 missing8256_8288 records8256_8288 :=
  aligned8256_8272.append aligned8272_8288

def missing8288_8289 : List (BitVec (edgeCount 12)) :=
  [missing8288]
abbrev records8288_8289 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8288]
theorem aligned8288_8289 :
    AlignedValid 12 3 missing8288_8289 records8288_8289 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8288
    maskCheck8288 AlignedValid.nil

def missing8289_8290 : List (BitVec (edgeCount 12)) :=
  [missing8289]
abbrev records8289_8290 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8289]
theorem aligned8289_8290 :
    AlignedValid 12 3 missing8289_8290 records8289_8290 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8289
    maskCheck8289 AlignedValid.nil

def missing8288_8290 : List (BitVec (edgeCount 12)) :=
  missing8288_8289 ++ missing8289_8290
abbrev records8288_8290 : List Blob :=
  records8288_8289 ++ records8289_8290
theorem aligned8288_8290 :
    AlignedValid 12 3 missing8288_8290 records8288_8290 :=
  aligned8288_8289.append aligned8289_8290

def missing8290_8291 : List (BitVec (edgeCount 12)) :=
  [missing8290]
abbrev records8290_8291 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8290]
theorem aligned8290_8291 :
    AlignedValid 12 3 missing8290_8291 records8290_8291 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8290
    maskCheck8290 AlignedValid.nil

def missing8291_8292 : List (BitVec (edgeCount 12)) :=
  [missing8291]
abbrev records8291_8292 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8291]
theorem aligned8291_8292 :
    AlignedValid 12 3 missing8291_8292 records8291_8292 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8291
    maskCheck8291 AlignedValid.nil

def missing8290_8292 : List (BitVec (edgeCount 12)) :=
  missing8290_8291 ++ missing8291_8292
abbrev records8290_8292 : List Blob :=
  records8290_8291 ++ records8291_8292
theorem aligned8290_8292 :
    AlignedValid 12 3 missing8290_8292 records8290_8292 :=
  aligned8290_8291.append aligned8291_8292

def missing8288_8292 : List (BitVec (edgeCount 12)) :=
  missing8288_8290 ++ missing8290_8292
abbrev records8288_8292 : List Blob :=
  records8288_8290 ++ records8290_8292
theorem aligned8288_8292 :
    AlignedValid 12 3 missing8288_8292 records8288_8292 :=
  aligned8288_8290.append aligned8290_8292

def missing8292_8293 : List (BitVec (edgeCount 12)) :=
  [missing8292]
abbrev records8292_8293 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8292]
theorem aligned8292_8293 :
    AlignedValid 12 3 missing8292_8293 records8292_8293 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8292
    maskCheck8292 AlignedValid.nil

def missing8293_8294 : List (BitVec (edgeCount 12)) :=
  [missing8293]
abbrev records8293_8294 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8293]
theorem aligned8293_8294 :
    AlignedValid 12 3 missing8293_8294 records8293_8294 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8293
    maskCheck8293 AlignedValid.nil

def missing8292_8294 : List (BitVec (edgeCount 12)) :=
  missing8292_8293 ++ missing8293_8294
abbrev records8292_8294 : List Blob :=
  records8292_8293 ++ records8293_8294
theorem aligned8292_8294 :
    AlignedValid 12 3 missing8292_8294 records8292_8294 :=
  aligned8292_8293.append aligned8293_8294

def missing8294_8295 : List (BitVec (edgeCount 12)) :=
  [missing8294]
abbrev records8294_8295 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8294]
theorem aligned8294_8295 :
    AlignedValid 12 3 missing8294_8295 records8294_8295 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8294
    maskCheck8294 AlignedValid.nil

def missing8295_8296 : List (BitVec (edgeCount 12)) :=
  [missing8295]
abbrev records8295_8296 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8295]
theorem aligned8295_8296 :
    AlignedValid 12 3 missing8295_8296 records8295_8296 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8295
    maskCheck8295 AlignedValid.nil

def missing8294_8296 : List (BitVec (edgeCount 12)) :=
  missing8294_8295 ++ missing8295_8296
abbrev records8294_8296 : List Blob :=
  records8294_8295 ++ records8295_8296
theorem aligned8294_8296 :
    AlignedValid 12 3 missing8294_8296 records8294_8296 :=
  aligned8294_8295.append aligned8295_8296

def missing8292_8296 : List (BitVec (edgeCount 12)) :=
  missing8292_8294 ++ missing8294_8296
abbrev records8292_8296 : List Blob :=
  records8292_8294 ++ records8294_8296
theorem aligned8292_8296 :
    AlignedValid 12 3 missing8292_8296 records8292_8296 :=
  aligned8292_8294.append aligned8294_8296

def missing8288_8296 : List (BitVec (edgeCount 12)) :=
  missing8288_8292 ++ missing8292_8296
abbrev records8288_8296 : List Blob :=
  records8288_8292 ++ records8292_8296
theorem aligned8288_8296 :
    AlignedValid 12 3 missing8288_8296 records8288_8296 :=
  aligned8288_8292.append aligned8292_8296

def missing8296_8297 : List (BitVec (edgeCount 12)) :=
  [missing8296]
abbrev records8296_8297 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8296]
theorem aligned8296_8297 :
    AlignedValid 12 3 missing8296_8297 records8296_8297 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8296
    maskCheck8296 AlignedValid.nil

def missing8297_8298 : List (BitVec (edgeCount 12)) :=
  [missing8297]
abbrev records8297_8298 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8297]
theorem aligned8297_8298 :
    AlignedValid 12 3 missing8297_8298 records8297_8298 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8297
    maskCheck8297 AlignedValid.nil

def missing8296_8298 : List (BitVec (edgeCount 12)) :=
  missing8296_8297 ++ missing8297_8298
abbrev records8296_8298 : List Blob :=
  records8296_8297 ++ records8297_8298
theorem aligned8296_8298 :
    AlignedValid 12 3 missing8296_8298 records8296_8298 :=
  aligned8296_8297.append aligned8297_8298

def missing8298_8299 : List (BitVec (edgeCount 12)) :=
  [missing8298]
abbrev records8298_8299 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8298]
theorem aligned8298_8299 :
    AlignedValid 12 3 missing8298_8299 records8298_8299 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8298
    maskCheck8298 AlignedValid.nil

def missing8299_8300 : List (BitVec (edgeCount 12)) :=
  [missing8299]
abbrev records8299_8300 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8299]
theorem aligned8299_8300 :
    AlignedValid 12 3 missing8299_8300 records8299_8300 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8299
    maskCheck8299 AlignedValid.nil

def missing8298_8300 : List (BitVec (edgeCount 12)) :=
  missing8298_8299 ++ missing8299_8300
abbrev records8298_8300 : List Blob :=
  records8298_8299 ++ records8299_8300
theorem aligned8298_8300 :
    AlignedValid 12 3 missing8298_8300 records8298_8300 :=
  aligned8298_8299.append aligned8299_8300

def missing8296_8300 : List (BitVec (edgeCount 12)) :=
  missing8296_8298 ++ missing8298_8300
abbrev records8296_8300 : List Blob :=
  records8296_8298 ++ records8298_8300
theorem aligned8296_8300 :
    AlignedValid 12 3 missing8296_8300 records8296_8300 :=
  aligned8296_8298.append aligned8298_8300

def missing8300_8301 : List (BitVec (edgeCount 12)) :=
  [missing8300]
abbrev records8300_8301 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8300]
theorem aligned8300_8301 :
    AlignedValid 12 3 missing8300_8301 records8300_8301 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8300
    maskCheck8300 AlignedValid.nil

def missing8301_8302 : List (BitVec (edgeCount 12)) :=
  [missing8301]
abbrev records8301_8302 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8301]
theorem aligned8301_8302 :
    AlignedValid 12 3 missing8301_8302 records8301_8302 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8301
    maskCheck8301 AlignedValid.nil

def missing8300_8302 : List (BitVec (edgeCount 12)) :=
  missing8300_8301 ++ missing8301_8302
abbrev records8300_8302 : List Blob :=
  records8300_8301 ++ records8301_8302
theorem aligned8300_8302 :
    AlignedValid 12 3 missing8300_8302 records8300_8302 :=
  aligned8300_8301.append aligned8301_8302

def missing8302_8303 : List (BitVec (edgeCount 12)) :=
  [missing8302]
abbrev records8302_8303 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8302]
theorem aligned8302_8303 :
    AlignedValid 12 3 missing8302_8303 records8302_8303 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8302
    maskCheck8302 AlignedValid.nil

def missing8303_8304 : List (BitVec (edgeCount 12)) :=
  [missing8303]
abbrev records8303_8304 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8303]
theorem aligned8303_8304 :
    AlignedValid 12 3 missing8303_8304 records8303_8304 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8303
    maskCheck8303 AlignedValid.nil

def missing8302_8304 : List (BitVec (edgeCount 12)) :=
  missing8302_8303 ++ missing8303_8304
abbrev records8302_8304 : List Blob :=
  records8302_8303 ++ records8303_8304
theorem aligned8302_8304 :
    AlignedValid 12 3 missing8302_8304 records8302_8304 :=
  aligned8302_8303.append aligned8303_8304

def missing8300_8304 : List (BitVec (edgeCount 12)) :=
  missing8300_8302 ++ missing8302_8304
abbrev records8300_8304 : List Blob :=
  records8300_8302 ++ records8302_8304
theorem aligned8300_8304 :
    AlignedValid 12 3 missing8300_8304 records8300_8304 :=
  aligned8300_8302.append aligned8302_8304

def missing8296_8304 : List (BitVec (edgeCount 12)) :=
  missing8296_8300 ++ missing8300_8304
abbrev records8296_8304 : List Blob :=
  records8296_8300 ++ records8300_8304
theorem aligned8296_8304 :
    AlignedValid 12 3 missing8296_8304 records8296_8304 :=
  aligned8296_8300.append aligned8300_8304

def missing8288_8304 : List (BitVec (edgeCount 12)) :=
  missing8288_8296 ++ missing8296_8304
abbrev records8288_8304 : List Blob :=
  records8288_8296 ++ records8296_8304
theorem aligned8288_8304 :
    AlignedValid 12 3 missing8288_8304 records8288_8304 :=
  aligned8288_8296.append aligned8296_8304

def missing8304_8305 : List (BitVec (edgeCount 12)) :=
  [missing8304]
abbrev records8304_8305 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8304]
theorem aligned8304_8305 :
    AlignedValid 12 3 missing8304_8305 records8304_8305 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8304
    maskCheck8304 AlignedValid.nil

def missing8305_8306 : List (BitVec (edgeCount 12)) :=
  [missing8305]
abbrev records8305_8306 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8305]
theorem aligned8305_8306 :
    AlignedValid 12 3 missing8305_8306 records8305_8306 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8305
    maskCheck8305 AlignedValid.nil

def missing8304_8306 : List (BitVec (edgeCount 12)) :=
  missing8304_8305 ++ missing8305_8306
abbrev records8304_8306 : List Blob :=
  records8304_8305 ++ records8305_8306
theorem aligned8304_8306 :
    AlignedValid 12 3 missing8304_8306 records8304_8306 :=
  aligned8304_8305.append aligned8305_8306

def missing8306_8307 : List (BitVec (edgeCount 12)) :=
  [missing8306]
abbrev records8306_8307 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8306]
theorem aligned8306_8307 :
    AlignedValid 12 3 missing8306_8307 records8306_8307 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8306
    maskCheck8306 AlignedValid.nil

def missing8307_8308 : List (BitVec (edgeCount 12)) :=
  [missing8307]
abbrev records8307_8308 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8307]
theorem aligned8307_8308 :
    AlignedValid 12 3 missing8307_8308 records8307_8308 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8307
    maskCheck8307 AlignedValid.nil

def missing8306_8308 : List (BitVec (edgeCount 12)) :=
  missing8306_8307 ++ missing8307_8308
abbrev records8306_8308 : List Blob :=
  records8306_8307 ++ records8307_8308
theorem aligned8306_8308 :
    AlignedValid 12 3 missing8306_8308 records8306_8308 :=
  aligned8306_8307.append aligned8307_8308

def missing8304_8308 : List (BitVec (edgeCount 12)) :=
  missing8304_8306 ++ missing8306_8308
abbrev records8304_8308 : List Blob :=
  records8304_8306 ++ records8306_8308
theorem aligned8304_8308 :
    AlignedValid 12 3 missing8304_8308 records8304_8308 :=
  aligned8304_8306.append aligned8306_8308

def missing8308_8309 : List (BitVec (edgeCount 12)) :=
  [missing8308]
abbrev records8308_8309 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8308]
theorem aligned8308_8309 :
    AlignedValid 12 3 missing8308_8309 records8308_8309 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8308
    maskCheck8308 AlignedValid.nil

def missing8309_8310 : List (BitVec (edgeCount 12)) :=
  [missing8309]
abbrev records8309_8310 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8309]
theorem aligned8309_8310 :
    AlignedValid 12 3 missing8309_8310 records8309_8310 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8309
    maskCheck8309 AlignedValid.nil

def missing8308_8310 : List (BitVec (edgeCount 12)) :=
  missing8308_8309 ++ missing8309_8310
abbrev records8308_8310 : List Blob :=
  records8308_8309 ++ records8309_8310
theorem aligned8308_8310 :
    AlignedValid 12 3 missing8308_8310 records8308_8310 :=
  aligned8308_8309.append aligned8309_8310

def missing8310_8311 : List (BitVec (edgeCount 12)) :=
  [missing8310]
abbrev records8310_8311 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8310]
theorem aligned8310_8311 :
    AlignedValid 12 3 missing8310_8311 records8310_8311 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8310
    maskCheck8310 AlignedValid.nil

def missing8311_8312 : List (BitVec (edgeCount 12)) :=
  [missing8311]
abbrev records8311_8312 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8311]
theorem aligned8311_8312 :
    AlignedValid 12 3 missing8311_8312 records8311_8312 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8311
    maskCheck8311 AlignedValid.nil

def missing8310_8312 : List (BitVec (edgeCount 12)) :=
  missing8310_8311 ++ missing8311_8312
abbrev records8310_8312 : List Blob :=
  records8310_8311 ++ records8311_8312
theorem aligned8310_8312 :
    AlignedValid 12 3 missing8310_8312 records8310_8312 :=
  aligned8310_8311.append aligned8311_8312

def missing8308_8312 : List (BitVec (edgeCount 12)) :=
  missing8308_8310 ++ missing8310_8312
abbrev records8308_8312 : List Blob :=
  records8308_8310 ++ records8310_8312
theorem aligned8308_8312 :
    AlignedValid 12 3 missing8308_8312 records8308_8312 :=
  aligned8308_8310.append aligned8310_8312

def missing8304_8312 : List (BitVec (edgeCount 12)) :=
  missing8304_8308 ++ missing8308_8312
abbrev records8304_8312 : List Blob :=
  records8304_8308 ++ records8308_8312
theorem aligned8304_8312 :
    AlignedValid 12 3 missing8304_8312 records8304_8312 :=
  aligned8304_8308.append aligned8308_8312

def missing8312_8313 : List (BitVec (edgeCount 12)) :=
  [missing8312]
abbrev records8312_8313 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8312]
theorem aligned8312_8313 :
    AlignedValid 12 3 missing8312_8313 records8312_8313 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8312
    maskCheck8312 AlignedValid.nil

def missing8313_8314 : List (BitVec (edgeCount 12)) :=
  [missing8313]
abbrev records8313_8314 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8313]
theorem aligned8313_8314 :
    AlignedValid 12 3 missing8313_8314 records8313_8314 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8313
    maskCheck8313 AlignedValid.nil

def missing8312_8314 : List (BitVec (edgeCount 12)) :=
  missing8312_8313 ++ missing8313_8314
abbrev records8312_8314 : List Blob :=
  records8312_8313 ++ records8313_8314
theorem aligned8312_8314 :
    AlignedValid 12 3 missing8312_8314 records8312_8314 :=
  aligned8312_8313.append aligned8313_8314

def missing8314_8315 : List (BitVec (edgeCount 12)) :=
  [missing8314]
abbrev records8314_8315 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8314]
theorem aligned8314_8315 :
    AlignedValid 12 3 missing8314_8315 records8314_8315 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8314
    maskCheck8314 AlignedValid.nil

def missing8315_8316 : List (BitVec (edgeCount 12)) :=
  [missing8315]
abbrev records8315_8316 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8315]
theorem aligned8315_8316 :
    AlignedValid 12 3 missing8315_8316 records8315_8316 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8315
    maskCheck8315 AlignedValid.nil

def missing8314_8316 : List (BitVec (edgeCount 12)) :=
  missing8314_8315 ++ missing8315_8316
abbrev records8314_8316 : List Blob :=
  records8314_8315 ++ records8315_8316
theorem aligned8314_8316 :
    AlignedValid 12 3 missing8314_8316 records8314_8316 :=
  aligned8314_8315.append aligned8315_8316

def missing8312_8316 : List (BitVec (edgeCount 12)) :=
  missing8312_8314 ++ missing8314_8316
abbrev records8312_8316 : List Blob :=
  records8312_8314 ++ records8314_8316
theorem aligned8312_8316 :
    AlignedValid 12 3 missing8312_8316 records8312_8316 :=
  aligned8312_8314.append aligned8314_8316

def missing8316_8317 : List (BitVec (edgeCount 12)) :=
  [missing8316]
abbrev records8316_8317 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8316]
theorem aligned8316_8317 :
    AlignedValid 12 3 missing8316_8317 records8316_8317 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8316
    maskCheck8316 AlignedValid.nil

def missing8317_8318 : List (BitVec (edgeCount 12)) :=
  [missing8317]
abbrev records8317_8318 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8317]
theorem aligned8317_8318 :
    AlignedValid 12 3 missing8317_8318 records8317_8318 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8317
    maskCheck8317 AlignedValid.nil

def missing8316_8318 : List (BitVec (edgeCount 12)) :=
  missing8316_8317 ++ missing8317_8318
abbrev records8316_8318 : List Blob :=
  records8316_8317 ++ records8317_8318
theorem aligned8316_8318 :
    AlignedValid 12 3 missing8316_8318 records8316_8318 :=
  aligned8316_8317.append aligned8317_8318

def missing8318_8319 : List (BitVec (edgeCount 12)) :=
  [missing8318]
abbrev records8318_8319 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8318]
theorem aligned8318_8319 :
    AlignedValid 12 3 missing8318_8319 records8318_8319 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8318
    maskCheck8318 AlignedValid.nil

def missing8319_8320 : List (BitVec (edgeCount 12)) :=
  [missing8319]
abbrev records8319_8320 : List Blob :=
  [StrongPackedBucketN12A3Shard064.record8319]
theorem aligned8319_8320 :
    AlignedValid 12 3 missing8319_8320 records8319_8320 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard064.check8319
    maskCheck8319 AlignedValid.nil

def missing8318_8320 : List (BitVec (edgeCount 12)) :=
  missing8318_8319 ++ missing8319_8320
abbrev records8318_8320 : List Blob :=
  records8318_8319 ++ records8319_8320
theorem aligned8318_8320 :
    AlignedValid 12 3 missing8318_8320 records8318_8320 :=
  aligned8318_8319.append aligned8319_8320

def missing8316_8320 : List (BitVec (edgeCount 12)) :=
  missing8316_8318 ++ missing8318_8320
abbrev records8316_8320 : List Blob :=
  records8316_8318 ++ records8318_8320
theorem aligned8316_8320 :
    AlignedValid 12 3 missing8316_8320 records8316_8320 :=
  aligned8316_8318.append aligned8318_8320

def missing8312_8320 : List (BitVec (edgeCount 12)) :=
  missing8312_8316 ++ missing8316_8320
abbrev records8312_8320 : List Blob :=
  records8312_8316 ++ records8316_8320
theorem aligned8312_8320 :
    AlignedValid 12 3 missing8312_8320 records8312_8320 :=
  aligned8312_8316.append aligned8316_8320

def missing8304_8320 : List (BitVec (edgeCount 12)) :=
  missing8304_8312 ++ missing8312_8320
abbrev records8304_8320 : List Blob :=
  records8304_8312 ++ records8312_8320
theorem aligned8304_8320 :
    AlignedValid 12 3 missing8304_8320 records8304_8320 :=
  aligned8304_8312.append aligned8312_8320

def missing8288_8320 : List (BitVec (edgeCount 12)) :=
  missing8288_8304 ++ missing8304_8320
abbrev records8288_8320 : List Blob :=
  records8288_8304 ++ records8304_8320
theorem aligned8288_8320 :
    AlignedValid 12 3 missing8288_8320 records8288_8320 :=
  aligned8288_8304.append aligned8304_8320

def missing8256_8320 : List (BitVec (edgeCount 12)) :=
  missing8256_8288 ++ missing8288_8320
abbrev records8256_8320 : List Blob :=
  records8256_8288 ++ records8288_8320
theorem aligned8256_8320 :
    AlignedValid 12 3 missing8256_8320 records8256_8320 :=
  aligned8256_8288.append aligned8288_8320

def missing8192_8320 : List (BitVec (edgeCount 12)) :=
  missing8192_8256 ++ missing8256_8320
abbrev records8192_8320 : List Blob :=
  records8192_8256 ++ records8256_8320
theorem aligned8192_8320 :
    AlignedValid 12 3 missing8192_8320 records8192_8320 :=
  aligned8192_8256.append aligned8256_8320

abbrev missing : List (BitVec (edgeCount 12)) := missing8192_8320
abbrev records : List Blob := records8192_8320
theorem aligned : AlignedValid 12 3 missing records := aligned8192_8320

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard064
