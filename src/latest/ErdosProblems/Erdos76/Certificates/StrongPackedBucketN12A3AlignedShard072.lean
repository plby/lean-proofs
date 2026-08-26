/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A3Shard072

/-! Decode-only alignment checks for n=12, a=3, records 9216--9343. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard072

open PackedBucketCertificate

def missing9216 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9408442247166296064
theorem maskCheck9216 :
    checkMaskFor missing9216 StrongPackedBucketN12A3Shard072.record9216 = true := by
  decide

def missing9217 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9444471044185260032
theorem maskCheck9217 :
    checkMaskFor missing9217 StrongPackedBucketN12A3Shard072.record9217 = true := by
  decide

def missing9218 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18559756689983143936
theorem maskCheck9218 :
    checkMaskFor missing9218 StrongPackedBucketN12A3Shard072.record9218 = true := by
  decide

def missing9219 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18631814284021071872
theorem maskCheck9219 :
    checkMaskFor missing9219 StrongPackedBucketN12A3Shard072.record9219 = true := by
  decide

def missing9220 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18775929472096927744
theorem maskCheck9220 :
    checkMaskFor missing9220 StrongPackedBucketN12A3Shard072.record9220 = true := by
  decide

def missing9221 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19064159848248639488
theorem maskCheck9221 :
    checkMaskFor missing9221 StrongPackedBucketN12A3Shard072.record9221 = true := by
  decide

def missing9222 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 542121630585847808
theorem maskCheck9222 :
    checkMaskFor missing9222 StrongPackedBucketN12A3Shard072.record9222 = true := by
  decide

def missing9223 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 830352006737559552
theorem maskCheck9223 :
    checkMaskFor missing9223 StrongPackedBucketN12A3Shard072.record9223 = true := by
  decide

def missing9224 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1046524788851343360
theorem maskCheck9224 :
    checkMaskFor missing9224 StrongPackedBucketN12A3Shard072.record9224 = true := by
  decide

def missing9225 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1082553585870307328
theorem maskCheck9225 :
    checkMaskFor missing9225 StrongPackedBucketN12A3Shard072.record9225 = true := by
  decide

def missing9226 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2163417496439226368
theorem maskCheck9226 :
    checkMaskFor missing9226 StrongPackedBucketN12A3Shard072.record9226 = true := by
  decide

def missing9227 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2559734263647830016
theorem maskCheck9227 :
    checkMaskFor missing9227 StrongPackedBucketN12A3Shard072.record9227 = true := by
  decide

def missing9228 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2775907045761613824
theorem maskCheck9228 :
    checkMaskFor missing9228 StrongPackedBucketN12A3Shard072.record9228 = true := by
  decide

def missing9229 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2811935842780577792
theorem maskCheck9229 :
    checkMaskFor missing9229 StrongPackedBucketN12A3Shard072.record9229 = true := by
  decide

def missing9230 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3064137421913325568
theorem maskCheck9230 :
    checkMaskFor missing9230 StrongPackedBucketN12A3Shard072.record9230 = true := by
  decide

def missing9231 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3100166218932289536
theorem maskCheck9231 :
    checkMaskFor missing9231 StrongPackedBucketN12A3Shard072.record9231 = true := by
  decide

def missing9232 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3316339001046073344
theorem maskCheck9232 :
    checkMaskFor missing9232 StrongPackedBucketN12A3Shard072.record9232 = true := by
  decide

def missing9233 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4865577272861523968
theorem maskCheck9233 :
    checkMaskFor missing9233 StrongPackedBucketN12A3Shard072.record9233 = true := by
  decide

def missing9234 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5081750054975307776
theorem maskCheck9234 :
    checkMaskFor missing9234 StrongPackedBucketN12A3Shard072.record9234 = true := by
  decide

def missing9235 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5117778851994271744
theorem maskCheck9235 :
    checkMaskFor missing9235 StrongPackedBucketN12A3Shard072.record9235 = true := by
  decide

def missing9236 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5369980431127019520
theorem maskCheck9236 :
    checkMaskFor missing9236 StrongPackedBucketN12A3Shard072.record9236 = true := by
  decide

def missing9237 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5406009228145983488
theorem maskCheck9237 :
    checkMaskFor missing9237 StrongPackedBucketN12A3Shard072.record9237 = true := by
  decide

def missing9238 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7027305093999362048
theorem maskCheck9238 :
    checkMaskFor missing9238 StrongPackedBucketN12A3Shard072.record9238 = true := by
  decide

def missing9239 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7099362688037289984
theorem maskCheck9239 :
    checkMaskFor missing9239 StrongPackedBucketN12A3Shard072.record9239 = true := by
  decide

def missing9240 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7135391485056253952
theorem maskCheck9240 :
    checkMaskFor missing9240 StrongPackedBucketN12A3Shard072.record9240 = true := by
  decide

def missing9241 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9477263291288911872
theorem maskCheck9241 :
    checkMaskFor missing9241 StrongPackedBucketN12A3Shard072.record9241 = true := by
  decide

def missing9242 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9693436073402695680
theorem maskCheck9242 :
    checkMaskFor missing9242 StrongPackedBucketN12A3Shard072.record9242 = true := by
  decide

def missing9243 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9981666449554407424
theorem maskCheck9243 :
    checkMaskFor missing9243 StrongPackedBucketN12A3Shard072.record9243 = true := by
  decide

def missing9244 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11638991112426749952
theorem maskCheck9244 :
    checkMaskFor missing9244 StrongPackedBucketN12A3Shard072.record9244 = true := by
  decide

def missing9245 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11711048706464677888
theorem maskCheck9245 :
    checkMaskFor missing9245 StrongPackedBucketN12A3Shard072.record9245 = true := by
  decide

def missing9246 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13944834121640443904
theorem maskCheck9246 :
    checkMaskFor missing9246 StrongPackedBucketN12A3Shard072.record9246 = true := by
  decide

def missing9247 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18700635328143687680
theorem maskCheck9247 :
    checkMaskFor missing9247 StrongPackedBucketN12A3Shard072.record9247 = true := by
  decide

def missing9248 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18916808110257471488
theorem maskCheck9248 :
    checkMaskFor missing9248 StrongPackedBucketN12A3Shard072.record9248 = true := by
  decide

def missing9249 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18952836907276435456
theorem maskCheck9249 :
    checkMaskFor missing9249 StrongPackedBucketN12A3Shard072.record9249 = true := by
  decide

def missing9250 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19132980892371255296
theorem maskCheck9250 :
    checkMaskFor missing9250 StrongPackedBucketN12A3Shard072.record9250 = true := by
  decide

def missing9251 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19205038486409183232
theorem maskCheck9251 :
    checkMaskFor missing9251 StrongPackedBucketN12A3Shard072.record9251 = true := by
  decide

def missing9252 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19241067283428147200
theorem maskCheck9252 :
    checkMaskFor missing9252 StrongPackedBucketN12A3Shard072.record9252 = true := by
  decide

def missing9253 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19457240065541931008
theorem maskCheck9253 :
    checkMaskFor missing9253 StrongPackedBucketN12A3Shard072.record9253 = true := by
  decide

def missing9254 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20213844802940174336
theorem maskCheck9254 :
    checkMaskFor missing9254 StrongPackedBucketN12A3Shard072.record9254 = true := by
  decide

def missing9255 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20249873599959138304
theorem maskCheck9255 :
    checkMaskFor missing9255 StrongPackedBucketN12A3Shard072.record9255 = true := by
  decide

def missing9256 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20321931193997066240
theorem maskCheck9256 :
    checkMaskFor missing9256 StrongPackedBucketN12A3Shard072.record9256 = true := by
  decide

def missing9257 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20862363149281525760
theorem maskCheck9257 :
    checkMaskFor missing9257 StrongPackedBucketN12A3Shard072.record9257 = true := by
  decide

def missing9258 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20934420743319453696
theorem maskCheck9258 :
    checkMaskFor missing9258 StrongPackedBucketN12A3Shard072.record9258 = true := by
  decide

def missing9259 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20970449540338417664
theorem maskCheck9259 :
    checkMaskFor missing9259 StrongPackedBucketN12A3Shard072.record9259 = true := by
  decide

def missing9260 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21186622322452201472
theorem maskCheck9260 :
    checkMaskFor missing9260 StrongPackedBucketN12A3Shard072.record9260 = true := by
  decide

def missing9261 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21366766307547021312
theorem maskCheck9261 :
    checkMaskFor missing9261 StrongPackedBucketN12A3Shard072.record9261 = true := by
  decide

def missing9262 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21402795104565985280
theorem maskCheck9262 :
    checkMaskFor missing9262 StrongPackedBucketN12A3Shard072.record9262 = true := by
  decide

def missing9263 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21474852698603913216
theorem maskCheck9263 :
    checkMaskFor missing9263 StrongPackedBucketN12A3Shard072.record9263 = true := by
  decide

def missing9264 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22483659015134904320
theorem maskCheck9264 :
    checkMaskFor missing9264 StrongPackedBucketN12A3Shard072.record9264 = true := by
  decide

def missing9265 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23168206158495219712
theorem maskCheck9265 :
    checkMaskFor missing9265 StrongPackedBucketN12A3Shard072.record9265 = true := by
  decide

def missing9266 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23240263752533147648
theorem maskCheck9266 :
    checkMaskFor missing9266 StrongPackedBucketN12A3Shard072.record9266 = true := by
  decide

def missing9267 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23276292549552111616
theorem maskCheck9267 :
    checkMaskFor missing9267 StrongPackedBucketN12A3Shard072.record9267 = true := by
  decide

def missing9268 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23672609316760715264
theorem maskCheck9268 :
    checkMaskFor missing9268 StrongPackedBucketN12A3Shard072.record9268 = true := by
  decide

def missing9269 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23708638113779679232
theorem maskCheck9269 :
    checkMaskFor missing9269 StrongPackedBucketN12A3Shard072.record9269 = true := by
  decide

def missing9270 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25401991573670985728
theorem maskCheck9270 :
    checkMaskFor missing9270 StrongPackedBucketN12A3Shard072.record9270 = true := by
  decide

def missing9271 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 25438020370689949696
theorem maskCheck9271 :
    checkMaskFor missing9271 StrongPackedBucketN12A3Shard072.record9271 = true := by
  decide

def missing9272 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27779892176922607616
theorem maskCheck9272 :
    checkMaskFor missing9272 StrongPackedBucketN12A3Shard072.record9272 = true := by
  decide

def missing9273 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27851949770960535552
theorem maskCheck9273 :
    checkMaskFor missing9273 StrongPackedBucketN12A3Shard072.record9273 = true := by
  decide

def missing9274 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28284295335188103168
theorem maskCheck9274 :
    checkMaskFor missing9274 StrongPackedBucketN12A3Shard072.record9274 = true := by
  decide

def missing9275 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30013677592098373632
theorem maskCheck9275 :
    checkMaskFor missing9275 StrongPackedBucketN12A3Shard072.record9275 = true := by
  decide

def missing9276 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55450008287486935040
theorem maskCheck9276 :
    checkMaskFor missing9276 StrongPackedBucketN12A3Shard072.record9276 = true := by
  decide

def missing9277 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55522065881524862976
theorem maskCheck9277 :
    checkMaskFor missing9277 StrongPackedBucketN12A3Shard072.record9277 = true := by
  decide

def missing9278 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55558094678543826944
theorem maskCheck9278 :
    checkMaskFor missing9278 StrongPackedBucketN12A3Shard072.record9278 = true := by
  decide

def missing9279 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55774267460657610752
theorem maskCheck9279 :
    checkMaskFor missing9279 StrongPackedBucketN12A3Shard072.record9279 = true := by
  decide

def missing9280 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56062497836809322496
theorem maskCheck9280 :
    checkMaskFor missing9280 StrongPackedBucketN12A3Shard072.record9280 = true := by
  decide

def missing9281 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57683793702662701056
theorem maskCheck9281 :
    checkMaskFor missing9281 StrongPackedBucketN12A3Shard072.record9281 = true := by
  decide

def missing9282 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57719822499681665024
theorem maskCheck9282 :
    checkMaskFor missing9282 StrongPackedBucketN12A3Shard072.record9282 = true := by
  decide

def missing9283 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57791880093719592960
theorem maskCheck9283 :
    checkMaskFor missing9283 StrongPackedBucketN12A3Shard072.record9283 = true := by
  decide

def missing9284 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59989636711876395008
theorem maskCheck9284 :
    checkMaskFor missing9284 StrongPackedBucketN12A3Shard072.record9284 = true := by
  decide

def missing9285 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 60025665508895358976
theorem maskCheck9285 :
    checkMaskFor missing9285 StrongPackedBucketN12A3Shard072.record9285 = true := by
  decide

def missing9286 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64601322730303782912
theorem maskCheck9286 :
    checkMaskFor missing9286 StrongPackedBucketN12A3Shard072.record9286 = true := by
  decide

def missing9287 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9655964717128089600
theorem maskCheck9287 :
    checkMaskFor missing9287 StrongPackedBucketN12A3Shard072.record9287 = true := by
  decide

def missing9288 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18663163971869081600
theorem maskCheck9288 :
    checkMaskFor missing9288 StrongPackedBucketN12A3Shard072.record9288 = true := by
  decide

def missing9289 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27814478414685929472
theorem maskCheck9289 :
    checkMaskFor missing9289 StrongPackedBucketN12A3Shard072.record9289 = true := by
  decide

def missing9290 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27958593602761785344
theorem maskCheck9290 :
    checkMaskFor missing9290 StrongPackedBucketN12A3Shard072.record9290 = true := by
  decide

def missing9291 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28246823978913497088
theorem maskCheck9291 :
    checkMaskFor missing9291 StrongPackedBucketN12A3Shard072.record9291 = true := by
  decide

def missing9292 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32282049245037461504
theorem maskCheck9292 :
    checkMaskFor missing9292 StrongPackedBucketN12A3Shard072.record9292 = true := by
  decide

def missing9293 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9656175823360622592
theorem maskCheck9293 :
    checkMaskFor missing9293 StrongPackedBucketN12A3Shard072.record9293 = true := by
  decide

def missing9294 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18879547860215398400
theorem maskCheck9294 :
    checkMaskFor missing9294 StrongPackedBucketN12A3Shard072.record9294 = true := by
  decide

def missing9295 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19095720642329182208
theorem maskCheck9295 :
    checkMaskFor missing9295 StrongPackedBucketN12A3Shard072.record9295 = true := by
  decide

def missing9296 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23130945908453146624
theorem maskCheck9296 :
    checkMaskFor missing9296 StrongPackedBucketN12A3Shard072.record9296 = true := by
  decide

def missing9297 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27814689520918462464
theorem maskCheck9297 :
    checkMaskFor missing9297 StrongPackedBucketN12A3Shard072.record9297 = true := by
  decide

def missing9298 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28247035085146030080
theorem maskCheck9298 :
    checkMaskFor missing9298 StrongPackedBucketN12A3Shard072.record9298 = true := by
  decide

def missing9299 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32282260351269994496
theorem maskCheck9299 :
    checkMaskFor missing9299 StrongPackedBucketN12A3Shard072.record9299 = true := by
  decide

def missing9300 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 252694985783115776
theorem maskCheck9300 :
    checkMaskFor missing9300 StrongPackedBucketN12A3Shard072.record9300 = true := by
  decide

def missing9301 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 468867767896899584
theorem maskCheck9301 :
    checkMaskFor missing9301 StrongPackedBucketN12A3Shard072.record9301 = true := by
  decide

def missing9302 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 504896564915863552
theorem maskCheck9302 :
    checkMaskFor missing9302 StrongPackedBucketN12A3Shard072.record9302 = true := by
  decide

def missing9303 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5044524989305323520
theorem maskCheck9303 :
    checkMaskFor missing9303 StrongPackedBucketN12A3Shard072.record9303 = true := by
  decide

def missing9304 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9404009428599963648
theorem maskCheck9304 :
    checkMaskFor missing9304 StrongPackedBucketN12A3Shard072.record9304 = true := by
  decide

def missing9305 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9440038225618927616
theorem maskCheck9305 :
    checkMaskFor missing9305 StrongPackedBucketN12A3Shard072.record9305 = true := by
  decide

def missing9306 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9656211007732711424
theorem maskCheck9306 :
    checkMaskFor missing9306 StrongPackedBucketN12A3Shard072.record9306 = true := by
  decide

def missing9307 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9836354992827531264
theorem maskCheck9307 :
    checkMaskFor missing9307 StrongPackedBucketN12A3Shard072.record9307 = true := by
  decide

def missing9308 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13871580258951495680
theorem maskCheck9308 :
    checkMaskFor missing9308 StrongPackedBucketN12A3Shard072.record9308 = true := by
  decide

def missing9309 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13979666650008387584
theorem maskCheck9309 :
    checkMaskFor missing9309 StrongPackedBucketN12A3Shard072.record9309 = true := by
  decide

def missing9310 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14412012214235955200
theorem maskCheck9310 :
    checkMaskFor missing9310 StrongPackedBucketN12A3Shard072.record9310 = true := by
  decide

def missing9311 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18555323871416811520
theorem maskCheck9311 :
    checkMaskFor missing9311 StrongPackedBucketN12A3Shard072.record9311 = true := by
  decide

def missing9312 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18627381465454739456
theorem maskCheck9312 :
    checkMaskFor missing9312 StrongPackedBucketN12A3Shard072.record9312 = true := by
  decide

def missing9313 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18879583044587487232
theorem maskCheck9313 :
    checkMaskFor missing9313 StrongPackedBucketN12A3Shard072.record9313 = true := by
  decide

def missing9314 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19059727029682307072
theorem maskCheck9314 :
    checkMaskFor missing9314 StrongPackedBucketN12A3Shard072.record9314 = true := by
  decide

def missing9315 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20176619737270190080
theorem maskCheck9315 :
    checkMaskFor missing9315 StrongPackedBucketN12A3Shard072.record9315 = true := by
  decide

def missing9316 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23094952295806271488
theorem maskCheck9316 :
    checkMaskFor missing9316 StrongPackedBucketN12A3Shard072.record9316 = true := by
  decide

def missing9317 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23130981092825235456
theorem maskCheck9317 :
    checkMaskFor missing9317 StrongPackedBucketN12A3Shard072.record9317 = true := by
  decide

def missing9318 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23635384251090731008
theorem maskCheck9318 :
    checkMaskFor missing9318 StrongPackedBucketN12A3Shard072.record9318 = true := by
  decide

def missing9319 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27706638314233659392
theorem maskCheck9319 :
    checkMaskFor missing9319 StrongPackedBucketN12A3Shard072.record9319 = true := by
  decide

def missing9320 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27742667111252623360
theorem maskCheck9320 :
    checkMaskFor missing9320 StrongPackedBucketN12A3Shard072.record9320 = true := by
  decide

def missing9321 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27814724705290551296
theorem maskCheck9321 :
    checkMaskFor missing9321 StrongPackedBucketN12A3Shard072.record9321 = true := by
  decide

def missing9322 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28247070269518118912
theorem maskCheck9322 :
    checkMaskFor missing9322 StrongPackedBucketN12A3Shard072.record9322 = true := by
  decide

def missing9323 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32282295535642083328
theorem maskCheck9323 :
    checkMaskFor missing9323 StrongPackedBucketN12A3Shard072.record9323 = true := by
  decide

def missing9324 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18663586184334147584
theorem maskCheck9324 :
    checkMaskFor missing9324 StrongPackedBucketN12A3Shard072.record9324 = true := by
  decide

def missing9325 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23131157014685679616
theorem maskCheck9325 :
    checkMaskFor missing9325 StrongPackedBucketN12A3Shard072.record9325 = true := by
  decide

def missing9326 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 252976460759826432
theorem maskCheck9326 :
    checkMaskFor missing9326 StrongPackedBucketN12A3Shard072.record9326 = true := by
  decide

def missing9327 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 397091648835682304
theorem maskCheck9327 :
    checkMaskFor missing9327 StrongPackedBucketN12A3Shard072.record9327 = true := by
  decide

def missing9328 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 469149242873610240
theorem maskCheck9328 :
    checkMaskFor missing9328 StrongPackedBucketN12A3Shard072.record9328 = true := by
  decide

def missing9329 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 505178039892574208
theorem maskCheck9329 :
    checkMaskFor missing9329 StrongPackedBucketN12A3Shard072.record9329 = true := by
  decide

def missing9330 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5477152028509601792
theorem maskCheck9330 :
    checkMaskFor missing9330 StrongPackedBucketN12A3Shard072.record9330 = true := by
  decide

def missing9331 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6053612780813025280
theorem maskCheck9331 :
    checkMaskFor missing9331 StrongPackedBucketN12A3Shard072.record9331 = true := by
  decide

def missing9332 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9404290903576674304
theorem maskCheck9332 :
    checkMaskFor missing9332 StrongPackedBucketN12A3Shard072.record9332 = true := by
  decide

def missing9333 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9440319700595638272
theorem maskCheck9333 :
    checkMaskFor missing9333 StrongPackedBucketN12A3Shard072.record9333 = true := by
  decide

def missing9334 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9548406091652530176
theorem maskCheck9334 :
    checkMaskFor missing9334 StrongPackedBucketN12A3Shard072.record9334 = true := by
  decide

def missing9335 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9656492482709422080
theorem maskCheck9335 :
    checkMaskFor missing9335 StrongPackedBucketN12A3Shard072.record9335 = true := by
  decide

def missing9336 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10413097220107665408
theorem maskCheck9336 :
    checkMaskFor missing9336 StrongPackedBucketN12A3Shard072.record9336 = true := by
  decide

def missing9337 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13871861733928206336
theorem maskCheck9337 :
    checkMaskFor missing9337 StrongPackedBucketN12A3Shard072.record9337 = true := by
  decide

def missing9338 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13979948124985098240
theorem maskCheck9338 :
    checkMaskFor missing9338 StrongPackedBucketN12A3Shard072.record9338 = true := by
  decide

def missing9339 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14124063313060954112
theorem maskCheck9339 :
    checkMaskFor missing9339 StrongPackedBucketN12A3Shard072.record9339 = true := by
  decide

def missing9340 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14412293689212665856
theorem maskCheck9340 :
    checkMaskFor missing9340 StrongPackedBucketN12A3Shard072.record9340 = true := by
  decide

def missing9341 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14988754441516089344
theorem maskCheck9341 :
    checkMaskFor missing9341 StrongPackedBucketN12A3Shard072.record9341 = true := by
  decide

def missing9342 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18555605346393522176
theorem maskCheck9342 :
    checkMaskFor missing9342 StrongPackedBucketN12A3Shard072.record9342 = true := by
  decide

def missing9343 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18627662940431450112
theorem maskCheck9343 :
    checkMaskFor missing9343 StrongPackedBucketN12A3Shard072.record9343 = true := by
  decide

def missing9216_9217 : List (BitVec (edgeCount 12)) :=
  [missing9216]
abbrev records9216_9217 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9216]
theorem aligned9216_9217 :
    AlignedValid 12 3 missing9216_9217 records9216_9217 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9216
    maskCheck9216 AlignedValid.nil

def missing9217_9218 : List (BitVec (edgeCount 12)) :=
  [missing9217]
abbrev records9217_9218 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9217]
theorem aligned9217_9218 :
    AlignedValid 12 3 missing9217_9218 records9217_9218 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9217
    maskCheck9217 AlignedValid.nil

def missing9216_9218 : List (BitVec (edgeCount 12)) :=
  missing9216_9217 ++ missing9217_9218
abbrev records9216_9218 : List Blob :=
  records9216_9217 ++ records9217_9218
theorem aligned9216_9218 :
    AlignedValid 12 3 missing9216_9218 records9216_9218 :=
  aligned9216_9217.append aligned9217_9218

def missing9218_9219 : List (BitVec (edgeCount 12)) :=
  [missing9218]
abbrev records9218_9219 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9218]
theorem aligned9218_9219 :
    AlignedValid 12 3 missing9218_9219 records9218_9219 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9218
    maskCheck9218 AlignedValid.nil

def missing9219_9220 : List (BitVec (edgeCount 12)) :=
  [missing9219]
abbrev records9219_9220 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9219]
theorem aligned9219_9220 :
    AlignedValid 12 3 missing9219_9220 records9219_9220 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9219
    maskCheck9219 AlignedValid.nil

def missing9218_9220 : List (BitVec (edgeCount 12)) :=
  missing9218_9219 ++ missing9219_9220
abbrev records9218_9220 : List Blob :=
  records9218_9219 ++ records9219_9220
theorem aligned9218_9220 :
    AlignedValid 12 3 missing9218_9220 records9218_9220 :=
  aligned9218_9219.append aligned9219_9220

def missing9216_9220 : List (BitVec (edgeCount 12)) :=
  missing9216_9218 ++ missing9218_9220
abbrev records9216_9220 : List Blob :=
  records9216_9218 ++ records9218_9220
theorem aligned9216_9220 :
    AlignedValid 12 3 missing9216_9220 records9216_9220 :=
  aligned9216_9218.append aligned9218_9220

def missing9220_9221 : List (BitVec (edgeCount 12)) :=
  [missing9220]
abbrev records9220_9221 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9220]
theorem aligned9220_9221 :
    AlignedValid 12 3 missing9220_9221 records9220_9221 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9220
    maskCheck9220 AlignedValid.nil

def missing9221_9222 : List (BitVec (edgeCount 12)) :=
  [missing9221]
abbrev records9221_9222 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9221]
theorem aligned9221_9222 :
    AlignedValid 12 3 missing9221_9222 records9221_9222 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9221
    maskCheck9221 AlignedValid.nil

def missing9220_9222 : List (BitVec (edgeCount 12)) :=
  missing9220_9221 ++ missing9221_9222
abbrev records9220_9222 : List Blob :=
  records9220_9221 ++ records9221_9222
theorem aligned9220_9222 :
    AlignedValid 12 3 missing9220_9222 records9220_9222 :=
  aligned9220_9221.append aligned9221_9222

def missing9222_9223 : List (BitVec (edgeCount 12)) :=
  [missing9222]
abbrev records9222_9223 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9222]
theorem aligned9222_9223 :
    AlignedValid 12 3 missing9222_9223 records9222_9223 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9222
    maskCheck9222 AlignedValid.nil

def missing9223_9224 : List (BitVec (edgeCount 12)) :=
  [missing9223]
abbrev records9223_9224 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9223]
theorem aligned9223_9224 :
    AlignedValid 12 3 missing9223_9224 records9223_9224 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9223
    maskCheck9223 AlignedValid.nil

def missing9222_9224 : List (BitVec (edgeCount 12)) :=
  missing9222_9223 ++ missing9223_9224
abbrev records9222_9224 : List Blob :=
  records9222_9223 ++ records9223_9224
theorem aligned9222_9224 :
    AlignedValid 12 3 missing9222_9224 records9222_9224 :=
  aligned9222_9223.append aligned9223_9224

def missing9220_9224 : List (BitVec (edgeCount 12)) :=
  missing9220_9222 ++ missing9222_9224
abbrev records9220_9224 : List Blob :=
  records9220_9222 ++ records9222_9224
theorem aligned9220_9224 :
    AlignedValid 12 3 missing9220_9224 records9220_9224 :=
  aligned9220_9222.append aligned9222_9224

def missing9216_9224 : List (BitVec (edgeCount 12)) :=
  missing9216_9220 ++ missing9220_9224
abbrev records9216_9224 : List Blob :=
  records9216_9220 ++ records9220_9224
theorem aligned9216_9224 :
    AlignedValid 12 3 missing9216_9224 records9216_9224 :=
  aligned9216_9220.append aligned9220_9224

def missing9224_9225 : List (BitVec (edgeCount 12)) :=
  [missing9224]
abbrev records9224_9225 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9224]
theorem aligned9224_9225 :
    AlignedValid 12 3 missing9224_9225 records9224_9225 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9224
    maskCheck9224 AlignedValid.nil

def missing9225_9226 : List (BitVec (edgeCount 12)) :=
  [missing9225]
abbrev records9225_9226 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9225]
theorem aligned9225_9226 :
    AlignedValid 12 3 missing9225_9226 records9225_9226 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9225
    maskCheck9225 AlignedValid.nil

def missing9224_9226 : List (BitVec (edgeCount 12)) :=
  missing9224_9225 ++ missing9225_9226
abbrev records9224_9226 : List Blob :=
  records9224_9225 ++ records9225_9226
theorem aligned9224_9226 :
    AlignedValid 12 3 missing9224_9226 records9224_9226 :=
  aligned9224_9225.append aligned9225_9226

def missing9226_9227 : List (BitVec (edgeCount 12)) :=
  [missing9226]
abbrev records9226_9227 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9226]
theorem aligned9226_9227 :
    AlignedValid 12 3 missing9226_9227 records9226_9227 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9226
    maskCheck9226 AlignedValid.nil

def missing9227_9228 : List (BitVec (edgeCount 12)) :=
  [missing9227]
abbrev records9227_9228 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9227]
theorem aligned9227_9228 :
    AlignedValid 12 3 missing9227_9228 records9227_9228 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9227
    maskCheck9227 AlignedValid.nil

def missing9226_9228 : List (BitVec (edgeCount 12)) :=
  missing9226_9227 ++ missing9227_9228
abbrev records9226_9228 : List Blob :=
  records9226_9227 ++ records9227_9228
theorem aligned9226_9228 :
    AlignedValid 12 3 missing9226_9228 records9226_9228 :=
  aligned9226_9227.append aligned9227_9228

def missing9224_9228 : List (BitVec (edgeCount 12)) :=
  missing9224_9226 ++ missing9226_9228
abbrev records9224_9228 : List Blob :=
  records9224_9226 ++ records9226_9228
theorem aligned9224_9228 :
    AlignedValid 12 3 missing9224_9228 records9224_9228 :=
  aligned9224_9226.append aligned9226_9228

def missing9228_9229 : List (BitVec (edgeCount 12)) :=
  [missing9228]
abbrev records9228_9229 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9228]
theorem aligned9228_9229 :
    AlignedValid 12 3 missing9228_9229 records9228_9229 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9228
    maskCheck9228 AlignedValid.nil

def missing9229_9230 : List (BitVec (edgeCount 12)) :=
  [missing9229]
abbrev records9229_9230 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9229]
theorem aligned9229_9230 :
    AlignedValid 12 3 missing9229_9230 records9229_9230 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9229
    maskCheck9229 AlignedValid.nil

def missing9228_9230 : List (BitVec (edgeCount 12)) :=
  missing9228_9229 ++ missing9229_9230
abbrev records9228_9230 : List Blob :=
  records9228_9229 ++ records9229_9230
theorem aligned9228_9230 :
    AlignedValid 12 3 missing9228_9230 records9228_9230 :=
  aligned9228_9229.append aligned9229_9230

def missing9230_9231 : List (BitVec (edgeCount 12)) :=
  [missing9230]
abbrev records9230_9231 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9230]
theorem aligned9230_9231 :
    AlignedValid 12 3 missing9230_9231 records9230_9231 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9230
    maskCheck9230 AlignedValid.nil

def missing9231_9232 : List (BitVec (edgeCount 12)) :=
  [missing9231]
abbrev records9231_9232 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9231]
theorem aligned9231_9232 :
    AlignedValid 12 3 missing9231_9232 records9231_9232 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9231
    maskCheck9231 AlignedValid.nil

def missing9230_9232 : List (BitVec (edgeCount 12)) :=
  missing9230_9231 ++ missing9231_9232
abbrev records9230_9232 : List Blob :=
  records9230_9231 ++ records9231_9232
theorem aligned9230_9232 :
    AlignedValid 12 3 missing9230_9232 records9230_9232 :=
  aligned9230_9231.append aligned9231_9232

def missing9228_9232 : List (BitVec (edgeCount 12)) :=
  missing9228_9230 ++ missing9230_9232
abbrev records9228_9232 : List Blob :=
  records9228_9230 ++ records9230_9232
theorem aligned9228_9232 :
    AlignedValid 12 3 missing9228_9232 records9228_9232 :=
  aligned9228_9230.append aligned9230_9232

def missing9224_9232 : List (BitVec (edgeCount 12)) :=
  missing9224_9228 ++ missing9228_9232
abbrev records9224_9232 : List Blob :=
  records9224_9228 ++ records9228_9232
theorem aligned9224_9232 :
    AlignedValid 12 3 missing9224_9232 records9224_9232 :=
  aligned9224_9228.append aligned9228_9232

def missing9216_9232 : List (BitVec (edgeCount 12)) :=
  missing9216_9224 ++ missing9224_9232
abbrev records9216_9232 : List Blob :=
  records9216_9224 ++ records9224_9232
theorem aligned9216_9232 :
    AlignedValid 12 3 missing9216_9232 records9216_9232 :=
  aligned9216_9224.append aligned9224_9232

def missing9232_9233 : List (BitVec (edgeCount 12)) :=
  [missing9232]
abbrev records9232_9233 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9232]
theorem aligned9232_9233 :
    AlignedValid 12 3 missing9232_9233 records9232_9233 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9232
    maskCheck9232 AlignedValid.nil

def missing9233_9234 : List (BitVec (edgeCount 12)) :=
  [missing9233]
abbrev records9233_9234 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9233]
theorem aligned9233_9234 :
    AlignedValid 12 3 missing9233_9234 records9233_9234 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9233
    maskCheck9233 AlignedValid.nil

def missing9232_9234 : List (BitVec (edgeCount 12)) :=
  missing9232_9233 ++ missing9233_9234
abbrev records9232_9234 : List Blob :=
  records9232_9233 ++ records9233_9234
theorem aligned9232_9234 :
    AlignedValid 12 3 missing9232_9234 records9232_9234 :=
  aligned9232_9233.append aligned9233_9234

def missing9234_9235 : List (BitVec (edgeCount 12)) :=
  [missing9234]
abbrev records9234_9235 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9234]
theorem aligned9234_9235 :
    AlignedValid 12 3 missing9234_9235 records9234_9235 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9234
    maskCheck9234 AlignedValid.nil

def missing9235_9236 : List (BitVec (edgeCount 12)) :=
  [missing9235]
abbrev records9235_9236 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9235]
theorem aligned9235_9236 :
    AlignedValid 12 3 missing9235_9236 records9235_9236 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9235
    maskCheck9235 AlignedValid.nil

def missing9234_9236 : List (BitVec (edgeCount 12)) :=
  missing9234_9235 ++ missing9235_9236
abbrev records9234_9236 : List Blob :=
  records9234_9235 ++ records9235_9236
theorem aligned9234_9236 :
    AlignedValid 12 3 missing9234_9236 records9234_9236 :=
  aligned9234_9235.append aligned9235_9236

def missing9232_9236 : List (BitVec (edgeCount 12)) :=
  missing9232_9234 ++ missing9234_9236
abbrev records9232_9236 : List Blob :=
  records9232_9234 ++ records9234_9236
theorem aligned9232_9236 :
    AlignedValid 12 3 missing9232_9236 records9232_9236 :=
  aligned9232_9234.append aligned9234_9236

def missing9236_9237 : List (BitVec (edgeCount 12)) :=
  [missing9236]
abbrev records9236_9237 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9236]
theorem aligned9236_9237 :
    AlignedValid 12 3 missing9236_9237 records9236_9237 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9236
    maskCheck9236 AlignedValid.nil

def missing9237_9238 : List (BitVec (edgeCount 12)) :=
  [missing9237]
abbrev records9237_9238 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9237]
theorem aligned9237_9238 :
    AlignedValid 12 3 missing9237_9238 records9237_9238 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9237
    maskCheck9237 AlignedValid.nil

def missing9236_9238 : List (BitVec (edgeCount 12)) :=
  missing9236_9237 ++ missing9237_9238
abbrev records9236_9238 : List Blob :=
  records9236_9237 ++ records9237_9238
theorem aligned9236_9238 :
    AlignedValid 12 3 missing9236_9238 records9236_9238 :=
  aligned9236_9237.append aligned9237_9238

def missing9238_9239 : List (BitVec (edgeCount 12)) :=
  [missing9238]
abbrev records9238_9239 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9238]
theorem aligned9238_9239 :
    AlignedValid 12 3 missing9238_9239 records9238_9239 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9238
    maskCheck9238 AlignedValid.nil

def missing9239_9240 : List (BitVec (edgeCount 12)) :=
  [missing9239]
abbrev records9239_9240 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9239]
theorem aligned9239_9240 :
    AlignedValid 12 3 missing9239_9240 records9239_9240 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9239
    maskCheck9239 AlignedValid.nil

def missing9238_9240 : List (BitVec (edgeCount 12)) :=
  missing9238_9239 ++ missing9239_9240
abbrev records9238_9240 : List Blob :=
  records9238_9239 ++ records9239_9240
theorem aligned9238_9240 :
    AlignedValid 12 3 missing9238_9240 records9238_9240 :=
  aligned9238_9239.append aligned9239_9240

def missing9236_9240 : List (BitVec (edgeCount 12)) :=
  missing9236_9238 ++ missing9238_9240
abbrev records9236_9240 : List Blob :=
  records9236_9238 ++ records9238_9240
theorem aligned9236_9240 :
    AlignedValid 12 3 missing9236_9240 records9236_9240 :=
  aligned9236_9238.append aligned9238_9240

def missing9232_9240 : List (BitVec (edgeCount 12)) :=
  missing9232_9236 ++ missing9236_9240
abbrev records9232_9240 : List Blob :=
  records9232_9236 ++ records9236_9240
theorem aligned9232_9240 :
    AlignedValid 12 3 missing9232_9240 records9232_9240 :=
  aligned9232_9236.append aligned9236_9240

def missing9240_9241 : List (BitVec (edgeCount 12)) :=
  [missing9240]
abbrev records9240_9241 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9240]
theorem aligned9240_9241 :
    AlignedValid 12 3 missing9240_9241 records9240_9241 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9240
    maskCheck9240 AlignedValid.nil

def missing9241_9242 : List (BitVec (edgeCount 12)) :=
  [missing9241]
abbrev records9241_9242 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9241]
theorem aligned9241_9242 :
    AlignedValid 12 3 missing9241_9242 records9241_9242 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9241
    maskCheck9241 AlignedValid.nil

def missing9240_9242 : List (BitVec (edgeCount 12)) :=
  missing9240_9241 ++ missing9241_9242
abbrev records9240_9242 : List Blob :=
  records9240_9241 ++ records9241_9242
theorem aligned9240_9242 :
    AlignedValid 12 3 missing9240_9242 records9240_9242 :=
  aligned9240_9241.append aligned9241_9242

def missing9242_9243 : List (BitVec (edgeCount 12)) :=
  [missing9242]
abbrev records9242_9243 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9242]
theorem aligned9242_9243 :
    AlignedValid 12 3 missing9242_9243 records9242_9243 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9242
    maskCheck9242 AlignedValid.nil

def missing9243_9244 : List (BitVec (edgeCount 12)) :=
  [missing9243]
abbrev records9243_9244 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9243]
theorem aligned9243_9244 :
    AlignedValid 12 3 missing9243_9244 records9243_9244 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9243
    maskCheck9243 AlignedValid.nil

def missing9242_9244 : List (BitVec (edgeCount 12)) :=
  missing9242_9243 ++ missing9243_9244
abbrev records9242_9244 : List Blob :=
  records9242_9243 ++ records9243_9244
theorem aligned9242_9244 :
    AlignedValid 12 3 missing9242_9244 records9242_9244 :=
  aligned9242_9243.append aligned9243_9244

def missing9240_9244 : List (BitVec (edgeCount 12)) :=
  missing9240_9242 ++ missing9242_9244
abbrev records9240_9244 : List Blob :=
  records9240_9242 ++ records9242_9244
theorem aligned9240_9244 :
    AlignedValid 12 3 missing9240_9244 records9240_9244 :=
  aligned9240_9242.append aligned9242_9244

def missing9244_9245 : List (BitVec (edgeCount 12)) :=
  [missing9244]
abbrev records9244_9245 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9244]
theorem aligned9244_9245 :
    AlignedValid 12 3 missing9244_9245 records9244_9245 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9244
    maskCheck9244 AlignedValid.nil

def missing9245_9246 : List (BitVec (edgeCount 12)) :=
  [missing9245]
abbrev records9245_9246 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9245]
theorem aligned9245_9246 :
    AlignedValid 12 3 missing9245_9246 records9245_9246 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9245
    maskCheck9245 AlignedValid.nil

def missing9244_9246 : List (BitVec (edgeCount 12)) :=
  missing9244_9245 ++ missing9245_9246
abbrev records9244_9246 : List Blob :=
  records9244_9245 ++ records9245_9246
theorem aligned9244_9246 :
    AlignedValid 12 3 missing9244_9246 records9244_9246 :=
  aligned9244_9245.append aligned9245_9246

def missing9246_9247 : List (BitVec (edgeCount 12)) :=
  [missing9246]
abbrev records9246_9247 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9246]
theorem aligned9246_9247 :
    AlignedValid 12 3 missing9246_9247 records9246_9247 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9246
    maskCheck9246 AlignedValid.nil

def missing9247_9248 : List (BitVec (edgeCount 12)) :=
  [missing9247]
abbrev records9247_9248 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9247]
theorem aligned9247_9248 :
    AlignedValid 12 3 missing9247_9248 records9247_9248 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9247
    maskCheck9247 AlignedValid.nil

def missing9246_9248 : List (BitVec (edgeCount 12)) :=
  missing9246_9247 ++ missing9247_9248
abbrev records9246_9248 : List Blob :=
  records9246_9247 ++ records9247_9248
theorem aligned9246_9248 :
    AlignedValid 12 3 missing9246_9248 records9246_9248 :=
  aligned9246_9247.append aligned9247_9248

def missing9244_9248 : List (BitVec (edgeCount 12)) :=
  missing9244_9246 ++ missing9246_9248
abbrev records9244_9248 : List Blob :=
  records9244_9246 ++ records9246_9248
theorem aligned9244_9248 :
    AlignedValid 12 3 missing9244_9248 records9244_9248 :=
  aligned9244_9246.append aligned9246_9248

def missing9240_9248 : List (BitVec (edgeCount 12)) :=
  missing9240_9244 ++ missing9244_9248
abbrev records9240_9248 : List Blob :=
  records9240_9244 ++ records9244_9248
theorem aligned9240_9248 :
    AlignedValid 12 3 missing9240_9248 records9240_9248 :=
  aligned9240_9244.append aligned9244_9248

def missing9232_9248 : List (BitVec (edgeCount 12)) :=
  missing9232_9240 ++ missing9240_9248
abbrev records9232_9248 : List Blob :=
  records9232_9240 ++ records9240_9248
theorem aligned9232_9248 :
    AlignedValid 12 3 missing9232_9248 records9232_9248 :=
  aligned9232_9240.append aligned9240_9248

def missing9216_9248 : List (BitVec (edgeCount 12)) :=
  missing9216_9232 ++ missing9232_9248
abbrev records9216_9248 : List Blob :=
  records9216_9232 ++ records9232_9248
theorem aligned9216_9248 :
    AlignedValid 12 3 missing9216_9248 records9216_9248 :=
  aligned9216_9232.append aligned9232_9248

def missing9248_9249 : List (BitVec (edgeCount 12)) :=
  [missing9248]
abbrev records9248_9249 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9248]
theorem aligned9248_9249 :
    AlignedValid 12 3 missing9248_9249 records9248_9249 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9248
    maskCheck9248 AlignedValid.nil

def missing9249_9250 : List (BitVec (edgeCount 12)) :=
  [missing9249]
abbrev records9249_9250 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9249]
theorem aligned9249_9250 :
    AlignedValid 12 3 missing9249_9250 records9249_9250 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9249
    maskCheck9249 AlignedValid.nil

def missing9248_9250 : List (BitVec (edgeCount 12)) :=
  missing9248_9249 ++ missing9249_9250
abbrev records9248_9250 : List Blob :=
  records9248_9249 ++ records9249_9250
theorem aligned9248_9250 :
    AlignedValid 12 3 missing9248_9250 records9248_9250 :=
  aligned9248_9249.append aligned9249_9250

def missing9250_9251 : List (BitVec (edgeCount 12)) :=
  [missing9250]
abbrev records9250_9251 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9250]
theorem aligned9250_9251 :
    AlignedValid 12 3 missing9250_9251 records9250_9251 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9250
    maskCheck9250 AlignedValid.nil

def missing9251_9252 : List (BitVec (edgeCount 12)) :=
  [missing9251]
abbrev records9251_9252 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9251]
theorem aligned9251_9252 :
    AlignedValid 12 3 missing9251_9252 records9251_9252 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9251
    maskCheck9251 AlignedValid.nil

def missing9250_9252 : List (BitVec (edgeCount 12)) :=
  missing9250_9251 ++ missing9251_9252
abbrev records9250_9252 : List Blob :=
  records9250_9251 ++ records9251_9252
theorem aligned9250_9252 :
    AlignedValid 12 3 missing9250_9252 records9250_9252 :=
  aligned9250_9251.append aligned9251_9252

def missing9248_9252 : List (BitVec (edgeCount 12)) :=
  missing9248_9250 ++ missing9250_9252
abbrev records9248_9252 : List Blob :=
  records9248_9250 ++ records9250_9252
theorem aligned9248_9252 :
    AlignedValid 12 3 missing9248_9252 records9248_9252 :=
  aligned9248_9250.append aligned9250_9252

def missing9252_9253 : List (BitVec (edgeCount 12)) :=
  [missing9252]
abbrev records9252_9253 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9252]
theorem aligned9252_9253 :
    AlignedValid 12 3 missing9252_9253 records9252_9253 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9252
    maskCheck9252 AlignedValid.nil

def missing9253_9254 : List (BitVec (edgeCount 12)) :=
  [missing9253]
abbrev records9253_9254 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9253]
theorem aligned9253_9254 :
    AlignedValid 12 3 missing9253_9254 records9253_9254 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9253
    maskCheck9253 AlignedValid.nil

def missing9252_9254 : List (BitVec (edgeCount 12)) :=
  missing9252_9253 ++ missing9253_9254
abbrev records9252_9254 : List Blob :=
  records9252_9253 ++ records9253_9254
theorem aligned9252_9254 :
    AlignedValid 12 3 missing9252_9254 records9252_9254 :=
  aligned9252_9253.append aligned9253_9254

def missing9254_9255 : List (BitVec (edgeCount 12)) :=
  [missing9254]
abbrev records9254_9255 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9254]
theorem aligned9254_9255 :
    AlignedValid 12 3 missing9254_9255 records9254_9255 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9254
    maskCheck9254 AlignedValid.nil

def missing9255_9256 : List (BitVec (edgeCount 12)) :=
  [missing9255]
abbrev records9255_9256 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9255]
theorem aligned9255_9256 :
    AlignedValid 12 3 missing9255_9256 records9255_9256 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9255
    maskCheck9255 AlignedValid.nil

def missing9254_9256 : List (BitVec (edgeCount 12)) :=
  missing9254_9255 ++ missing9255_9256
abbrev records9254_9256 : List Blob :=
  records9254_9255 ++ records9255_9256
theorem aligned9254_9256 :
    AlignedValid 12 3 missing9254_9256 records9254_9256 :=
  aligned9254_9255.append aligned9255_9256

def missing9252_9256 : List (BitVec (edgeCount 12)) :=
  missing9252_9254 ++ missing9254_9256
abbrev records9252_9256 : List Blob :=
  records9252_9254 ++ records9254_9256
theorem aligned9252_9256 :
    AlignedValid 12 3 missing9252_9256 records9252_9256 :=
  aligned9252_9254.append aligned9254_9256

def missing9248_9256 : List (BitVec (edgeCount 12)) :=
  missing9248_9252 ++ missing9252_9256
abbrev records9248_9256 : List Blob :=
  records9248_9252 ++ records9252_9256
theorem aligned9248_9256 :
    AlignedValid 12 3 missing9248_9256 records9248_9256 :=
  aligned9248_9252.append aligned9252_9256

def missing9256_9257 : List (BitVec (edgeCount 12)) :=
  [missing9256]
abbrev records9256_9257 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9256]
theorem aligned9256_9257 :
    AlignedValid 12 3 missing9256_9257 records9256_9257 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9256
    maskCheck9256 AlignedValid.nil

def missing9257_9258 : List (BitVec (edgeCount 12)) :=
  [missing9257]
abbrev records9257_9258 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9257]
theorem aligned9257_9258 :
    AlignedValid 12 3 missing9257_9258 records9257_9258 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9257
    maskCheck9257 AlignedValid.nil

def missing9256_9258 : List (BitVec (edgeCount 12)) :=
  missing9256_9257 ++ missing9257_9258
abbrev records9256_9258 : List Blob :=
  records9256_9257 ++ records9257_9258
theorem aligned9256_9258 :
    AlignedValid 12 3 missing9256_9258 records9256_9258 :=
  aligned9256_9257.append aligned9257_9258

def missing9258_9259 : List (BitVec (edgeCount 12)) :=
  [missing9258]
abbrev records9258_9259 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9258]
theorem aligned9258_9259 :
    AlignedValid 12 3 missing9258_9259 records9258_9259 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9258
    maskCheck9258 AlignedValid.nil

def missing9259_9260 : List (BitVec (edgeCount 12)) :=
  [missing9259]
abbrev records9259_9260 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9259]
theorem aligned9259_9260 :
    AlignedValid 12 3 missing9259_9260 records9259_9260 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9259
    maskCheck9259 AlignedValid.nil

def missing9258_9260 : List (BitVec (edgeCount 12)) :=
  missing9258_9259 ++ missing9259_9260
abbrev records9258_9260 : List Blob :=
  records9258_9259 ++ records9259_9260
theorem aligned9258_9260 :
    AlignedValid 12 3 missing9258_9260 records9258_9260 :=
  aligned9258_9259.append aligned9259_9260

def missing9256_9260 : List (BitVec (edgeCount 12)) :=
  missing9256_9258 ++ missing9258_9260
abbrev records9256_9260 : List Blob :=
  records9256_9258 ++ records9258_9260
theorem aligned9256_9260 :
    AlignedValid 12 3 missing9256_9260 records9256_9260 :=
  aligned9256_9258.append aligned9258_9260

def missing9260_9261 : List (BitVec (edgeCount 12)) :=
  [missing9260]
abbrev records9260_9261 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9260]
theorem aligned9260_9261 :
    AlignedValid 12 3 missing9260_9261 records9260_9261 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9260
    maskCheck9260 AlignedValid.nil

def missing9261_9262 : List (BitVec (edgeCount 12)) :=
  [missing9261]
abbrev records9261_9262 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9261]
theorem aligned9261_9262 :
    AlignedValid 12 3 missing9261_9262 records9261_9262 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9261
    maskCheck9261 AlignedValid.nil

def missing9260_9262 : List (BitVec (edgeCount 12)) :=
  missing9260_9261 ++ missing9261_9262
abbrev records9260_9262 : List Blob :=
  records9260_9261 ++ records9261_9262
theorem aligned9260_9262 :
    AlignedValid 12 3 missing9260_9262 records9260_9262 :=
  aligned9260_9261.append aligned9261_9262

def missing9262_9263 : List (BitVec (edgeCount 12)) :=
  [missing9262]
abbrev records9262_9263 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9262]
theorem aligned9262_9263 :
    AlignedValid 12 3 missing9262_9263 records9262_9263 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9262
    maskCheck9262 AlignedValid.nil

def missing9263_9264 : List (BitVec (edgeCount 12)) :=
  [missing9263]
abbrev records9263_9264 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9263]
theorem aligned9263_9264 :
    AlignedValid 12 3 missing9263_9264 records9263_9264 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9263
    maskCheck9263 AlignedValid.nil

def missing9262_9264 : List (BitVec (edgeCount 12)) :=
  missing9262_9263 ++ missing9263_9264
abbrev records9262_9264 : List Blob :=
  records9262_9263 ++ records9263_9264
theorem aligned9262_9264 :
    AlignedValid 12 3 missing9262_9264 records9262_9264 :=
  aligned9262_9263.append aligned9263_9264

def missing9260_9264 : List (BitVec (edgeCount 12)) :=
  missing9260_9262 ++ missing9262_9264
abbrev records9260_9264 : List Blob :=
  records9260_9262 ++ records9262_9264
theorem aligned9260_9264 :
    AlignedValid 12 3 missing9260_9264 records9260_9264 :=
  aligned9260_9262.append aligned9262_9264

def missing9256_9264 : List (BitVec (edgeCount 12)) :=
  missing9256_9260 ++ missing9260_9264
abbrev records9256_9264 : List Blob :=
  records9256_9260 ++ records9260_9264
theorem aligned9256_9264 :
    AlignedValid 12 3 missing9256_9264 records9256_9264 :=
  aligned9256_9260.append aligned9260_9264

def missing9248_9264 : List (BitVec (edgeCount 12)) :=
  missing9248_9256 ++ missing9256_9264
abbrev records9248_9264 : List Blob :=
  records9248_9256 ++ records9256_9264
theorem aligned9248_9264 :
    AlignedValid 12 3 missing9248_9264 records9248_9264 :=
  aligned9248_9256.append aligned9256_9264

def missing9264_9265 : List (BitVec (edgeCount 12)) :=
  [missing9264]
abbrev records9264_9265 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9264]
theorem aligned9264_9265 :
    AlignedValid 12 3 missing9264_9265 records9264_9265 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9264
    maskCheck9264 AlignedValid.nil

def missing9265_9266 : List (BitVec (edgeCount 12)) :=
  [missing9265]
abbrev records9265_9266 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9265]
theorem aligned9265_9266 :
    AlignedValid 12 3 missing9265_9266 records9265_9266 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9265
    maskCheck9265 AlignedValid.nil

def missing9264_9266 : List (BitVec (edgeCount 12)) :=
  missing9264_9265 ++ missing9265_9266
abbrev records9264_9266 : List Blob :=
  records9264_9265 ++ records9265_9266
theorem aligned9264_9266 :
    AlignedValid 12 3 missing9264_9266 records9264_9266 :=
  aligned9264_9265.append aligned9265_9266

def missing9266_9267 : List (BitVec (edgeCount 12)) :=
  [missing9266]
abbrev records9266_9267 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9266]
theorem aligned9266_9267 :
    AlignedValid 12 3 missing9266_9267 records9266_9267 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9266
    maskCheck9266 AlignedValid.nil

def missing9267_9268 : List (BitVec (edgeCount 12)) :=
  [missing9267]
abbrev records9267_9268 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9267]
theorem aligned9267_9268 :
    AlignedValid 12 3 missing9267_9268 records9267_9268 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9267
    maskCheck9267 AlignedValid.nil

def missing9266_9268 : List (BitVec (edgeCount 12)) :=
  missing9266_9267 ++ missing9267_9268
abbrev records9266_9268 : List Blob :=
  records9266_9267 ++ records9267_9268
theorem aligned9266_9268 :
    AlignedValid 12 3 missing9266_9268 records9266_9268 :=
  aligned9266_9267.append aligned9267_9268

def missing9264_9268 : List (BitVec (edgeCount 12)) :=
  missing9264_9266 ++ missing9266_9268
abbrev records9264_9268 : List Blob :=
  records9264_9266 ++ records9266_9268
theorem aligned9264_9268 :
    AlignedValid 12 3 missing9264_9268 records9264_9268 :=
  aligned9264_9266.append aligned9266_9268

def missing9268_9269 : List (BitVec (edgeCount 12)) :=
  [missing9268]
abbrev records9268_9269 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9268]
theorem aligned9268_9269 :
    AlignedValid 12 3 missing9268_9269 records9268_9269 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9268
    maskCheck9268 AlignedValid.nil

def missing9269_9270 : List (BitVec (edgeCount 12)) :=
  [missing9269]
abbrev records9269_9270 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9269]
theorem aligned9269_9270 :
    AlignedValid 12 3 missing9269_9270 records9269_9270 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9269
    maskCheck9269 AlignedValid.nil

def missing9268_9270 : List (BitVec (edgeCount 12)) :=
  missing9268_9269 ++ missing9269_9270
abbrev records9268_9270 : List Blob :=
  records9268_9269 ++ records9269_9270
theorem aligned9268_9270 :
    AlignedValid 12 3 missing9268_9270 records9268_9270 :=
  aligned9268_9269.append aligned9269_9270

def missing9270_9271 : List (BitVec (edgeCount 12)) :=
  [missing9270]
abbrev records9270_9271 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9270]
theorem aligned9270_9271 :
    AlignedValid 12 3 missing9270_9271 records9270_9271 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9270
    maskCheck9270 AlignedValid.nil

def missing9271_9272 : List (BitVec (edgeCount 12)) :=
  [missing9271]
abbrev records9271_9272 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9271]
theorem aligned9271_9272 :
    AlignedValid 12 3 missing9271_9272 records9271_9272 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9271
    maskCheck9271 AlignedValid.nil

def missing9270_9272 : List (BitVec (edgeCount 12)) :=
  missing9270_9271 ++ missing9271_9272
abbrev records9270_9272 : List Blob :=
  records9270_9271 ++ records9271_9272
theorem aligned9270_9272 :
    AlignedValid 12 3 missing9270_9272 records9270_9272 :=
  aligned9270_9271.append aligned9271_9272

def missing9268_9272 : List (BitVec (edgeCount 12)) :=
  missing9268_9270 ++ missing9270_9272
abbrev records9268_9272 : List Blob :=
  records9268_9270 ++ records9270_9272
theorem aligned9268_9272 :
    AlignedValid 12 3 missing9268_9272 records9268_9272 :=
  aligned9268_9270.append aligned9270_9272

def missing9264_9272 : List (BitVec (edgeCount 12)) :=
  missing9264_9268 ++ missing9268_9272
abbrev records9264_9272 : List Blob :=
  records9264_9268 ++ records9268_9272
theorem aligned9264_9272 :
    AlignedValid 12 3 missing9264_9272 records9264_9272 :=
  aligned9264_9268.append aligned9268_9272

def missing9272_9273 : List (BitVec (edgeCount 12)) :=
  [missing9272]
abbrev records9272_9273 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9272]
theorem aligned9272_9273 :
    AlignedValid 12 3 missing9272_9273 records9272_9273 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9272
    maskCheck9272 AlignedValid.nil

def missing9273_9274 : List (BitVec (edgeCount 12)) :=
  [missing9273]
abbrev records9273_9274 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9273]
theorem aligned9273_9274 :
    AlignedValid 12 3 missing9273_9274 records9273_9274 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9273
    maskCheck9273 AlignedValid.nil

def missing9272_9274 : List (BitVec (edgeCount 12)) :=
  missing9272_9273 ++ missing9273_9274
abbrev records9272_9274 : List Blob :=
  records9272_9273 ++ records9273_9274
theorem aligned9272_9274 :
    AlignedValid 12 3 missing9272_9274 records9272_9274 :=
  aligned9272_9273.append aligned9273_9274

def missing9274_9275 : List (BitVec (edgeCount 12)) :=
  [missing9274]
abbrev records9274_9275 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9274]
theorem aligned9274_9275 :
    AlignedValid 12 3 missing9274_9275 records9274_9275 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9274
    maskCheck9274 AlignedValid.nil

def missing9275_9276 : List (BitVec (edgeCount 12)) :=
  [missing9275]
abbrev records9275_9276 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9275]
theorem aligned9275_9276 :
    AlignedValid 12 3 missing9275_9276 records9275_9276 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9275
    maskCheck9275 AlignedValid.nil

def missing9274_9276 : List (BitVec (edgeCount 12)) :=
  missing9274_9275 ++ missing9275_9276
abbrev records9274_9276 : List Blob :=
  records9274_9275 ++ records9275_9276
theorem aligned9274_9276 :
    AlignedValid 12 3 missing9274_9276 records9274_9276 :=
  aligned9274_9275.append aligned9275_9276

def missing9272_9276 : List (BitVec (edgeCount 12)) :=
  missing9272_9274 ++ missing9274_9276
abbrev records9272_9276 : List Blob :=
  records9272_9274 ++ records9274_9276
theorem aligned9272_9276 :
    AlignedValid 12 3 missing9272_9276 records9272_9276 :=
  aligned9272_9274.append aligned9274_9276

def missing9276_9277 : List (BitVec (edgeCount 12)) :=
  [missing9276]
abbrev records9276_9277 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9276]
theorem aligned9276_9277 :
    AlignedValid 12 3 missing9276_9277 records9276_9277 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9276
    maskCheck9276 AlignedValid.nil

def missing9277_9278 : List (BitVec (edgeCount 12)) :=
  [missing9277]
abbrev records9277_9278 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9277]
theorem aligned9277_9278 :
    AlignedValid 12 3 missing9277_9278 records9277_9278 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9277
    maskCheck9277 AlignedValid.nil

def missing9276_9278 : List (BitVec (edgeCount 12)) :=
  missing9276_9277 ++ missing9277_9278
abbrev records9276_9278 : List Blob :=
  records9276_9277 ++ records9277_9278
theorem aligned9276_9278 :
    AlignedValid 12 3 missing9276_9278 records9276_9278 :=
  aligned9276_9277.append aligned9277_9278

def missing9278_9279 : List (BitVec (edgeCount 12)) :=
  [missing9278]
abbrev records9278_9279 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9278]
theorem aligned9278_9279 :
    AlignedValid 12 3 missing9278_9279 records9278_9279 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9278
    maskCheck9278 AlignedValid.nil

def missing9279_9280 : List (BitVec (edgeCount 12)) :=
  [missing9279]
abbrev records9279_9280 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9279]
theorem aligned9279_9280 :
    AlignedValid 12 3 missing9279_9280 records9279_9280 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9279
    maskCheck9279 AlignedValid.nil

def missing9278_9280 : List (BitVec (edgeCount 12)) :=
  missing9278_9279 ++ missing9279_9280
abbrev records9278_9280 : List Blob :=
  records9278_9279 ++ records9279_9280
theorem aligned9278_9280 :
    AlignedValid 12 3 missing9278_9280 records9278_9280 :=
  aligned9278_9279.append aligned9279_9280

def missing9276_9280 : List (BitVec (edgeCount 12)) :=
  missing9276_9278 ++ missing9278_9280
abbrev records9276_9280 : List Blob :=
  records9276_9278 ++ records9278_9280
theorem aligned9276_9280 :
    AlignedValid 12 3 missing9276_9280 records9276_9280 :=
  aligned9276_9278.append aligned9278_9280

def missing9272_9280 : List (BitVec (edgeCount 12)) :=
  missing9272_9276 ++ missing9276_9280
abbrev records9272_9280 : List Blob :=
  records9272_9276 ++ records9276_9280
theorem aligned9272_9280 :
    AlignedValid 12 3 missing9272_9280 records9272_9280 :=
  aligned9272_9276.append aligned9276_9280

def missing9264_9280 : List (BitVec (edgeCount 12)) :=
  missing9264_9272 ++ missing9272_9280
abbrev records9264_9280 : List Blob :=
  records9264_9272 ++ records9272_9280
theorem aligned9264_9280 :
    AlignedValid 12 3 missing9264_9280 records9264_9280 :=
  aligned9264_9272.append aligned9272_9280

def missing9248_9280 : List (BitVec (edgeCount 12)) :=
  missing9248_9264 ++ missing9264_9280
abbrev records9248_9280 : List Blob :=
  records9248_9264 ++ records9264_9280
theorem aligned9248_9280 :
    AlignedValid 12 3 missing9248_9280 records9248_9280 :=
  aligned9248_9264.append aligned9264_9280

def missing9216_9280 : List (BitVec (edgeCount 12)) :=
  missing9216_9248 ++ missing9248_9280
abbrev records9216_9280 : List Blob :=
  records9216_9248 ++ records9248_9280
theorem aligned9216_9280 :
    AlignedValid 12 3 missing9216_9280 records9216_9280 :=
  aligned9216_9248.append aligned9248_9280

def missing9280_9281 : List (BitVec (edgeCount 12)) :=
  [missing9280]
abbrev records9280_9281 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9280]
theorem aligned9280_9281 :
    AlignedValid 12 3 missing9280_9281 records9280_9281 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9280
    maskCheck9280 AlignedValid.nil

def missing9281_9282 : List (BitVec (edgeCount 12)) :=
  [missing9281]
abbrev records9281_9282 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9281]
theorem aligned9281_9282 :
    AlignedValid 12 3 missing9281_9282 records9281_9282 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9281
    maskCheck9281 AlignedValid.nil

def missing9280_9282 : List (BitVec (edgeCount 12)) :=
  missing9280_9281 ++ missing9281_9282
abbrev records9280_9282 : List Blob :=
  records9280_9281 ++ records9281_9282
theorem aligned9280_9282 :
    AlignedValid 12 3 missing9280_9282 records9280_9282 :=
  aligned9280_9281.append aligned9281_9282

def missing9282_9283 : List (BitVec (edgeCount 12)) :=
  [missing9282]
abbrev records9282_9283 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9282]
theorem aligned9282_9283 :
    AlignedValid 12 3 missing9282_9283 records9282_9283 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9282
    maskCheck9282 AlignedValid.nil

def missing9283_9284 : List (BitVec (edgeCount 12)) :=
  [missing9283]
abbrev records9283_9284 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9283]
theorem aligned9283_9284 :
    AlignedValid 12 3 missing9283_9284 records9283_9284 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9283
    maskCheck9283 AlignedValid.nil

def missing9282_9284 : List (BitVec (edgeCount 12)) :=
  missing9282_9283 ++ missing9283_9284
abbrev records9282_9284 : List Blob :=
  records9282_9283 ++ records9283_9284
theorem aligned9282_9284 :
    AlignedValid 12 3 missing9282_9284 records9282_9284 :=
  aligned9282_9283.append aligned9283_9284

def missing9280_9284 : List (BitVec (edgeCount 12)) :=
  missing9280_9282 ++ missing9282_9284
abbrev records9280_9284 : List Blob :=
  records9280_9282 ++ records9282_9284
theorem aligned9280_9284 :
    AlignedValid 12 3 missing9280_9284 records9280_9284 :=
  aligned9280_9282.append aligned9282_9284

def missing9284_9285 : List (BitVec (edgeCount 12)) :=
  [missing9284]
abbrev records9284_9285 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9284]
theorem aligned9284_9285 :
    AlignedValid 12 3 missing9284_9285 records9284_9285 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9284
    maskCheck9284 AlignedValid.nil

def missing9285_9286 : List (BitVec (edgeCount 12)) :=
  [missing9285]
abbrev records9285_9286 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9285]
theorem aligned9285_9286 :
    AlignedValid 12 3 missing9285_9286 records9285_9286 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9285
    maskCheck9285 AlignedValid.nil

def missing9284_9286 : List (BitVec (edgeCount 12)) :=
  missing9284_9285 ++ missing9285_9286
abbrev records9284_9286 : List Blob :=
  records9284_9285 ++ records9285_9286
theorem aligned9284_9286 :
    AlignedValid 12 3 missing9284_9286 records9284_9286 :=
  aligned9284_9285.append aligned9285_9286

def missing9286_9287 : List (BitVec (edgeCount 12)) :=
  [missing9286]
abbrev records9286_9287 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9286]
theorem aligned9286_9287 :
    AlignedValid 12 3 missing9286_9287 records9286_9287 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9286
    maskCheck9286 AlignedValid.nil

def missing9287_9288 : List (BitVec (edgeCount 12)) :=
  [missing9287]
abbrev records9287_9288 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9287]
theorem aligned9287_9288 :
    AlignedValid 12 3 missing9287_9288 records9287_9288 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9287
    maskCheck9287 AlignedValid.nil

def missing9286_9288 : List (BitVec (edgeCount 12)) :=
  missing9286_9287 ++ missing9287_9288
abbrev records9286_9288 : List Blob :=
  records9286_9287 ++ records9287_9288
theorem aligned9286_9288 :
    AlignedValid 12 3 missing9286_9288 records9286_9288 :=
  aligned9286_9287.append aligned9287_9288

def missing9284_9288 : List (BitVec (edgeCount 12)) :=
  missing9284_9286 ++ missing9286_9288
abbrev records9284_9288 : List Blob :=
  records9284_9286 ++ records9286_9288
theorem aligned9284_9288 :
    AlignedValid 12 3 missing9284_9288 records9284_9288 :=
  aligned9284_9286.append aligned9286_9288

def missing9280_9288 : List (BitVec (edgeCount 12)) :=
  missing9280_9284 ++ missing9284_9288
abbrev records9280_9288 : List Blob :=
  records9280_9284 ++ records9284_9288
theorem aligned9280_9288 :
    AlignedValid 12 3 missing9280_9288 records9280_9288 :=
  aligned9280_9284.append aligned9284_9288

def missing9288_9289 : List (BitVec (edgeCount 12)) :=
  [missing9288]
abbrev records9288_9289 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9288]
theorem aligned9288_9289 :
    AlignedValid 12 3 missing9288_9289 records9288_9289 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9288
    maskCheck9288 AlignedValid.nil

def missing9289_9290 : List (BitVec (edgeCount 12)) :=
  [missing9289]
abbrev records9289_9290 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9289]
theorem aligned9289_9290 :
    AlignedValid 12 3 missing9289_9290 records9289_9290 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9289
    maskCheck9289 AlignedValid.nil

def missing9288_9290 : List (BitVec (edgeCount 12)) :=
  missing9288_9289 ++ missing9289_9290
abbrev records9288_9290 : List Blob :=
  records9288_9289 ++ records9289_9290
theorem aligned9288_9290 :
    AlignedValid 12 3 missing9288_9290 records9288_9290 :=
  aligned9288_9289.append aligned9289_9290

def missing9290_9291 : List (BitVec (edgeCount 12)) :=
  [missing9290]
abbrev records9290_9291 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9290]
theorem aligned9290_9291 :
    AlignedValid 12 3 missing9290_9291 records9290_9291 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9290
    maskCheck9290 AlignedValid.nil

def missing9291_9292 : List (BitVec (edgeCount 12)) :=
  [missing9291]
abbrev records9291_9292 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9291]
theorem aligned9291_9292 :
    AlignedValid 12 3 missing9291_9292 records9291_9292 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9291
    maskCheck9291 AlignedValid.nil

def missing9290_9292 : List (BitVec (edgeCount 12)) :=
  missing9290_9291 ++ missing9291_9292
abbrev records9290_9292 : List Blob :=
  records9290_9291 ++ records9291_9292
theorem aligned9290_9292 :
    AlignedValid 12 3 missing9290_9292 records9290_9292 :=
  aligned9290_9291.append aligned9291_9292

def missing9288_9292 : List (BitVec (edgeCount 12)) :=
  missing9288_9290 ++ missing9290_9292
abbrev records9288_9292 : List Blob :=
  records9288_9290 ++ records9290_9292
theorem aligned9288_9292 :
    AlignedValid 12 3 missing9288_9292 records9288_9292 :=
  aligned9288_9290.append aligned9290_9292

def missing9292_9293 : List (BitVec (edgeCount 12)) :=
  [missing9292]
abbrev records9292_9293 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9292]
theorem aligned9292_9293 :
    AlignedValid 12 3 missing9292_9293 records9292_9293 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9292
    maskCheck9292 AlignedValid.nil

def missing9293_9294 : List (BitVec (edgeCount 12)) :=
  [missing9293]
abbrev records9293_9294 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9293]
theorem aligned9293_9294 :
    AlignedValid 12 3 missing9293_9294 records9293_9294 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9293
    maskCheck9293 AlignedValid.nil

def missing9292_9294 : List (BitVec (edgeCount 12)) :=
  missing9292_9293 ++ missing9293_9294
abbrev records9292_9294 : List Blob :=
  records9292_9293 ++ records9293_9294
theorem aligned9292_9294 :
    AlignedValid 12 3 missing9292_9294 records9292_9294 :=
  aligned9292_9293.append aligned9293_9294

def missing9294_9295 : List (BitVec (edgeCount 12)) :=
  [missing9294]
abbrev records9294_9295 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9294]
theorem aligned9294_9295 :
    AlignedValid 12 3 missing9294_9295 records9294_9295 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9294
    maskCheck9294 AlignedValid.nil

def missing9295_9296 : List (BitVec (edgeCount 12)) :=
  [missing9295]
abbrev records9295_9296 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9295]
theorem aligned9295_9296 :
    AlignedValid 12 3 missing9295_9296 records9295_9296 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9295
    maskCheck9295 AlignedValid.nil

def missing9294_9296 : List (BitVec (edgeCount 12)) :=
  missing9294_9295 ++ missing9295_9296
abbrev records9294_9296 : List Blob :=
  records9294_9295 ++ records9295_9296
theorem aligned9294_9296 :
    AlignedValid 12 3 missing9294_9296 records9294_9296 :=
  aligned9294_9295.append aligned9295_9296

def missing9292_9296 : List (BitVec (edgeCount 12)) :=
  missing9292_9294 ++ missing9294_9296
abbrev records9292_9296 : List Blob :=
  records9292_9294 ++ records9294_9296
theorem aligned9292_9296 :
    AlignedValid 12 3 missing9292_9296 records9292_9296 :=
  aligned9292_9294.append aligned9294_9296

def missing9288_9296 : List (BitVec (edgeCount 12)) :=
  missing9288_9292 ++ missing9292_9296
abbrev records9288_9296 : List Blob :=
  records9288_9292 ++ records9292_9296
theorem aligned9288_9296 :
    AlignedValid 12 3 missing9288_9296 records9288_9296 :=
  aligned9288_9292.append aligned9292_9296

def missing9280_9296 : List (BitVec (edgeCount 12)) :=
  missing9280_9288 ++ missing9288_9296
abbrev records9280_9296 : List Blob :=
  records9280_9288 ++ records9288_9296
theorem aligned9280_9296 :
    AlignedValid 12 3 missing9280_9296 records9280_9296 :=
  aligned9280_9288.append aligned9288_9296

def missing9296_9297 : List (BitVec (edgeCount 12)) :=
  [missing9296]
abbrev records9296_9297 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9296]
theorem aligned9296_9297 :
    AlignedValid 12 3 missing9296_9297 records9296_9297 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9296
    maskCheck9296 AlignedValid.nil

def missing9297_9298 : List (BitVec (edgeCount 12)) :=
  [missing9297]
abbrev records9297_9298 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9297]
theorem aligned9297_9298 :
    AlignedValid 12 3 missing9297_9298 records9297_9298 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9297
    maskCheck9297 AlignedValid.nil

def missing9296_9298 : List (BitVec (edgeCount 12)) :=
  missing9296_9297 ++ missing9297_9298
abbrev records9296_9298 : List Blob :=
  records9296_9297 ++ records9297_9298
theorem aligned9296_9298 :
    AlignedValid 12 3 missing9296_9298 records9296_9298 :=
  aligned9296_9297.append aligned9297_9298

def missing9298_9299 : List (BitVec (edgeCount 12)) :=
  [missing9298]
abbrev records9298_9299 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9298]
theorem aligned9298_9299 :
    AlignedValid 12 3 missing9298_9299 records9298_9299 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9298
    maskCheck9298 AlignedValid.nil

def missing9299_9300 : List (BitVec (edgeCount 12)) :=
  [missing9299]
abbrev records9299_9300 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9299]
theorem aligned9299_9300 :
    AlignedValid 12 3 missing9299_9300 records9299_9300 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9299
    maskCheck9299 AlignedValid.nil

def missing9298_9300 : List (BitVec (edgeCount 12)) :=
  missing9298_9299 ++ missing9299_9300
abbrev records9298_9300 : List Blob :=
  records9298_9299 ++ records9299_9300
theorem aligned9298_9300 :
    AlignedValid 12 3 missing9298_9300 records9298_9300 :=
  aligned9298_9299.append aligned9299_9300

def missing9296_9300 : List (BitVec (edgeCount 12)) :=
  missing9296_9298 ++ missing9298_9300
abbrev records9296_9300 : List Blob :=
  records9296_9298 ++ records9298_9300
theorem aligned9296_9300 :
    AlignedValid 12 3 missing9296_9300 records9296_9300 :=
  aligned9296_9298.append aligned9298_9300

def missing9300_9301 : List (BitVec (edgeCount 12)) :=
  [missing9300]
abbrev records9300_9301 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9300]
theorem aligned9300_9301 :
    AlignedValid 12 3 missing9300_9301 records9300_9301 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9300
    maskCheck9300 AlignedValid.nil

def missing9301_9302 : List (BitVec (edgeCount 12)) :=
  [missing9301]
abbrev records9301_9302 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9301]
theorem aligned9301_9302 :
    AlignedValid 12 3 missing9301_9302 records9301_9302 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9301
    maskCheck9301 AlignedValid.nil

def missing9300_9302 : List (BitVec (edgeCount 12)) :=
  missing9300_9301 ++ missing9301_9302
abbrev records9300_9302 : List Blob :=
  records9300_9301 ++ records9301_9302
theorem aligned9300_9302 :
    AlignedValid 12 3 missing9300_9302 records9300_9302 :=
  aligned9300_9301.append aligned9301_9302

def missing9302_9303 : List (BitVec (edgeCount 12)) :=
  [missing9302]
abbrev records9302_9303 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9302]
theorem aligned9302_9303 :
    AlignedValid 12 3 missing9302_9303 records9302_9303 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9302
    maskCheck9302 AlignedValid.nil

def missing9303_9304 : List (BitVec (edgeCount 12)) :=
  [missing9303]
abbrev records9303_9304 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9303]
theorem aligned9303_9304 :
    AlignedValid 12 3 missing9303_9304 records9303_9304 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9303
    maskCheck9303 AlignedValid.nil

def missing9302_9304 : List (BitVec (edgeCount 12)) :=
  missing9302_9303 ++ missing9303_9304
abbrev records9302_9304 : List Blob :=
  records9302_9303 ++ records9303_9304
theorem aligned9302_9304 :
    AlignedValid 12 3 missing9302_9304 records9302_9304 :=
  aligned9302_9303.append aligned9303_9304

def missing9300_9304 : List (BitVec (edgeCount 12)) :=
  missing9300_9302 ++ missing9302_9304
abbrev records9300_9304 : List Blob :=
  records9300_9302 ++ records9302_9304
theorem aligned9300_9304 :
    AlignedValid 12 3 missing9300_9304 records9300_9304 :=
  aligned9300_9302.append aligned9302_9304

def missing9296_9304 : List (BitVec (edgeCount 12)) :=
  missing9296_9300 ++ missing9300_9304
abbrev records9296_9304 : List Blob :=
  records9296_9300 ++ records9300_9304
theorem aligned9296_9304 :
    AlignedValid 12 3 missing9296_9304 records9296_9304 :=
  aligned9296_9300.append aligned9300_9304

def missing9304_9305 : List (BitVec (edgeCount 12)) :=
  [missing9304]
abbrev records9304_9305 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9304]
theorem aligned9304_9305 :
    AlignedValid 12 3 missing9304_9305 records9304_9305 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9304
    maskCheck9304 AlignedValid.nil

def missing9305_9306 : List (BitVec (edgeCount 12)) :=
  [missing9305]
abbrev records9305_9306 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9305]
theorem aligned9305_9306 :
    AlignedValid 12 3 missing9305_9306 records9305_9306 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9305
    maskCheck9305 AlignedValid.nil

def missing9304_9306 : List (BitVec (edgeCount 12)) :=
  missing9304_9305 ++ missing9305_9306
abbrev records9304_9306 : List Blob :=
  records9304_9305 ++ records9305_9306
theorem aligned9304_9306 :
    AlignedValid 12 3 missing9304_9306 records9304_9306 :=
  aligned9304_9305.append aligned9305_9306

def missing9306_9307 : List (BitVec (edgeCount 12)) :=
  [missing9306]
abbrev records9306_9307 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9306]
theorem aligned9306_9307 :
    AlignedValid 12 3 missing9306_9307 records9306_9307 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9306
    maskCheck9306 AlignedValid.nil

def missing9307_9308 : List (BitVec (edgeCount 12)) :=
  [missing9307]
abbrev records9307_9308 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9307]
theorem aligned9307_9308 :
    AlignedValid 12 3 missing9307_9308 records9307_9308 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9307
    maskCheck9307 AlignedValid.nil

def missing9306_9308 : List (BitVec (edgeCount 12)) :=
  missing9306_9307 ++ missing9307_9308
abbrev records9306_9308 : List Blob :=
  records9306_9307 ++ records9307_9308
theorem aligned9306_9308 :
    AlignedValid 12 3 missing9306_9308 records9306_9308 :=
  aligned9306_9307.append aligned9307_9308

def missing9304_9308 : List (BitVec (edgeCount 12)) :=
  missing9304_9306 ++ missing9306_9308
abbrev records9304_9308 : List Blob :=
  records9304_9306 ++ records9306_9308
theorem aligned9304_9308 :
    AlignedValid 12 3 missing9304_9308 records9304_9308 :=
  aligned9304_9306.append aligned9306_9308

def missing9308_9309 : List (BitVec (edgeCount 12)) :=
  [missing9308]
abbrev records9308_9309 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9308]
theorem aligned9308_9309 :
    AlignedValid 12 3 missing9308_9309 records9308_9309 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9308
    maskCheck9308 AlignedValid.nil

def missing9309_9310 : List (BitVec (edgeCount 12)) :=
  [missing9309]
abbrev records9309_9310 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9309]
theorem aligned9309_9310 :
    AlignedValid 12 3 missing9309_9310 records9309_9310 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9309
    maskCheck9309 AlignedValid.nil

def missing9308_9310 : List (BitVec (edgeCount 12)) :=
  missing9308_9309 ++ missing9309_9310
abbrev records9308_9310 : List Blob :=
  records9308_9309 ++ records9309_9310
theorem aligned9308_9310 :
    AlignedValid 12 3 missing9308_9310 records9308_9310 :=
  aligned9308_9309.append aligned9309_9310

def missing9310_9311 : List (BitVec (edgeCount 12)) :=
  [missing9310]
abbrev records9310_9311 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9310]
theorem aligned9310_9311 :
    AlignedValid 12 3 missing9310_9311 records9310_9311 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9310
    maskCheck9310 AlignedValid.nil

def missing9311_9312 : List (BitVec (edgeCount 12)) :=
  [missing9311]
abbrev records9311_9312 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9311]
theorem aligned9311_9312 :
    AlignedValid 12 3 missing9311_9312 records9311_9312 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9311
    maskCheck9311 AlignedValid.nil

def missing9310_9312 : List (BitVec (edgeCount 12)) :=
  missing9310_9311 ++ missing9311_9312
abbrev records9310_9312 : List Blob :=
  records9310_9311 ++ records9311_9312
theorem aligned9310_9312 :
    AlignedValid 12 3 missing9310_9312 records9310_9312 :=
  aligned9310_9311.append aligned9311_9312

def missing9308_9312 : List (BitVec (edgeCount 12)) :=
  missing9308_9310 ++ missing9310_9312
abbrev records9308_9312 : List Blob :=
  records9308_9310 ++ records9310_9312
theorem aligned9308_9312 :
    AlignedValid 12 3 missing9308_9312 records9308_9312 :=
  aligned9308_9310.append aligned9310_9312

def missing9304_9312 : List (BitVec (edgeCount 12)) :=
  missing9304_9308 ++ missing9308_9312
abbrev records9304_9312 : List Blob :=
  records9304_9308 ++ records9308_9312
theorem aligned9304_9312 :
    AlignedValid 12 3 missing9304_9312 records9304_9312 :=
  aligned9304_9308.append aligned9308_9312

def missing9296_9312 : List (BitVec (edgeCount 12)) :=
  missing9296_9304 ++ missing9304_9312
abbrev records9296_9312 : List Blob :=
  records9296_9304 ++ records9304_9312
theorem aligned9296_9312 :
    AlignedValid 12 3 missing9296_9312 records9296_9312 :=
  aligned9296_9304.append aligned9304_9312

def missing9280_9312 : List (BitVec (edgeCount 12)) :=
  missing9280_9296 ++ missing9296_9312
abbrev records9280_9312 : List Blob :=
  records9280_9296 ++ records9296_9312
theorem aligned9280_9312 :
    AlignedValid 12 3 missing9280_9312 records9280_9312 :=
  aligned9280_9296.append aligned9296_9312

def missing9312_9313 : List (BitVec (edgeCount 12)) :=
  [missing9312]
abbrev records9312_9313 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9312]
theorem aligned9312_9313 :
    AlignedValid 12 3 missing9312_9313 records9312_9313 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9312
    maskCheck9312 AlignedValid.nil

def missing9313_9314 : List (BitVec (edgeCount 12)) :=
  [missing9313]
abbrev records9313_9314 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9313]
theorem aligned9313_9314 :
    AlignedValid 12 3 missing9313_9314 records9313_9314 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9313
    maskCheck9313 AlignedValid.nil

def missing9312_9314 : List (BitVec (edgeCount 12)) :=
  missing9312_9313 ++ missing9313_9314
abbrev records9312_9314 : List Blob :=
  records9312_9313 ++ records9313_9314
theorem aligned9312_9314 :
    AlignedValid 12 3 missing9312_9314 records9312_9314 :=
  aligned9312_9313.append aligned9313_9314

def missing9314_9315 : List (BitVec (edgeCount 12)) :=
  [missing9314]
abbrev records9314_9315 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9314]
theorem aligned9314_9315 :
    AlignedValid 12 3 missing9314_9315 records9314_9315 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9314
    maskCheck9314 AlignedValid.nil

def missing9315_9316 : List (BitVec (edgeCount 12)) :=
  [missing9315]
abbrev records9315_9316 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9315]
theorem aligned9315_9316 :
    AlignedValid 12 3 missing9315_9316 records9315_9316 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9315
    maskCheck9315 AlignedValid.nil

def missing9314_9316 : List (BitVec (edgeCount 12)) :=
  missing9314_9315 ++ missing9315_9316
abbrev records9314_9316 : List Blob :=
  records9314_9315 ++ records9315_9316
theorem aligned9314_9316 :
    AlignedValid 12 3 missing9314_9316 records9314_9316 :=
  aligned9314_9315.append aligned9315_9316

def missing9312_9316 : List (BitVec (edgeCount 12)) :=
  missing9312_9314 ++ missing9314_9316
abbrev records9312_9316 : List Blob :=
  records9312_9314 ++ records9314_9316
theorem aligned9312_9316 :
    AlignedValid 12 3 missing9312_9316 records9312_9316 :=
  aligned9312_9314.append aligned9314_9316

def missing9316_9317 : List (BitVec (edgeCount 12)) :=
  [missing9316]
abbrev records9316_9317 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9316]
theorem aligned9316_9317 :
    AlignedValid 12 3 missing9316_9317 records9316_9317 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9316
    maskCheck9316 AlignedValid.nil

def missing9317_9318 : List (BitVec (edgeCount 12)) :=
  [missing9317]
abbrev records9317_9318 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9317]
theorem aligned9317_9318 :
    AlignedValid 12 3 missing9317_9318 records9317_9318 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9317
    maskCheck9317 AlignedValid.nil

def missing9316_9318 : List (BitVec (edgeCount 12)) :=
  missing9316_9317 ++ missing9317_9318
abbrev records9316_9318 : List Blob :=
  records9316_9317 ++ records9317_9318
theorem aligned9316_9318 :
    AlignedValid 12 3 missing9316_9318 records9316_9318 :=
  aligned9316_9317.append aligned9317_9318

def missing9318_9319 : List (BitVec (edgeCount 12)) :=
  [missing9318]
abbrev records9318_9319 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9318]
theorem aligned9318_9319 :
    AlignedValid 12 3 missing9318_9319 records9318_9319 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9318
    maskCheck9318 AlignedValid.nil

def missing9319_9320 : List (BitVec (edgeCount 12)) :=
  [missing9319]
abbrev records9319_9320 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9319]
theorem aligned9319_9320 :
    AlignedValid 12 3 missing9319_9320 records9319_9320 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9319
    maskCheck9319 AlignedValid.nil

def missing9318_9320 : List (BitVec (edgeCount 12)) :=
  missing9318_9319 ++ missing9319_9320
abbrev records9318_9320 : List Blob :=
  records9318_9319 ++ records9319_9320
theorem aligned9318_9320 :
    AlignedValid 12 3 missing9318_9320 records9318_9320 :=
  aligned9318_9319.append aligned9319_9320

def missing9316_9320 : List (BitVec (edgeCount 12)) :=
  missing9316_9318 ++ missing9318_9320
abbrev records9316_9320 : List Blob :=
  records9316_9318 ++ records9318_9320
theorem aligned9316_9320 :
    AlignedValid 12 3 missing9316_9320 records9316_9320 :=
  aligned9316_9318.append aligned9318_9320

def missing9312_9320 : List (BitVec (edgeCount 12)) :=
  missing9312_9316 ++ missing9316_9320
abbrev records9312_9320 : List Blob :=
  records9312_9316 ++ records9316_9320
theorem aligned9312_9320 :
    AlignedValid 12 3 missing9312_9320 records9312_9320 :=
  aligned9312_9316.append aligned9316_9320

def missing9320_9321 : List (BitVec (edgeCount 12)) :=
  [missing9320]
abbrev records9320_9321 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9320]
theorem aligned9320_9321 :
    AlignedValid 12 3 missing9320_9321 records9320_9321 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9320
    maskCheck9320 AlignedValid.nil

def missing9321_9322 : List (BitVec (edgeCount 12)) :=
  [missing9321]
abbrev records9321_9322 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9321]
theorem aligned9321_9322 :
    AlignedValid 12 3 missing9321_9322 records9321_9322 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9321
    maskCheck9321 AlignedValid.nil

def missing9320_9322 : List (BitVec (edgeCount 12)) :=
  missing9320_9321 ++ missing9321_9322
abbrev records9320_9322 : List Blob :=
  records9320_9321 ++ records9321_9322
theorem aligned9320_9322 :
    AlignedValid 12 3 missing9320_9322 records9320_9322 :=
  aligned9320_9321.append aligned9321_9322

def missing9322_9323 : List (BitVec (edgeCount 12)) :=
  [missing9322]
abbrev records9322_9323 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9322]
theorem aligned9322_9323 :
    AlignedValid 12 3 missing9322_9323 records9322_9323 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9322
    maskCheck9322 AlignedValid.nil

def missing9323_9324 : List (BitVec (edgeCount 12)) :=
  [missing9323]
abbrev records9323_9324 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9323]
theorem aligned9323_9324 :
    AlignedValid 12 3 missing9323_9324 records9323_9324 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9323
    maskCheck9323 AlignedValid.nil

def missing9322_9324 : List (BitVec (edgeCount 12)) :=
  missing9322_9323 ++ missing9323_9324
abbrev records9322_9324 : List Blob :=
  records9322_9323 ++ records9323_9324
theorem aligned9322_9324 :
    AlignedValid 12 3 missing9322_9324 records9322_9324 :=
  aligned9322_9323.append aligned9323_9324

def missing9320_9324 : List (BitVec (edgeCount 12)) :=
  missing9320_9322 ++ missing9322_9324
abbrev records9320_9324 : List Blob :=
  records9320_9322 ++ records9322_9324
theorem aligned9320_9324 :
    AlignedValid 12 3 missing9320_9324 records9320_9324 :=
  aligned9320_9322.append aligned9322_9324

def missing9324_9325 : List (BitVec (edgeCount 12)) :=
  [missing9324]
abbrev records9324_9325 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9324]
theorem aligned9324_9325 :
    AlignedValid 12 3 missing9324_9325 records9324_9325 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9324
    maskCheck9324 AlignedValid.nil

def missing9325_9326 : List (BitVec (edgeCount 12)) :=
  [missing9325]
abbrev records9325_9326 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9325]
theorem aligned9325_9326 :
    AlignedValid 12 3 missing9325_9326 records9325_9326 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9325
    maskCheck9325 AlignedValid.nil

def missing9324_9326 : List (BitVec (edgeCount 12)) :=
  missing9324_9325 ++ missing9325_9326
abbrev records9324_9326 : List Blob :=
  records9324_9325 ++ records9325_9326
theorem aligned9324_9326 :
    AlignedValid 12 3 missing9324_9326 records9324_9326 :=
  aligned9324_9325.append aligned9325_9326

def missing9326_9327 : List (BitVec (edgeCount 12)) :=
  [missing9326]
abbrev records9326_9327 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9326]
theorem aligned9326_9327 :
    AlignedValid 12 3 missing9326_9327 records9326_9327 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9326
    maskCheck9326 AlignedValid.nil

def missing9327_9328 : List (BitVec (edgeCount 12)) :=
  [missing9327]
abbrev records9327_9328 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9327]
theorem aligned9327_9328 :
    AlignedValid 12 3 missing9327_9328 records9327_9328 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9327
    maskCheck9327 AlignedValid.nil

def missing9326_9328 : List (BitVec (edgeCount 12)) :=
  missing9326_9327 ++ missing9327_9328
abbrev records9326_9328 : List Blob :=
  records9326_9327 ++ records9327_9328
theorem aligned9326_9328 :
    AlignedValid 12 3 missing9326_9328 records9326_9328 :=
  aligned9326_9327.append aligned9327_9328

def missing9324_9328 : List (BitVec (edgeCount 12)) :=
  missing9324_9326 ++ missing9326_9328
abbrev records9324_9328 : List Blob :=
  records9324_9326 ++ records9326_9328
theorem aligned9324_9328 :
    AlignedValid 12 3 missing9324_9328 records9324_9328 :=
  aligned9324_9326.append aligned9326_9328

def missing9320_9328 : List (BitVec (edgeCount 12)) :=
  missing9320_9324 ++ missing9324_9328
abbrev records9320_9328 : List Blob :=
  records9320_9324 ++ records9324_9328
theorem aligned9320_9328 :
    AlignedValid 12 3 missing9320_9328 records9320_9328 :=
  aligned9320_9324.append aligned9324_9328

def missing9312_9328 : List (BitVec (edgeCount 12)) :=
  missing9312_9320 ++ missing9320_9328
abbrev records9312_9328 : List Blob :=
  records9312_9320 ++ records9320_9328
theorem aligned9312_9328 :
    AlignedValid 12 3 missing9312_9328 records9312_9328 :=
  aligned9312_9320.append aligned9320_9328

def missing9328_9329 : List (BitVec (edgeCount 12)) :=
  [missing9328]
abbrev records9328_9329 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9328]
theorem aligned9328_9329 :
    AlignedValid 12 3 missing9328_9329 records9328_9329 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9328
    maskCheck9328 AlignedValid.nil

def missing9329_9330 : List (BitVec (edgeCount 12)) :=
  [missing9329]
abbrev records9329_9330 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9329]
theorem aligned9329_9330 :
    AlignedValid 12 3 missing9329_9330 records9329_9330 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9329
    maskCheck9329 AlignedValid.nil

def missing9328_9330 : List (BitVec (edgeCount 12)) :=
  missing9328_9329 ++ missing9329_9330
abbrev records9328_9330 : List Blob :=
  records9328_9329 ++ records9329_9330
theorem aligned9328_9330 :
    AlignedValid 12 3 missing9328_9330 records9328_9330 :=
  aligned9328_9329.append aligned9329_9330

def missing9330_9331 : List (BitVec (edgeCount 12)) :=
  [missing9330]
abbrev records9330_9331 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9330]
theorem aligned9330_9331 :
    AlignedValid 12 3 missing9330_9331 records9330_9331 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9330
    maskCheck9330 AlignedValid.nil

def missing9331_9332 : List (BitVec (edgeCount 12)) :=
  [missing9331]
abbrev records9331_9332 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9331]
theorem aligned9331_9332 :
    AlignedValid 12 3 missing9331_9332 records9331_9332 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9331
    maskCheck9331 AlignedValid.nil

def missing9330_9332 : List (BitVec (edgeCount 12)) :=
  missing9330_9331 ++ missing9331_9332
abbrev records9330_9332 : List Blob :=
  records9330_9331 ++ records9331_9332
theorem aligned9330_9332 :
    AlignedValid 12 3 missing9330_9332 records9330_9332 :=
  aligned9330_9331.append aligned9331_9332

def missing9328_9332 : List (BitVec (edgeCount 12)) :=
  missing9328_9330 ++ missing9330_9332
abbrev records9328_9332 : List Blob :=
  records9328_9330 ++ records9330_9332
theorem aligned9328_9332 :
    AlignedValid 12 3 missing9328_9332 records9328_9332 :=
  aligned9328_9330.append aligned9330_9332

def missing9332_9333 : List (BitVec (edgeCount 12)) :=
  [missing9332]
abbrev records9332_9333 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9332]
theorem aligned9332_9333 :
    AlignedValid 12 3 missing9332_9333 records9332_9333 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9332
    maskCheck9332 AlignedValid.nil

def missing9333_9334 : List (BitVec (edgeCount 12)) :=
  [missing9333]
abbrev records9333_9334 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9333]
theorem aligned9333_9334 :
    AlignedValid 12 3 missing9333_9334 records9333_9334 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9333
    maskCheck9333 AlignedValid.nil

def missing9332_9334 : List (BitVec (edgeCount 12)) :=
  missing9332_9333 ++ missing9333_9334
abbrev records9332_9334 : List Blob :=
  records9332_9333 ++ records9333_9334
theorem aligned9332_9334 :
    AlignedValid 12 3 missing9332_9334 records9332_9334 :=
  aligned9332_9333.append aligned9333_9334

def missing9334_9335 : List (BitVec (edgeCount 12)) :=
  [missing9334]
abbrev records9334_9335 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9334]
theorem aligned9334_9335 :
    AlignedValid 12 3 missing9334_9335 records9334_9335 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9334
    maskCheck9334 AlignedValid.nil

def missing9335_9336 : List (BitVec (edgeCount 12)) :=
  [missing9335]
abbrev records9335_9336 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9335]
theorem aligned9335_9336 :
    AlignedValid 12 3 missing9335_9336 records9335_9336 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9335
    maskCheck9335 AlignedValid.nil

def missing9334_9336 : List (BitVec (edgeCount 12)) :=
  missing9334_9335 ++ missing9335_9336
abbrev records9334_9336 : List Blob :=
  records9334_9335 ++ records9335_9336
theorem aligned9334_9336 :
    AlignedValid 12 3 missing9334_9336 records9334_9336 :=
  aligned9334_9335.append aligned9335_9336

def missing9332_9336 : List (BitVec (edgeCount 12)) :=
  missing9332_9334 ++ missing9334_9336
abbrev records9332_9336 : List Blob :=
  records9332_9334 ++ records9334_9336
theorem aligned9332_9336 :
    AlignedValid 12 3 missing9332_9336 records9332_9336 :=
  aligned9332_9334.append aligned9334_9336

def missing9328_9336 : List (BitVec (edgeCount 12)) :=
  missing9328_9332 ++ missing9332_9336
abbrev records9328_9336 : List Blob :=
  records9328_9332 ++ records9332_9336
theorem aligned9328_9336 :
    AlignedValid 12 3 missing9328_9336 records9328_9336 :=
  aligned9328_9332.append aligned9332_9336

def missing9336_9337 : List (BitVec (edgeCount 12)) :=
  [missing9336]
abbrev records9336_9337 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9336]
theorem aligned9336_9337 :
    AlignedValid 12 3 missing9336_9337 records9336_9337 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9336
    maskCheck9336 AlignedValid.nil

def missing9337_9338 : List (BitVec (edgeCount 12)) :=
  [missing9337]
abbrev records9337_9338 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9337]
theorem aligned9337_9338 :
    AlignedValid 12 3 missing9337_9338 records9337_9338 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9337
    maskCheck9337 AlignedValid.nil

def missing9336_9338 : List (BitVec (edgeCount 12)) :=
  missing9336_9337 ++ missing9337_9338
abbrev records9336_9338 : List Blob :=
  records9336_9337 ++ records9337_9338
theorem aligned9336_9338 :
    AlignedValid 12 3 missing9336_9338 records9336_9338 :=
  aligned9336_9337.append aligned9337_9338

def missing9338_9339 : List (BitVec (edgeCount 12)) :=
  [missing9338]
abbrev records9338_9339 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9338]
theorem aligned9338_9339 :
    AlignedValid 12 3 missing9338_9339 records9338_9339 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9338
    maskCheck9338 AlignedValid.nil

def missing9339_9340 : List (BitVec (edgeCount 12)) :=
  [missing9339]
abbrev records9339_9340 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9339]
theorem aligned9339_9340 :
    AlignedValid 12 3 missing9339_9340 records9339_9340 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9339
    maskCheck9339 AlignedValid.nil

def missing9338_9340 : List (BitVec (edgeCount 12)) :=
  missing9338_9339 ++ missing9339_9340
abbrev records9338_9340 : List Blob :=
  records9338_9339 ++ records9339_9340
theorem aligned9338_9340 :
    AlignedValid 12 3 missing9338_9340 records9338_9340 :=
  aligned9338_9339.append aligned9339_9340

def missing9336_9340 : List (BitVec (edgeCount 12)) :=
  missing9336_9338 ++ missing9338_9340
abbrev records9336_9340 : List Blob :=
  records9336_9338 ++ records9338_9340
theorem aligned9336_9340 :
    AlignedValid 12 3 missing9336_9340 records9336_9340 :=
  aligned9336_9338.append aligned9338_9340

def missing9340_9341 : List (BitVec (edgeCount 12)) :=
  [missing9340]
abbrev records9340_9341 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9340]
theorem aligned9340_9341 :
    AlignedValid 12 3 missing9340_9341 records9340_9341 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9340
    maskCheck9340 AlignedValid.nil

def missing9341_9342 : List (BitVec (edgeCount 12)) :=
  [missing9341]
abbrev records9341_9342 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9341]
theorem aligned9341_9342 :
    AlignedValid 12 3 missing9341_9342 records9341_9342 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9341
    maskCheck9341 AlignedValid.nil

def missing9340_9342 : List (BitVec (edgeCount 12)) :=
  missing9340_9341 ++ missing9341_9342
abbrev records9340_9342 : List Blob :=
  records9340_9341 ++ records9341_9342
theorem aligned9340_9342 :
    AlignedValid 12 3 missing9340_9342 records9340_9342 :=
  aligned9340_9341.append aligned9341_9342

def missing9342_9343 : List (BitVec (edgeCount 12)) :=
  [missing9342]
abbrev records9342_9343 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9342]
theorem aligned9342_9343 :
    AlignedValid 12 3 missing9342_9343 records9342_9343 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9342
    maskCheck9342 AlignedValid.nil

def missing9343_9344 : List (BitVec (edgeCount 12)) :=
  [missing9343]
abbrev records9343_9344 : List Blob :=
  [StrongPackedBucketN12A3Shard072.record9343]
theorem aligned9343_9344 :
    AlignedValid 12 3 missing9343_9344 records9343_9344 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard072.check9343
    maskCheck9343 AlignedValid.nil

def missing9342_9344 : List (BitVec (edgeCount 12)) :=
  missing9342_9343 ++ missing9343_9344
abbrev records9342_9344 : List Blob :=
  records9342_9343 ++ records9343_9344
theorem aligned9342_9344 :
    AlignedValid 12 3 missing9342_9344 records9342_9344 :=
  aligned9342_9343.append aligned9343_9344

def missing9340_9344 : List (BitVec (edgeCount 12)) :=
  missing9340_9342 ++ missing9342_9344
abbrev records9340_9344 : List Blob :=
  records9340_9342 ++ records9342_9344
theorem aligned9340_9344 :
    AlignedValid 12 3 missing9340_9344 records9340_9344 :=
  aligned9340_9342.append aligned9342_9344

def missing9336_9344 : List (BitVec (edgeCount 12)) :=
  missing9336_9340 ++ missing9340_9344
abbrev records9336_9344 : List Blob :=
  records9336_9340 ++ records9340_9344
theorem aligned9336_9344 :
    AlignedValid 12 3 missing9336_9344 records9336_9344 :=
  aligned9336_9340.append aligned9340_9344

def missing9328_9344 : List (BitVec (edgeCount 12)) :=
  missing9328_9336 ++ missing9336_9344
abbrev records9328_9344 : List Blob :=
  records9328_9336 ++ records9336_9344
theorem aligned9328_9344 :
    AlignedValid 12 3 missing9328_9344 records9328_9344 :=
  aligned9328_9336.append aligned9336_9344

def missing9312_9344 : List (BitVec (edgeCount 12)) :=
  missing9312_9328 ++ missing9328_9344
abbrev records9312_9344 : List Blob :=
  records9312_9328 ++ records9328_9344
theorem aligned9312_9344 :
    AlignedValid 12 3 missing9312_9344 records9312_9344 :=
  aligned9312_9328.append aligned9328_9344

def missing9280_9344 : List (BitVec (edgeCount 12)) :=
  missing9280_9312 ++ missing9312_9344
abbrev records9280_9344 : List Blob :=
  records9280_9312 ++ records9312_9344
theorem aligned9280_9344 :
    AlignedValid 12 3 missing9280_9344 records9280_9344 :=
  aligned9280_9312.append aligned9312_9344

def missing9216_9344 : List (BitVec (edgeCount 12)) :=
  missing9216_9280 ++ missing9280_9344
abbrev records9216_9344 : List Blob :=
  records9216_9280 ++ records9280_9344
theorem aligned9216_9344 :
    AlignedValid 12 3 missing9216_9344 records9216_9344 :=
  aligned9216_9280.append aligned9280_9344

abbrev missing : List (BitVec (edgeCount 12)) := missing9216_9344
abbrev records : List Blob := records9216_9344
theorem aligned : AlignedValid 12 3 missing records := aligned9216_9344

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard072
