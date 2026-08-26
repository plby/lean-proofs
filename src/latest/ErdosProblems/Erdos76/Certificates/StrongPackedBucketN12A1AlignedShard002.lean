/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A1Shard002

/-! Decode-only alignment checks for n=12, a=1, records 256--383. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A1AlignedShard002

open PackedBucketCertificate

def missing256 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19456535758817460224
theorem maskCheck256 :
    checkMaskFor missing256 StrongPackedBucketN12A1Shard002.record256 = true := by
  decide

def missing257 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19708737337950208000
theorem maskCheck257 :
    checkMaskFor missing257 StrongPackedBucketN12A1Shard002.record257 = true := by
  decide

def missing258 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19780794931988135936
theorem maskCheck258 :
    checkMaskFor missing258 StrongPackedBucketN12A1Shard002.record258 = true := by
  decide

def missing259 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20032996511120883712
theorem maskCheck259 :
    checkMaskFor missing259 StrongPackedBucketN12A1Shard002.record259 = true := by
  decide

def missing260 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21942522753125974016
theorem maskCheck260 :
    checkMaskFor missing260 StrongPackedBucketN12A1Shard002.record260 = true := by
  decide

def missing261 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22050609144182865920
theorem maskCheck261 :
    checkMaskFor missing261 StrongPackedBucketN12A1Shard002.record261 = true := by
  decide

def missing262 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 26518179974534397952
theorem maskCheck262 :
    checkMaskFor missing262 StrongPackedBucketN12A1Shard002.record262 = true := by
  decide

def missing263 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37146675095128768512
theorem maskCheck263 :
    checkMaskFor missing263 StrongPackedBucketN12A1Shard002.record263 = true := by
  decide

def missing264 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37362847877242552320
theorem maskCheck264 :
    checkMaskFor missing264 StrongPackedBucketN12A1Shard002.record264 = true := by
  decide

def missing265 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37903279832527011840
theorem maskCheck265 :
    checkMaskFor missing265 StrongPackedBucketN12A1Shard002.record265 = true := by
  decide

def missing266 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38155481411659759616
theorem maskCheck266 :
    checkMaskFor missing266 StrongPackedBucketN12A1Shard002.record266 = true := by
  decide

def missing267 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38227539005697687552
theorem maskCheck267 :
    checkMaskFor missing267 StrongPackedBucketN12A1Shard002.record267 = true := by
  decide

def missing268 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38479740584830435328
theorem maskCheck268 :
    checkMaskFor missing268 StrongPackedBucketN12A1Shard002.record268 = true := by
  decide

def missing269 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40389266826835525632
theorem maskCheck269 :
    checkMaskFor missing269 StrongPackedBucketN12A1Shard002.record269 = true := by
  decide

def missing270 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40497353217892417536
theorem maskCheck270 :
    checkMaskFor missing270 StrongPackedBucketN12A1Shard002.record270 = true := by
  decide

def missing271 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 44964924048243949568
theorem maskCheck271 :
    checkMaskFor missing271 StrongPackedBucketN12A1Shard002.record271 = true := by
  decide

def missing272 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55449303980762464256
theorem maskCheck272 :
    checkMaskFor missing272 StrongPackedBucketN12A1Shard002.record272 = true := by
  decide

def missing273 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55521361574800392192
theorem maskCheck273 :
    checkMaskFor missing273 StrongPackedBucketN12A1Shard002.record273 = true := by
  decide

def missing274 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56530167891331383296
theorem maskCheck274 :
    checkMaskFor missing274 StrongPackedBucketN12A1Shard002.record274 = true := by
  decide

def missing275 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 558552113068638208
theorem maskCheck275 :
    checkMaskFor missing275 StrongPackedBucketN12A1Shard002.record275 = true := by
  decide

def missing276 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1062955271334133760
theorem maskCheck276 :
    checkMaskFor missing276 StrongPackedBucketN12A1Shard002.record276 = true := by
  decide

def missing277 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2179847978922016768
theorem maskCheck277 :
    checkMaskFor missing277 StrongPackedBucketN12A1Shard002.record277 = true := by
  decide

def missing278 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18717065810626478080
theorem maskCheck278 :
    checkMaskFor missing278 StrongPackedBucketN12A1Shard002.record278 = true := by
  decide

def missing279 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55466438769969725440
theorem maskCheck279 :
    checkMaskFor missing279 StrongPackedBucketN12A1Shard002.record279 = true := by
  decide

def missing280 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55790697943140401152
theorem maskCheck280 :
    checkMaskFor missing280 StrongPackedBucketN12A1Shard002.record280 = true := by
  decide

def missing281 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 558622481812815872
theorem maskCheck281 :
    checkMaskFor missing281 StrongPackedBucketN12A1Shard002.record281 = true := by
  decide

def missing282 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 990968046040383488
theorem maskCheck282 :
    checkMaskFor missing282 StrongPackedBucketN12A1Shard002.record282 = true := by
  decide

def missing283 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1099054437097275392
theorem maskCheck283 :
    checkMaskFor missing283 StrongPackedBucketN12A1Shard002.record283 = true := by
  decide

def missing284 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2071831956609302528
theorem maskCheck284 :
    checkMaskFor missing284 StrongPackedBucketN12A1Shard002.record284 = true := by
  decide

def missing285 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2107860753628266496
theorem maskCheck285 :
    checkMaskFor missing285 StrongPackedBucketN12A1Shard002.record285 = true := by
  decide

def missing286 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4341646168804032512
theorem maskCheck286 :
    checkMaskFor missing286 StrongPackedBucketN12A1Shard002.record286 = true := by
  decide

def missing287 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18717136179370655744
theorem maskCheck287 :
    checkMaskFor missing287 StrongPackedBucketN12A1Shard002.record287 = true := by
  decide

def missing288 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18861251367446511616
theorem maskCheck288 :
    checkMaskFor missing288 StrongPackedBucketN12A1Shard002.record288 = true := by
  decide

def missing289 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18933308961484439552
theorem maskCheck289 :
    checkMaskFor missing289 StrongPackedBucketN12A1Shard002.record289 = true := by
  decide

def missing290 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18969337758503403520
theorem maskCheck290 :
    checkMaskFor missing290 StrongPackedBucketN12A1Shard002.record290 = true := by
  decide

def missing291 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19365654525712007168
theorem maskCheck291 :
    checkMaskFor missing291 StrongPackedBucketN12A1Shard002.record291 = true := by
  decide

def missing292 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19473740916768899072
theorem maskCheck292 :
    checkMaskFor missing292 StrongPackedBucketN12A1Shard002.record292 = true := by
  decide

def missing293 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55466509138713903104
theorem maskCheck293 :
    checkMaskFor missing293 StrongPackedBucketN12A1Shard002.record293 = true := by
  decide

def missing294 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55574595529770795008
theorem maskCheck294 :
    checkMaskFor missing294 StrongPackedBucketN12A1Shard002.record294 = true := by
  decide

def missing295 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55682681920827686912
theorem maskCheck295 :
    checkMaskFor missing295 StrongPackedBucketN12A1Shard002.record295 = true := by
  decide

def missing296 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55718710717846650880
theorem maskCheck296 :
    checkMaskFor missing296 StrongPackedBucketN12A1Shard002.record296 = true := by
  decide

def missing297 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56223113876112146432
theorem maskCheck297 :
    checkMaskFor missing297 StrongPackedBucketN12A1Shard002.record297 = true := by
  decide

def missing298 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 558868772417437696
theorem maskCheck298 :
    checkMaskFor missing298 StrongPackedBucketN12A1Shard002.record298 = true := by
  decide

def missing299 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 847099148569149440
theorem maskCheck299 :
    checkMaskFor missing299 StrongPackedBucketN12A1Shard002.record299 = true := by
  decide

def missing300 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1855905465100140544
theorem maskCheck300 :
    checkMaskFor missing300 StrongPackedBucketN12A1Shard002.record300 = true := by
  decide

def missing301 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1927963059138068480
theorem maskCheck301 :
    checkMaskFor missing301 StrongPackedBucketN12A1Shard002.record301 = true := by
  decide

def missing302 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4089690880275906560
theorem maskCheck302 :
    checkMaskFor missing302 StrongPackedBucketN12A1Shard002.record302 = true := by
  decide

def missing303 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8665348101684330496
theorem maskCheck303 :
    checkMaskFor missing303 StrongPackedBucketN12A1Shard002.record303 = true := by
  decide

def missing304 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18717382469975277568
theorem maskCheck304 :
    checkMaskFor missing304 StrongPackedBucketN12A1Shard002.record304 = true := by
  decide

def missing305 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18933555252089061376
theorem maskCheck305 :
    checkMaskFor missing305 StrongPackedBucketN12A1Shard002.record305 = true := by
  decide

def missing306 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19149728034202845184
theorem maskCheck306 :
    checkMaskFor missing306 StrongPackedBucketN12A1Shard002.record306 = true := by
  decide

def missing307 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19221785628240773120
theorem maskCheck307 :
    checkMaskFor missing307 StrongPackedBucketN12A1Shard002.record307 = true := by
  decide

def missing308 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19473987207373520896
theorem maskCheck308 :
    checkMaskFor missing308 StrongPackedBucketN12A1Shard002.record308 = true := by
  decide

def missing309 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20230591944771764224
theorem maskCheck309 :
    checkMaskFor missing309 StrongPackedBucketN12A1Shard002.record309 = true := by
  decide

def missing310 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20338678335828656128
theorem maskCheck310 :
    checkMaskFor missing310 StrongPackedBucketN12A1Shard002.record310 = true := by
  decide

def missing311 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22500406156966494208
theorem maskCheck311 :
    checkMaskFor missing311 StrongPackedBucketN12A1Shard002.record311 = true := by
  decide

def missing312 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57088051295171903488
theorem maskCheck312 :
    checkMaskFor missing312 StrongPackedBucketN12A1Shard002.record312 = true := by
  decide

def missing313 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 252448350773706752
theorem maskCheck313 :
    checkMaskFor missing313 StrongPackedBucketN12A1Shard002.record313 = true := by
  decide

def missing314 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2017859404702941184
theorem maskCheck314 :
    checkMaskFor missing314 StrongPackedBucketN12A1Shard002.record314 = true := by
  decide

def missing315 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1873884954115440640
theorem maskCheck315 :
    checkMaskFor missing315 StrongPackedBucketN12A1Shard002.record315 = true := by
  decide

def missing316 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4035612775253278720
theorem maskCheck316 :
    checkMaskFor missing316 StrongPackedBucketN12A1Shard002.record316 = true := by
  decide

def missing317 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 505283248604053504
theorem maskCheck317 :
    checkMaskFor missing317 StrongPackedBucketN12A1Shard002.record317 = true := by
  decide

def missing318 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1514089565135044608
theorem maskCheck318 :
    checkMaskFor missing318 StrongPackedBucketN12A1Shard002.record318 = true := by
  decide

def missing319 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3531702198197026816
theorem maskCheck319 :
    checkMaskFor missing319 StrongPackedBucketN12A1Shard002.record319 = true := by
  decide

def missing320 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8071330622586486784
theorem maskCheck320 :
    checkMaskFor missing320 StrongPackedBucketN12A1Shard002.record320 = true := by
  decide

def missing321 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16142871870369169408
theorem maskCheck321 :
    checkMaskFor missing321 StrongPackedBucketN12A1Shard002.record321 = true := by
  decide

def missing322 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2269955087390474240
theorem maskCheck322 :
    checkMaskFor missing322 StrongPackedBucketN12A1Shard002.record322 = true := by
  decide

def missing323 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4431682908528312320
theorem maskCheck323 :
    checkMaskFor missing323 StrongPackedBucketN12A1Shard002.record323 = true := by
  decide

def missing324 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8971311332917772288
theorem maskCheck324 :
    checkMaskFor missing324 StrongPackedBucketN12A1Shard002.record324 = true := by
  decide

def missing325 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10340405619638403072
theorem maskCheck325 :
    checkMaskFor missing325 StrongPackedBucketN12A1Shard002.record325 = true := by
  decide

def missing326 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11349211936169394176
theorem maskCheck326 :
    checkMaskFor missing326 StrongPackedBucketN12A1Shard002.record326 = true := by
  decide

def missing327 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13582997351345160192
theorem maskCheck327 :
    checkMaskFor missing327 StrongPackedBucketN12A1Shard002.record327 = true := by
  decide

def missing328 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28210688941044531200
theorem maskCheck328 :
    checkMaskFor missing328 StrongPackedBucketN12A1Shard002.record328 = true := by
  decide

def missing329 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28643034505272098816
theorem maskCheck329 :
    checkMaskFor missing329 StrongPackedBucketN12A1Shard002.record329 = true := by
  decide

def missing330 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64815946712311922688
theorem maskCheck330 :
    checkMaskFor missing330 StrongPackedBucketN12A1Shard002.record330 = true := by
  decide

def missing331 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117068767155716096
theorem maskCheck331 :
    checkMaskFor missing331 StrongPackedBucketN12A1Shard002.record331 = true := by
  decide

def missing332 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2125875083686707200
theorem maskCheck332 :
    checkMaskFor missing332 StrongPackedBucketN12A1Shard002.record332 = true := by
  decide

def missing333 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2197932677724635136
theorem maskCheck333 :
    checkMaskFor missing333 StrongPackedBucketN12A1Shard002.record333 = true := by
  decide

def missing334 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2233961474743599104
theorem maskCheck334 :
    checkMaskFor missing334 StrongPackedBucketN12A1Shard002.record334 = true := by
  decide

def missing335 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4359660498862473216
theorem maskCheck335 :
    checkMaskFor missing335 StrongPackedBucketN12A1Shard002.record335 = true := by
  decide

def missing336 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4395689295881437184
theorem maskCheck336 :
    checkMaskFor missing336 StrongPackedBucketN12A1Shard002.record336 = true := by
  decide

def missing337 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4467746889919365120
theorem maskCheck337 :
    checkMaskFor missing337 StrongPackedBucketN12A1Shard002.record337 = true := by
  decide

def missing338 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8935317720270897152
theorem maskCheck338 :
    checkMaskFor missing338 StrongPackedBucketN12A1Shard002.record338 = true := by
  decide

def missing339 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9763980051707068416
theorem maskCheck339 :
    checkMaskFor missing339 StrongPackedBucketN12A1Shard002.record339 = true := by
  decide

def missing340 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10196325615934636032
theorem maskCheck340 :
    checkMaskFor missing340 StrongPackedBucketN12A1Shard002.record340 = true := by
  decide

def missing341 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10268383209972563968
theorem maskCheck341 :
    checkMaskFor missing341 StrongPackedBucketN12A1Shard002.record341 = true := by
  decide

def missing342 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10304412006991527936
theorem maskCheck342 :
    checkMaskFor missing342 StrongPackedBucketN12A1Shard002.record342 = true := by
  decide

def missing343 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11277189526503555072
theorem maskCheck343 :
    checkMaskFor missing343 StrongPackedBucketN12A1Shard002.record343 = true := by
  decide

def missing344 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11385275917560446976
theorem maskCheck344 :
    checkMaskFor missing344 StrongPackedBucketN12A1Shard002.record344 = true := by
  decide

def missing345 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18987352088561844224
theorem maskCheck345 :
    checkMaskFor missing345 StrongPackedBucketN12A1Shard002.record345 = true := by
  decide

def missing346 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19419697652789411840
theorem maskCheck346 :
    checkMaskFor missing346 StrongPackedBucketN12A1Shard002.record346 = true := by
  decide

def missing347 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19527784043846303744
theorem maskCheck347 :
    checkMaskFor missing347 StrongPackedBucketN12A1Shard002.record347 = true := by
  decide

def missing348 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20536590360377294848
theorem maskCheck348 :
    checkMaskFor missing348 StrongPackedBucketN12A1Shard002.record348 = true := by
  decide

def missing349 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27922493749264908288
theorem maskCheck349 :
    checkMaskFor missing349 StrongPackedBucketN12A1Shard002.record349 = true := by
  decide

def missing350 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28066608937340764160
theorem maskCheck350 :
    checkMaskFor missing350 StrongPackedBucketN12A1Shard002.record350 = true := by
  decide

def missing351 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28174695328397656064
theorem maskCheck351 :
    checkMaskFor missing351 StrongPackedBucketN12A1Shard002.record351 = true := by
  decide

def missing352 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37434096162271395840
theorem maskCheck352 :
    checkMaskFor missing352 StrongPackedBucketN12A1Shard002.record352 = true := by
  decide

def missing353 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37866441726498963456
theorem maskCheck353 :
    checkMaskFor missing353 StrongPackedBucketN12A1Shard002.record353 = true := by
  decide

def missing354 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37938499320536891392
theorem maskCheck354 :
    checkMaskFor missing354 StrongPackedBucketN12A1Shard002.record354 = true := by
  decide

def missing355 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38947305637067882496
theorem maskCheck355 :
    checkMaskFor missing355 StrongPackedBucketN12A1Shard002.record355 = true := by
  decide

def missing356 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46369237822974459904
theorem maskCheck356 :
    checkMaskFor missing356 StrongPackedBucketN12A1Shard002.record356 = true := by
  decide

def missing357 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46585410605088243712
theorem maskCheck357 :
    checkMaskFor missing357 StrongPackedBucketN12A1Shard002.record357 = true := by
  decide

def missing358 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55592609859829235712
theorem maskCheck358 :
    checkMaskFor missing358 StrongPackedBucketN12A1Shard002.record358 = true := by
  decide

def missing359 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55736725047905091584
theorem maskCheck359 :
    checkMaskFor missing359 StrongPackedBucketN12A1Shard002.record359 = true := by
  decide

def missing360 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117315057760337920
theorem maskCheck360 :
    checkMaskFor missing360 StrongPackedBucketN12A1Shard002.record360 = true := by
  decide

def missing361 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1982006186215473152
theorem maskCheck361 :
    checkMaskFor missing361 StrongPackedBucketN12A1Shard002.record361 = true := by
  decide

def missing362 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2198178968329256960
theorem maskCheck362 :
    checkMaskFor missing362 StrongPackedBucketN12A1Shard002.record362 = true := by
  decide

def missing363 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4143734007353311232
theorem maskCheck363 :
    checkMaskFor missing363 StrongPackedBucketN12A1Shard002.record363 = true := by
  decide

def missing364 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4215791601391239168
theorem maskCheck364 :
    checkMaskFor missing364 StrongPackedBucketN12A1Shard002.record364 = true := by
  decide

def missing365 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4467993180523986944
theorem maskCheck365 :
    checkMaskFor missing365 StrongPackedBucketN12A1Shard002.record365 = true := by
  decide

def missing366 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8683362431742771200
theorem maskCheck366 :
    checkMaskFor missing366 StrongPackedBucketN12A1Shard002.record366 = true := by
  decide

def missing367 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8791448822799663104
theorem maskCheck367 :
    checkMaskFor missing367 StrongPackedBucketN12A1Shard002.record367 = true := by
  decide

def missing368 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9764226342311690240
theorem maskCheck368 :
    checkMaskFor missing368 StrongPackedBucketN12A1Shard002.record368 = true := by
  decide

def missing369 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10052456718463401984
theorem maskCheck369 :
    checkMaskFor missing369 StrongPackedBucketN12A1Shard002.record369 = true := by
  decide

def missing370 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10268629500577185792
theorem maskCheck370 :
    checkMaskFor missing370 StrongPackedBucketN12A1Shard002.record370 = true := by
  decide

def missing371 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11061263034994393088
theorem maskCheck371 :
    checkMaskFor missing371 StrongPackedBucketN12A1Shard002.record371 = true := by
  decide

def missing372 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11133320629032321024
theorem maskCheck372 :
    checkMaskFor missing372 StrongPackedBucketN12A1Shard002.record372 = true := by
  decide

def missing373 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13295048450170159104
theorem maskCheck373 :
    checkMaskFor missing373 StrongPackedBucketN12A1Shard002.record373 = true := by
  decide

def missing374 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27922740039869530112
theorem maskCheck374 :
    checkMaskFor missing374 StrongPackedBucketN12A1Shard002.record374 = true := by
  decide

def missing375 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28355085604097097728
theorem maskCheck375 :
    checkMaskFor missing375 StrongPackedBucketN12A1Shard002.record375 = true := by
  decide

def missing376 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37434342452876017664
theorem maskCheck376 :
    checkMaskFor missing376 StrongPackedBucketN12A1Shard002.record376 = true := by
  decide

def missing377 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37722572829027729408
theorem maskCheck377 :
    checkMaskFor missing377 StrongPackedBucketN12A1Shard002.record377 = true := by
  decide

def missing378 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37938745611141513216
theorem maskCheck378 :
    checkMaskFor missing378 StrongPackedBucketN12A1Shard002.record378 = true := by
  decide

def missing379 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38731379145558720512
theorem maskCheck379 :
    checkMaskFor missing379 StrongPackedBucketN12A1Shard002.record379 = true := by
  decide

def missing380 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38803436739596648448
theorem maskCheck380 :
    checkMaskFor missing380 StrongPackedBucketN12A1Shard002.record380 = true := by
  decide

def missing381 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39055638318729396224
theorem maskCheck381 :
    checkMaskFor missing381 StrongPackedBucketN12A1Shard002.record381 = true := by
  decide

def missing382 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40965164560734486528
theorem maskCheck382 :
    checkMaskFor missing382 StrongPackedBucketN12A1Shard002.record382 = true := by
  decide

def missing383 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41073250951791378432
theorem maskCheck383 :
    checkMaskFor missing383 StrongPackedBucketN12A1Shard002.record383 = true := by
  decide

def missing256_257 : List (BitVec (edgeCount 12)) :=
  [missing256]
abbrev records256_257 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record256]
theorem aligned256_257 :
    AlignedValid 12 1 missing256_257 records256_257 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check256
    maskCheck256 AlignedValid.nil

def missing257_258 : List (BitVec (edgeCount 12)) :=
  [missing257]
abbrev records257_258 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record257]
theorem aligned257_258 :
    AlignedValid 12 1 missing257_258 records257_258 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check257
    maskCheck257 AlignedValid.nil

def missing256_258 : List (BitVec (edgeCount 12)) :=
  missing256_257 ++ missing257_258
abbrev records256_258 : List Blob :=
  records256_257 ++ records257_258
theorem aligned256_258 :
    AlignedValid 12 1 missing256_258 records256_258 :=
  aligned256_257.append aligned257_258

def missing258_259 : List (BitVec (edgeCount 12)) :=
  [missing258]
abbrev records258_259 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record258]
theorem aligned258_259 :
    AlignedValid 12 1 missing258_259 records258_259 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check258
    maskCheck258 AlignedValid.nil

def missing259_260 : List (BitVec (edgeCount 12)) :=
  [missing259]
abbrev records259_260 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record259]
theorem aligned259_260 :
    AlignedValid 12 1 missing259_260 records259_260 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check259
    maskCheck259 AlignedValid.nil

def missing258_260 : List (BitVec (edgeCount 12)) :=
  missing258_259 ++ missing259_260
abbrev records258_260 : List Blob :=
  records258_259 ++ records259_260
theorem aligned258_260 :
    AlignedValid 12 1 missing258_260 records258_260 :=
  aligned258_259.append aligned259_260

def missing256_260 : List (BitVec (edgeCount 12)) :=
  missing256_258 ++ missing258_260
abbrev records256_260 : List Blob :=
  records256_258 ++ records258_260
theorem aligned256_260 :
    AlignedValid 12 1 missing256_260 records256_260 :=
  aligned256_258.append aligned258_260

def missing260_261 : List (BitVec (edgeCount 12)) :=
  [missing260]
abbrev records260_261 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record260]
theorem aligned260_261 :
    AlignedValid 12 1 missing260_261 records260_261 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check260
    maskCheck260 AlignedValid.nil

def missing261_262 : List (BitVec (edgeCount 12)) :=
  [missing261]
abbrev records261_262 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record261]
theorem aligned261_262 :
    AlignedValid 12 1 missing261_262 records261_262 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check261
    maskCheck261 AlignedValid.nil

def missing260_262 : List (BitVec (edgeCount 12)) :=
  missing260_261 ++ missing261_262
abbrev records260_262 : List Blob :=
  records260_261 ++ records261_262
theorem aligned260_262 :
    AlignedValid 12 1 missing260_262 records260_262 :=
  aligned260_261.append aligned261_262

def missing262_263 : List (BitVec (edgeCount 12)) :=
  [missing262]
abbrev records262_263 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record262]
theorem aligned262_263 :
    AlignedValid 12 1 missing262_263 records262_263 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check262
    maskCheck262 AlignedValid.nil

def missing263_264 : List (BitVec (edgeCount 12)) :=
  [missing263]
abbrev records263_264 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record263]
theorem aligned263_264 :
    AlignedValid 12 1 missing263_264 records263_264 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check263
    maskCheck263 AlignedValid.nil

def missing262_264 : List (BitVec (edgeCount 12)) :=
  missing262_263 ++ missing263_264
abbrev records262_264 : List Blob :=
  records262_263 ++ records263_264
theorem aligned262_264 :
    AlignedValid 12 1 missing262_264 records262_264 :=
  aligned262_263.append aligned263_264

def missing260_264 : List (BitVec (edgeCount 12)) :=
  missing260_262 ++ missing262_264
abbrev records260_264 : List Blob :=
  records260_262 ++ records262_264
theorem aligned260_264 :
    AlignedValid 12 1 missing260_264 records260_264 :=
  aligned260_262.append aligned262_264

def missing256_264 : List (BitVec (edgeCount 12)) :=
  missing256_260 ++ missing260_264
abbrev records256_264 : List Blob :=
  records256_260 ++ records260_264
theorem aligned256_264 :
    AlignedValid 12 1 missing256_264 records256_264 :=
  aligned256_260.append aligned260_264

def missing264_265 : List (BitVec (edgeCount 12)) :=
  [missing264]
abbrev records264_265 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record264]
theorem aligned264_265 :
    AlignedValid 12 1 missing264_265 records264_265 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check264
    maskCheck264 AlignedValid.nil

def missing265_266 : List (BitVec (edgeCount 12)) :=
  [missing265]
abbrev records265_266 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record265]
theorem aligned265_266 :
    AlignedValid 12 1 missing265_266 records265_266 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check265
    maskCheck265 AlignedValid.nil

def missing264_266 : List (BitVec (edgeCount 12)) :=
  missing264_265 ++ missing265_266
abbrev records264_266 : List Blob :=
  records264_265 ++ records265_266
theorem aligned264_266 :
    AlignedValid 12 1 missing264_266 records264_266 :=
  aligned264_265.append aligned265_266

def missing266_267 : List (BitVec (edgeCount 12)) :=
  [missing266]
abbrev records266_267 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record266]
theorem aligned266_267 :
    AlignedValid 12 1 missing266_267 records266_267 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check266
    maskCheck266 AlignedValid.nil

def missing267_268 : List (BitVec (edgeCount 12)) :=
  [missing267]
abbrev records267_268 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record267]
theorem aligned267_268 :
    AlignedValid 12 1 missing267_268 records267_268 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check267
    maskCheck267 AlignedValid.nil

def missing266_268 : List (BitVec (edgeCount 12)) :=
  missing266_267 ++ missing267_268
abbrev records266_268 : List Blob :=
  records266_267 ++ records267_268
theorem aligned266_268 :
    AlignedValid 12 1 missing266_268 records266_268 :=
  aligned266_267.append aligned267_268

def missing264_268 : List (BitVec (edgeCount 12)) :=
  missing264_266 ++ missing266_268
abbrev records264_268 : List Blob :=
  records264_266 ++ records266_268
theorem aligned264_268 :
    AlignedValid 12 1 missing264_268 records264_268 :=
  aligned264_266.append aligned266_268

def missing268_269 : List (BitVec (edgeCount 12)) :=
  [missing268]
abbrev records268_269 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record268]
theorem aligned268_269 :
    AlignedValid 12 1 missing268_269 records268_269 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check268
    maskCheck268 AlignedValid.nil

def missing269_270 : List (BitVec (edgeCount 12)) :=
  [missing269]
abbrev records269_270 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record269]
theorem aligned269_270 :
    AlignedValid 12 1 missing269_270 records269_270 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check269
    maskCheck269 AlignedValid.nil

def missing268_270 : List (BitVec (edgeCount 12)) :=
  missing268_269 ++ missing269_270
abbrev records268_270 : List Blob :=
  records268_269 ++ records269_270
theorem aligned268_270 :
    AlignedValid 12 1 missing268_270 records268_270 :=
  aligned268_269.append aligned269_270

def missing270_271 : List (BitVec (edgeCount 12)) :=
  [missing270]
abbrev records270_271 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record270]
theorem aligned270_271 :
    AlignedValid 12 1 missing270_271 records270_271 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check270
    maskCheck270 AlignedValid.nil

def missing271_272 : List (BitVec (edgeCount 12)) :=
  [missing271]
abbrev records271_272 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record271]
theorem aligned271_272 :
    AlignedValid 12 1 missing271_272 records271_272 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check271
    maskCheck271 AlignedValid.nil

def missing270_272 : List (BitVec (edgeCount 12)) :=
  missing270_271 ++ missing271_272
abbrev records270_272 : List Blob :=
  records270_271 ++ records271_272
theorem aligned270_272 :
    AlignedValid 12 1 missing270_272 records270_272 :=
  aligned270_271.append aligned271_272

def missing268_272 : List (BitVec (edgeCount 12)) :=
  missing268_270 ++ missing270_272
abbrev records268_272 : List Blob :=
  records268_270 ++ records270_272
theorem aligned268_272 :
    AlignedValid 12 1 missing268_272 records268_272 :=
  aligned268_270.append aligned270_272

def missing264_272 : List (BitVec (edgeCount 12)) :=
  missing264_268 ++ missing268_272
abbrev records264_272 : List Blob :=
  records264_268 ++ records268_272
theorem aligned264_272 :
    AlignedValid 12 1 missing264_272 records264_272 :=
  aligned264_268.append aligned268_272

def missing256_272 : List (BitVec (edgeCount 12)) :=
  missing256_264 ++ missing264_272
abbrev records256_272 : List Blob :=
  records256_264 ++ records264_272
theorem aligned256_272 :
    AlignedValid 12 1 missing256_272 records256_272 :=
  aligned256_264.append aligned264_272

def missing272_273 : List (BitVec (edgeCount 12)) :=
  [missing272]
abbrev records272_273 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record272]
theorem aligned272_273 :
    AlignedValid 12 1 missing272_273 records272_273 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check272
    maskCheck272 AlignedValid.nil

def missing273_274 : List (BitVec (edgeCount 12)) :=
  [missing273]
abbrev records273_274 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record273]
theorem aligned273_274 :
    AlignedValid 12 1 missing273_274 records273_274 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check273
    maskCheck273 AlignedValid.nil

def missing272_274 : List (BitVec (edgeCount 12)) :=
  missing272_273 ++ missing273_274
abbrev records272_274 : List Blob :=
  records272_273 ++ records273_274
theorem aligned272_274 :
    AlignedValid 12 1 missing272_274 records272_274 :=
  aligned272_273.append aligned273_274

def missing274_275 : List (BitVec (edgeCount 12)) :=
  [missing274]
abbrev records274_275 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record274]
theorem aligned274_275 :
    AlignedValid 12 1 missing274_275 records274_275 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check274
    maskCheck274 AlignedValid.nil

def missing275_276 : List (BitVec (edgeCount 12)) :=
  [missing275]
abbrev records275_276 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record275]
theorem aligned275_276 :
    AlignedValid 12 1 missing275_276 records275_276 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check275
    maskCheck275 AlignedValid.nil

def missing274_276 : List (BitVec (edgeCount 12)) :=
  missing274_275 ++ missing275_276
abbrev records274_276 : List Blob :=
  records274_275 ++ records275_276
theorem aligned274_276 :
    AlignedValid 12 1 missing274_276 records274_276 :=
  aligned274_275.append aligned275_276

def missing272_276 : List (BitVec (edgeCount 12)) :=
  missing272_274 ++ missing274_276
abbrev records272_276 : List Blob :=
  records272_274 ++ records274_276
theorem aligned272_276 :
    AlignedValid 12 1 missing272_276 records272_276 :=
  aligned272_274.append aligned274_276

def missing276_277 : List (BitVec (edgeCount 12)) :=
  [missing276]
abbrev records276_277 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record276]
theorem aligned276_277 :
    AlignedValid 12 1 missing276_277 records276_277 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check276
    maskCheck276 AlignedValid.nil

def missing277_278 : List (BitVec (edgeCount 12)) :=
  [missing277]
abbrev records277_278 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record277]
theorem aligned277_278 :
    AlignedValid 12 1 missing277_278 records277_278 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check277
    maskCheck277 AlignedValid.nil

def missing276_278 : List (BitVec (edgeCount 12)) :=
  missing276_277 ++ missing277_278
abbrev records276_278 : List Blob :=
  records276_277 ++ records277_278
theorem aligned276_278 :
    AlignedValid 12 1 missing276_278 records276_278 :=
  aligned276_277.append aligned277_278

def missing278_279 : List (BitVec (edgeCount 12)) :=
  [missing278]
abbrev records278_279 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record278]
theorem aligned278_279 :
    AlignedValid 12 1 missing278_279 records278_279 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check278
    maskCheck278 AlignedValid.nil

def missing279_280 : List (BitVec (edgeCount 12)) :=
  [missing279]
abbrev records279_280 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record279]
theorem aligned279_280 :
    AlignedValid 12 1 missing279_280 records279_280 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check279
    maskCheck279 AlignedValid.nil

def missing278_280 : List (BitVec (edgeCount 12)) :=
  missing278_279 ++ missing279_280
abbrev records278_280 : List Blob :=
  records278_279 ++ records279_280
theorem aligned278_280 :
    AlignedValid 12 1 missing278_280 records278_280 :=
  aligned278_279.append aligned279_280

def missing276_280 : List (BitVec (edgeCount 12)) :=
  missing276_278 ++ missing278_280
abbrev records276_280 : List Blob :=
  records276_278 ++ records278_280
theorem aligned276_280 :
    AlignedValid 12 1 missing276_280 records276_280 :=
  aligned276_278.append aligned278_280

def missing272_280 : List (BitVec (edgeCount 12)) :=
  missing272_276 ++ missing276_280
abbrev records272_280 : List Blob :=
  records272_276 ++ records276_280
theorem aligned272_280 :
    AlignedValid 12 1 missing272_280 records272_280 :=
  aligned272_276.append aligned276_280

def missing280_281 : List (BitVec (edgeCount 12)) :=
  [missing280]
abbrev records280_281 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record280]
theorem aligned280_281 :
    AlignedValid 12 1 missing280_281 records280_281 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check280
    maskCheck280 AlignedValid.nil

def missing281_282 : List (BitVec (edgeCount 12)) :=
  [missing281]
abbrev records281_282 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record281]
theorem aligned281_282 :
    AlignedValid 12 1 missing281_282 records281_282 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check281
    maskCheck281 AlignedValid.nil

def missing280_282 : List (BitVec (edgeCount 12)) :=
  missing280_281 ++ missing281_282
abbrev records280_282 : List Blob :=
  records280_281 ++ records281_282
theorem aligned280_282 :
    AlignedValid 12 1 missing280_282 records280_282 :=
  aligned280_281.append aligned281_282

def missing282_283 : List (BitVec (edgeCount 12)) :=
  [missing282]
abbrev records282_283 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record282]
theorem aligned282_283 :
    AlignedValid 12 1 missing282_283 records282_283 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check282
    maskCheck282 AlignedValid.nil

def missing283_284 : List (BitVec (edgeCount 12)) :=
  [missing283]
abbrev records283_284 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record283]
theorem aligned283_284 :
    AlignedValid 12 1 missing283_284 records283_284 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check283
    maskCheck283 AlignedValid.nil

def missing282_284 : List (BitVec (edgeCount 12)) :=
  missing282_283 ++ missing283_284
abbrev records282_284 : List Blob :=
  records282_283 ++ records283_284
theorem aligned282_284 :
    AlignedValid 12 1 missing282_284 records282_284 :=
  aligned282_283.append aligned283_284

def missing280_284 : List (BitVec (edgeCount 12)) :=
  missing280_282 ++ missing282_284
abbrev records280_284 : List Blob :=
  records280_282 ++ records282_284
theorem aligned280_284 :
    AlignedValid 12 1 missing280_284 records280_284 :=
  aligned280_282.append aligned282_284

def missing284_285 : List (BitVec (edgeCount 12)) :=
  [missing284]
abbrev records284_285 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record284]
theorem aligned284_285 :
    AlignedValid 12 1 missing284_285 records284_285 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check284
    maskCheck284 AlignedValid.nil

def missing285_286 : List (BitVec (edgeCount 12)) :=
  [missing285]
abbrev records285_286 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record285]
theorem aligned285_286 :
    AlignedValid 12 1 missing285_286 records285_286 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check285
    maskCheck285 AlignedValid.nil

def missing284_286 : List (BitVec (edgeCount 12)) :=
  missing284_285 ++ missing285_286
abbrev records284_286 : List Blob :=
  records284_285 ++ records285_286
theorem aligned284_286 :
    AlignedValid 12 1 missing284_286 records284_286 :=
  aligned284_285.append aligned285_286

def missing286_287 : List (BitVec (edgeCount 12)) :=
  [missing286]
abbrev records286_287 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record286]
theorem aligned286_287 :
    AlignedValid 12 1 missing286_287 records286_287 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check286
    maskCheck286 AlignedValid.nil

def missing287_288 : List (BitVec (edgeCount 12)) :=
  [missing287]
abbrev records287_288 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record287]
theorem aligned287_288 :
    AlignedValid 12 1 missing287_288 records287_288 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check287
    maskCheck287 AlignedValid.nil

def missing286_288 : List (BitVec (edgeCount 12)) :=
  missing286_287 ++ missing287_288
abbrev records286_288 : List Blob :=
  records286_287 ++ records287_288
theorem aligned286_288 :
    AlignedValid 12 1 missing286_288 records286_288 :=
  aligned286_287.append aligned287_288

def missing284_288 : List (BitVec (edgeCount 12)) :=
  missing284_286 ++ missing286_288
abbrev records284_288 : List Blob :=
  records284_286 ++ records286_288
theorem aligned284_288 :
    AlignedValid 12 1 missing284_288 records284_288 :=
  aligned284_286.append aligned286_288

def missing280_288 : List (BitVec (edgeCount 12)) :=
  missing280_284 ++ missing284_288
abbrev records280_288 : List Blob :=
  records280_284 ++ records284_288
theorem aligned280_288 :
    AlignedValid 12 1 missing280_288 records280_288 :=
  aligned280_284.append aligned284_288

def missing272_288 : List (BitVec (edgeCount 12)) :=
  missing272_280 ++ missing280_288
abbrev records272_288 : List Blob :=
  records272_280 ++ records280_288
theorem aligned272_288 :
    AlignedValid 12 1 missing272_288 records272_288 :=
  aligned272_280.append aligned280_288

def missing256_288 : List (BitVec (edgeCount 12)) :=
  missing256_272 ++ missing272_288
abbrev records256_288 : List Blob :=
  records256_272 ++ records272_288
theorem aligned256_288 :
    AlignedValid 12 1 missing256_288 records256_288 :=
  aligned256_272.append aligned272_288

def missing288_289 : List (BitVec (edgeCount 12)) :=
  [missing288]
abbrev records288_289 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record288]
theorem aligned288_289 :
    AlignedValid 12 1 missing288_289 records288_289 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check288
    maskCheck288 AlignedValid.nil

def missing289_290 : List (BitVec (edgeCount 12)) :=
  [missing289]
abbrev records289_290 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record289]
theorem aligned289_290 :
    AlignedValid 12 1 missing289_290 records289_290 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check289
    maskCheck289 AlignedValid.nil

def missing288_290 : List (BitVec (edgeCount 12)) :=
  missing288_289 ++ missing289_290
abbrev records288_290 : List Blob :=
  records288_289 ++ records289_290
theorem aligned288_290 :
    AlignedValid 12 1 missing288_290 records288_290 :=
  aligned288_289.append aligned289_290

def missing290_291 : List (BitVec (edgeCount 12)) :=
  [missing290]
abbrev records290_291 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record290]
theorem aligned290_291 :
    AlignedValid 12 1 missing290_291 records290_291 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check290
    maskCheck290 AlignedValid.nil

def missing291_292 : List (BitVec (edgeCount 12)) :=
  [missing291]
abbrev records291_292 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record291]
theorem aligned291_292 :
    AlignedValid 12 1 missing291_292 records291_292 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check291
    maskCheck291 AlignedValid.nil

def missing290_292 : List (BitVec (edgeCount 12)) :=
  missing290_291 ++ missing291_292
abbrev records290_292 : List Blob :=
  records290_291 ++ records291_292
theorem aligned290_292 :
    AlignedValid 12 1 missing290_292 records290_292 :=
  aligned290_291.append aligned291_292

def missing288_292 : List (BitVec (edgeCount 12)) :=
  missing288_290 ++ missing290_292
abbrev records288_292 : List Blob :=
  records288_290 ++ records290_292
theorem aligned288_292 :
    AlignedValid 12 1 missing288_292 records288_292 :=
  aligned288_290.append aligned290_292

def missing292_293 : List (BitVec (edgeCount 12)) :=
  [missing292]
abbrev records292_293 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record292]
theorem aligned292_293 :
    AlignedValid 12 1 missing292_293 records292_293 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check292
    maskCheck292 AlignedValid.nil

def missing293_294 : List (BitVec (edgeCount 12)) :=
  [missing293]
abbrev records293_294 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record293]
theorem aligned293_294 :
    AlignedValid 12 1 missing293_294 records293_294 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check293
    maskCheck293 AlignedValid.nil

def missing292_294 : List (BitVec (edgeCount 12)) :=
  missing292_293 ++ missing293_294
abbrev records292_294 : List Blob :=
  records292_293 ++ records293_294
theorem aligned292_294 :
    AlignedValid 12 1 missing292_294 records292_294 :=
  aligned292_293.append aligned293_294

def missing294_295 : List (BitVec (edgeCount 12)) :=
  [missing294]
abbrev records294_295 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record294]
theorem aligned294_295 :
    AlignedValid 12 1 missing294_295 records294_295 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check294
    maskCheck294 AlignedValid.nil

def missing295_296 : List (BitVec (edgeCount 12)) :=
  [missing295]
abbrev records295_296 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record295]
theorem aligned295_296 :
    AlignedValid 12 1 missing295_296 records295_296 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check295
    maskCheck295 AlignedValid.nil

def missing294_296 : List (BitVec (edgeCount 12)) :=
  missing294_295 ++ missing295_296
abbrev records294_296 : List Blob :=
  records294_295 ++ records295_296
theorem aligned294_296 :
    AlignedValid 12 1 missing294_296 records294_296 :=
  aligned294_295.append aligned295_296

def missing292_296 : List (BitVec (edgeCount 12)) :=
  missing292_294 ++ missing294_296
abbrev records292_296 : List Blob :=
  records292_294 ++ records294_296
theorem aligned292_296 :
    AlignedValid 12 1 missing292_296 records292_296 :=
  aligned292_294.append aligned294_296

def missing288_296 : List (BitVec (edgeCount 12)) :=
  missing288_292 ++ missing292_296
abbrev records288_296 : List Blob :=
  records288_292 ++ records292_296
theorem aligned288_296 :
    AlignedValid 12 1 missing288_296 records288_296 :=
  aligned288_292.append aligned292_296

def missing296_297 : List (BitVec (edgeCount 12)) :=
  [missing296]
abbrev records296_297 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record296]
theorem aligned296_297 :
    AlignedValid 12 1 missing296_297 records296_297 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check296
    maskCheck296 AlignedValid.nil

def missing297_298 : List (BitVec (edgeCount 12)) :=
  [missing297]
abbrev records297_298 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record297]
theorem aligned297_298 :
    AlignedValid 12 1 missing297_298 records297_298 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check297
    maskCheck297 AlignedValid.nil

def missing296_298 : List (BitVec (edgeCount 12)) :=
  missing296_297 ++ missing297_298
abbrev records296_298 : List Blob :=
  records296_297 ++ records297_298
theorem aligned296_298 :
    AlignedValid 12 1 missing296_298 records296_298 :=
  aligned296_297.append aligned297_298

def missing298_299 : List (BitVec (edgeCount 12)) :=
  [missing298]
abbrev records298_299 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record298]
theorem aligned298_299 :
    AlignedValid 12 1 missing298_299 records298_299 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check298
    maskCheck298 AlignedValid.nil

def missing299_300 : List (BitVec (edgeCount 12)) :=
  [missing299]
abbrev records299_300 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record299]
theorem aligned299_300 :
    AlignedValid 12 1 missing299_300 records299_300 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check299
    maskCheck299 AlignedValid.nil

def missing298_300 : List (BitVec (edgeCount 12)) :=
  missing298_299 ++ missing299_300
abbrev records298_300 : List Blob :=
  records298_299 ++ records299_300
theorem aligned298_300 :
    AlignedValid 12 1 missing298_300 records298_300 :=
  aligned298_299.append aligned299_300

def missing296_300 : List (BitVec (edgeCount 12)) :=
  missing296_298 ++ missing298_300
abbrev records296_300 : List Blob :=
  records296_298 ++ records298_300
theorem aligned296_300 :
    AlignedValid 12 1 missing296_300 records296_300 :=
  aligned296_298.append aligned298_300

def missing300_301 : List (BitVec (edgeCount 12)) :=
  [missing300]
abbrev records300_301 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record300]
theorem aligned300_301 :
    AlignedValid 12 1 missing300_301 records300_301 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check300
    maskCheck300 AlignedValid.nil

def missing301_302 : List (BitVec (edgeCount 12)) :=
  [missing301]
abbrev records301_302 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record301]
theorem aligned301_302 :
    AlignedValid 12 1 missing301_302 records301_302 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check301
    maskCheck301 AlignedValid.nil

def missing300_302 : List (BitVec (edgeCount 12)) :=
  missing300_301 ++ missing301_302
abbrev records300_302 : List Blob :=
  records300_301 ++ records301_302
theorem aligned300_302 :
    AlignedValid 12 1 missing300_302 records300_302 :=
  aligned300_301.append aligned301_302

def missing302_303 : List (BitVec (edgeCount 12)) :=
  [missing302]
abbrev records302_303 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record302]
theorem aligned302_303 :
    AlignedValid 12 1 missing302_303 records302_303 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check302
    maskCheck302 AlignedValid.nil

def missing303_304 : List (BitVec (edgeCount 12)) :=
  [missing303]
abbrev records303_304 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record303]
theorem aligned303_304 :
    AlignedValid 12 1 missing303_304 records303_304 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check303
    maskCheck303 AlignedValid.nil

def missing302_304 : List (BitVec (edgeCount 12)) :=
  missing302_303 ++ missing303_304
abbrev records302_304 : List Blob :=
  records302_303 ++ records303_304
theorem aligned302_304 :
    AlignedValid 12 1 missing302_304 records302_304 :=
  aligned302_303.append aligned303_304

def missing300_304 : List (BitVec (edgeCount 12)) :=
  missing300_302 ++ missing302_304
abbrev records300_304 : List Blob :=
  records300_302 ++ records302_304
theorem aligned300_304 :
    AlignedValid 12 1 missing300_304 records300_304 :=
  aligned300_302.append aligned302_304

def missing296_304 : List (BitVec (edgeCount 12)) :=
  missing296_300 ++ missing300_304
abbrev records296_304 : List Blob :=
  records296_300 ++ records300_304
theorem aligned296_304 :
    AlignedValid 12 1 missing296_304 records296_304 :=
  aligned296_300.append aligned300_304

def missing288_304 : List (BitVec (edgeCount 12)) :=
  missing288_296 ++ missing296_304
abbrev records288_304 : List Blob :=
  records288_296 ++ records296_304
theorem aligned288_304 :
    AlignedValid 12 1 missing288_304 records288_304 :=
  aligned288_296.append aligned296_304

def missing304_305 : List (BitVec (edgeCount 12)) :=
  [missing304]
abbrev records304_305 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record304]
theorem aligned304_305 :
    AlignedValid 12 1 missing304_305 records304_305 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check304
    maskCheck304 AlignedValid.nil

def missing305_306 : List (BitVec (edgeCount 12)) :=
  [missing305]
abbrev records305_306 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record305]
theorem aligned305_306 :
    AlignedValid 12 1 missing305_306 records305_306 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check305
    maskCheck305 AlignedValid.nil

def missing304_306 : List (BitVec (edgeCount 12)) :=
  missing304_305 ++ missing305_306
abbrev records304_306 : List Blob :=
  records304_305 ++ records305_306
theorem aligned304_306 :
    AlignedValid 12 1 missing304_306 records304_306 :=
  aligned304_305.append aligned305_306

def missing306_307 : List (BitVec (edgeCount 12)) :=
  [missing306]
abbrev records306_307 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record306]
theorem aligned306_307 :
    AlignedValid 12 1 missing306_307 records306_307 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check306
    maskCheck306 AlignedValid.nil

def missing307_308 : List (BitVec (edgeCount 12)) :=
  [missing307]
abbrev records307_308 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record307]
theorem aligned307_308 :
    AlignedValid 12 1 missing307_308 records307_308 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check307
    maskCheck307 AlignedValid.nil

def missing306_308 : List (BitVec (edgeCount 12)) :=
  missing306_307 ++ missing307_308
abbrev records306_308 : List Blob :=
  records306_307 ++ records307_308
theorem aligned306_308 :
    AlignedValid 12 1 missing306_308 records306_308 :=
  aligned306_307.append aligned307_308

def missing304_308 : List (BitVec (edgeCount 12)) :=
  missing304_306 ++ missing306_308
abbrev records304_308 : List Blob :=
  records304_306 ++ records306_308
theorem aligned304_308 :
    AlignedValid 12 1 missing304_308 records304_308 :=
  aligned304_306.append aligned306_308

def missing308_309 : List (BitVec (edgeCount 12)) :=
  [missing308]
abbrev records308_309 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record308]
theorem aligned308_309 :
    AlignedValid 12 1 missing308_309 records308_309 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check308
    maskCheck308 AlignedValid.nil

def missing309_310 : List (BitVec (edgeCount 12)) :=
  [missing309]
abbrev records309_310 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record309]
theorem aligned309_310 :
    AlignedValid 12 1 missing309_310 records309_310 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check309
    maskCheck309 AlignedValid.nil

def missing308_310 : List (BitVec (edgeCount 12)) :=
  missing308_309 ++ missing309_310
abbrev records308_310 : List Blob :=
  records308_309 ++ records309_310
theorem aligned308_310 :
    AlignedValid 12 1 missing308_310 records308_310 :=
  aligned308_309.append aligned309_310

def missing310_311 : List (BitVec (edgeCount 12)) :=
  [missing310]
abbrev records310_311 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record310]
theorem aligned310_311 :
    AlignedValid 12 1 missing310_311 records310_311 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check310
    maskCheck310 AlignedValid.nil

def missing311_312 : List (BitVec (edgeCount 12)) :=
  [missing311]
abbrev records311_312 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record311]
theorem aligned311_312 :
    AlignedValid 12 1 missing311_312 records311_312 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check311
    maskCheck311 AlignedValid.nil

def missing310_312 : List (BitVec (edgeCount 12)) :=
  missing310_311 ++ missing311_312
abbrev records310_312 : List Blob :=
  records310_311 ++ records311_312
theorem aligned310_312 :
    AlignedValid 12 1 missing310_312 records310_312 :=
  aligned310_311.append aligned311_312

def missing308_312 : List (BitVec (edgeCount 12)) :=
  missing308_310 ++ missing310_312
abbrev records308_312 : List Blob :=
  records308_310 ++ records310_312
theorem aligned308_312 :
    AlignedValid 12 1 missing308_312 records308_312 :=
  aligned308_310.append aligned310_312

def missing304_312 : List (BitVec (edgeCount 12)) :=
  missing304_308 ++ missing308_312
abbrev records304_312 : List Blob :=
  records304_308 ++ records308_312
theorem aligned304_312 :
    AlignedValid 12 1 missing304_312 records304_312 :=
  aligned304_308.append aligned308_312

def missing312_313 : List (BitVec (edgeCount 12)) :=
  [missing312]
abbrev records312_313 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record312]
theorem aligned312_313 :
    AlignedValid 12 1 missing312_313 records312_313 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check312
    maskCheck312 AlignedValid.nil

def missing313_314 : List (BitVec (edgeCount 12)) :=
  [missing313]
abbrev records313_314 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record313]
theorem aligned313_314 :
    AlignedValid 12 1 missing313_314 records313_314 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check313
    maskCheck313 AlignedValid.nil

def missing312_314 : List (BitVec (edgeCount 12)) :=
  missing312_313 ++ missing313_314
abbrev records312_314 : List Blob :=
  records312_313 ++ records313_314
theorem aligned312_314 :
    AlignedValid 12 1 missing312_314 records312_314 :=
  aligned312_313.append aligned313_314

def missing314_315 : List (BitVec (edgeCount 12)) :=
  [missing314]
abbrev records314_315 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record314]
theorem aligned314_315 :
    AlignedValid 12 1 missing314_315 records314_315 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check314
    maskCheck314 AlignedValid.nil

def missing315_316 : List (BitVec (edgeCount 12)) :=
  [missing315]
abbrev records315_316 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record315]
theorem aligned315_316 :
    AlignedValid 12 1 missing315_316 records315_316 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check315
    maskCheck315 AlignedValid.nil

def missing314_316 : List (BitVec (edgeCount 12)) :=
  missing314_315 ++ missing315_316
abbrev records314_316 : List Blob :=
  records314_315 ++ records315_316
theorem aligned314_316 :
    AlignedValid 12 1 missing314_316 records314_316 :=
  aligned314_315.append aligned315_316

def missing312_316 : List (BitVec (edgeCount 12)) :=
  missing312_314 ++ missing314_316
abbrev records312_316 : List Blob :=
  records312_314 ++ records314_316
theorem aligned312_316 :
    AlignedValid 12 1 missing312_316 records312_316 :=
  aligned312_314.append aligned314_316

def missing316_317 : List (BitVec (edgeCount 12)) :=
  [missing316]
abbrev records316_317 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record316]
theorem aligned316_317 :
    AlignedValid 12 1 missing316_317 records316_317 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check316
    maskCheck316 AlignedValid.nil

def missing317_318 : List (BitVec (edgeCount 12)) :=
  [missing317]
abbrev records317_318 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record317]
theorem aligned317_318 :
    AlignedValid 12 1 missing317_318 records317_318 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check317
    maskCheck317 AlignedValid.nil

def missing316_318 : List (BitVec (edgeCount 12)) :=
  missing316_317 ++ missing317_318
abbrev records316_318 : List Blob :=
  records316_317 ++ records317_318
theorem aligned316_318 :
    AlignedValid 12 1 missing316_318 records316_318 :=
  aligned316_317.append aligned317_318

def missing318_319 : List (BitVec (edgeCount 12)) :=
  [missing318]
abbrev records318_319 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record318]
theorem aligned318_319 :
    AlignedValid 12 1 missing318_319 records318_319 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check318
    maskCheck318 AlignedValid.nil

def missing319_320 : List (BitVec (edgeCount 12)) :=
  [missing319]
abbrev records319_320 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record319]
theorem aligned319_320 :
    AlignedValid 12 1 missing319_320 records319_320 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check319
    maskCheck319 AlignedValid.nil

def missing318_320 : List (BitVec (edgeCount 12)) :=
  missing318_319 ++ missing319_320
abbrev records318_320 : List Blob :=
  records318_319 ++ records319_320
theorem aligned318_320 :
    AlignedValid 12 1 missing318_320 records318_320 :=
  aligned318_319.append aligned319_320

def missing316_320 : List (BitVec (edgeCount 12)) :=
  missing316_318 ++ missing318_320
abbrev records316_320 : List Blob :=
  records316_318 ++ records318_320
theorem aligned316_320 :
    AlignedValid 12 1 missing316_320 records316_320 :=
  aligned316_318.append aligned318_320

def missing312_320 : List (BitVec (edgeCount 12)) :=
  missing312_316 ++ missing316_320
abbrev records312_320 : List Blob :=
  records312_316 ++ records316_320
theorem aligned312_320 :
    AlignedValid 12 1 missing312_320 records312_320 :=
  aligned312_316.append aligned316_320

def missing304_320 : List (BitVec (edgeCount 12)) :=
  missing304_312 ++ missing312_320
abbrev records304_320 : List Blob :=
  records304_312 ++ records312_320
theorem aligned304_320 :
    AlignedValid 12 1 missing304_320 records304_320 :=
  aligned304_312.append aligned312_320

def missing288_320 : List (BitVec (edgeCount 12)) :=
  missing288_304 ++ missing304_320
abbrev records288_320 : List Blob :=
  records288_304 ++ records304_320
theorem aligned288_320 :
    AlignedValid 12 1 missing288_320 records288_320 :=
  aligned288_304.append aligned304_320

def missing256_320 : List (BitVec (edgeCount 12)) :=
  missing256_288 ++ missing288_320
abbrev records256_320 : List Blob :=
  records256_288 ++ records288_320
theorem aligned256_320 :
    AlignedValid 12 1 missing256_320 records256_320 :=
  aligned256_288.append aligned288_320

def missing320_321 : List (BitVec (edgeCount 12)) :=
  [missing320]
abbrev records320_321 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record320]
theorem aligned320_321 :
    AlignedValid 12 1 missing320_321 records320_321 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check320
    maskCheck320 AlignedValid.nil

def missing321_322 : List (BitVec (edgeCount 12)) :=
  [missing321]
abbrev records321_322 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record321]
theorem aligned321_322 :
    AlignedValid 12 1 missing321_322 records321_322 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check321
    maskCheck321 AlignedValid.nil

def missing320_322 : List (BitVec (edgeCount 12)) :=
  missing320_321 ++ missing321_322
abbrev records320_322 : List Blob :=
  records320_321 ++ records321_322
theorem aligned320_322 :
    AlignedValid 12 1 missing320_322 records320_322 :=
  aligned320_321.append aligned321_322

def missing322_323 : List (BitVec (edgeCount 12)) :=
  [missing322]
abbrev records322_323 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record322]
theorem aligned322_323 :
    AlignedValid 12 1 missing322_323 records322_323 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check322
    maskCheck322 AlignedValid.nil

def missing323_324 : List (BitVec (edgeCount 12)) :=
  [missing323]
abbrev records323_324 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record323]
theorem aligned323_324 :
    AlignedValid 12 1 missing323_324 records323_324 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check323
    maskCheck323 AlignedValid.nil

def missing322_324 : List (BitVec (edgeCount 12)) :=
  missing322_323 ++ missing323_324
abbrev records322_324 : List Blob :=
  records322_323 ++ records323_324
theorem aligned322_324 :
    AlignedValid 12 1 missing322_324 records322_324 :=
  aligned322_323.append aligned323_324

def missing320_324 : List (BitVec (edgeCount 12)) :=
  missing320_322 ++ missing322_324
abbrev records320_324 : List Blob :=
  records320_322 ++ records322_324
theorem aligned320_324 :
    AlignedValid 12 1 missing320_324 records320_324 :=
  aligned320_322.append aligned322_324

def missing324_325 : List (BitVec (edgeCount 12)) :=
  [missing324]
abbrev records324_325 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record324]
theorem aligned324_325 :
    AlignedValid 12 1 missing324_325 records324_325 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check324
    maskCheck324 AlignedValid.nil

def missing325_326 : List (BitVec (edgeCount 12)) :=
  [missing325]
abbrev records325_326 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record325]
theorem aligned325_326 :
    AlignedValid 12 1 missing325_326 records325_326 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check325
    maskCheck325 AlignedValid.nil

def missing324_326 : List (BitVec (edgeCount 12)) :=
  missing324_325 ++ missing325_326
abbrev records324_326 : List Blob :=
  records324_325 ++ records325_326
theorem aligned324_326 :
    AlignedValid 12 1 missing324_326 records324_326 :=
  aligned324_325.append aligned325_326

def missing326_327 : List (BitVec (edgeCount 12)) :=
  [missing326]
abbrev records326_327 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record326]
theorem aligned326_327 :
    AlignedValid 12 1 missing326_327 records326_327 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check326
    maskCheck326 AlignedValid.nil

def missing327_328 : List (BitVec (edgeCount 12)) :=
  [missing327]
abbrev records327_328 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record327]
theorem aligned327_328 :
    AlignedValid 12 1 missing327_328 records327_328 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check327
    maskCheck327 AlignedValid.nil

def missing326_328 : List (BitVec (edgeCount 12)) :=
  missing326_327 ++ missing327_328
abbrev records326_328 : List Blob :=
  records326_327 ++ records327_328
theorem aligned326_328 :
    AlignedValid 12 1 missing326_328 records326_328 :=
  aligned326_327.append aligned327_328

def missing324_328 : List (BitVec (edgeCount 12)) :=
  missing324_326 ++ missing326_328
abbrev records324_328 : List Blob :=
  records324_326 ++ records326_328
theorem aligned324_328 :
    AlignedValid 12 1 missing324_328 records324_328 :=
  aligned324_326.append aligned326_328

def missing320_328 : List (BitVec (edgeCount 12)) :=
  missing320_324 ++ missing324_328
abbrev records320_328 : List Blob :=
  records320_324 ++ records324_328
theorem aligned320_328 :
    AlignedValid 12 1 missing320_328 records320_328 :=
  aligned320_324.append aligned324_328

def missing328_329 : List (BitVec (edgeCount 12)) :=
  [missing328]
abbrev records328_329 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record328]
theorem aligned328_329 :
    AlignedValid 12 1 missing328_329 records328_329 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check328
    maskCheck328 AlignedValid.nil

def missing329_330 : List (BitVec (edgeCount 12)) :=
  [missing329]
abbrev records329_330 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record329]
theorem aligned329_330 :
    AlignedValid 12 1 missing329_330 records329_330 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check329
    maskCheck329 AlignedValid.nil

def missing328_330 : List (BitVec (edgeCount 12)) :=
  missing328_329 ++ missing329_330
abbrev records328_330 : List Blob :=
  records328_329 ++ records329_330
theorem aligned328_330 :
    AlignedValid 12 1 missing328_330 records328_330 :=
  aligned328_329.append aligned329_330

def missing330_331 : List (BitVec (edgeCount 12)) :=
  [missing330]
abbrev records330_331 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record330]
theorem aligned330_331 :
    AlignedValid 12 1 missing330_331 records330_331 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check330
    maskCheck330 AlignedValid.nil

def missing331_332 : List (BitVec (edgeCount 12)) :=
  [missing331]
abbrev records331_332 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record331]
theorem aligned331_332 :
    AlignedValid 12 1 missing331_332 records331_332 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check331
    maskCheck331 AlignedValid.nil

def missing330_332 : List (BitVec (edgeCount 12)) :=
  missing330_331 ++ missing331_332
abbrev records330_332 : List Blob :=
  records330_331 ++ records331_332
theorem aligned330_332 :
    AlignedValid 12 1 missing330_332 records330_332 :=
  aligned330_331.append aligned331_332

def missing328_332 : List (BitVec (edgeCount 12)) :=
  missing328_330 ++ missing330_332
abbrev records328_332 : List Blob :=
  records328_330 ++ records330_332
theorem aligned328_332 :
    AlignedValid 12 1 missing328_332 records328_332 :=
  aligned328_330.append aligned330_332

def missing332_333 : List (BitVec (edgeCount 12)) :=
  [missing332]
abbrev records332_333 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record332]
theorem aligned332_333 :
    AlignedValid 12 1 missing332_333 records332_333 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check332
    maskCheck332 AlignedValid.nil

def missing333_334 : List (BitVec (edgeCount 12)) :=
  [missing333]
abbrev records333_334 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record333]
theorem aligned333_334 :
    AlignedValid 12 1 missing333_334 records333_334 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check333
    maskCheck333 AlignedValid.nil

def missing332_334 : List (BitVec (edgeCount 12)) :=
  missing332_333 ++ missing333_334
abbrev records332_334 : List Blob :=
  records332_333 ++ records333_334
theorem aligned332_334 :
    AlignedValid 12 1 missing332_334 records332_334 :=
  aligned332_333.append aligned333_334

def missing334_335 : List (BitVec (edgeCount 12)) :=
  [missing334]
abbrev records334_335 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record334]
theorem aligned334_335 :
    AlignedValid 12 1 missing334_335 records334_335 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check334
    maskCheck334 AlignedValid.nil

def missing335_336 : List (BitVec (edgeCount 12)) :=
  [missing335]
abbrev records335_336 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record335]
theorem aligned335_336 :
    AlignedValid 12 1 missing335_336 records335_336 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check335
    maskCheck335 AlignedValid.nil

def missing334_336 : List (BitVec (edgeCount 12)) :=
  missing334_335 ++ missing335_336
abbrev records334_336 : List Blob :=
  records334_335 ++ records335_336
theorem aligned334_336 :
    AlignedValid 12 1 missing334_336 records334_336 :=
  aligned334_335.append aligned335_336

def missing332_336 : List (BitVec (edgeCount 12)) :=
  missing332_334 ++ missing334_336
abbrev records332_336 : List Blob :=
  records332_334 ++ records334_336
theorem aligned332_336 :
    AlignedValid 12 1 missing332_336 records332_336 :=
  aligned332_334.append aligned334_336

def missing328_336 : List (BitVec (edgeCount 12)) :=
  missing328_332 ++ missing332_336
abbrev records328_336 : List Blob :=
  records328_332 ++ records332_336
theorem aligned328_336 :
    AlignedValid 12 1 missing328_336 records328_336 :=
  aligned328_332.append aligned332_336

def missing320_336 : List (BitVec (edgeCount 12)) :=
  missing320_328 ++ missing328_336
abbrev records320_336 : List Blob :=
  records320_328 ++ records328_336
theorem aligned320_336 :
    AlignedValid 12 1 missing320_336 records320_336 :=
  aligned320_328.append aligned328_336

def missing336_337 : List (BitVec (edgeCount 12)) :=
  [missing336]
abbrev records336_337 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record336]
theorem aligned336_337 :
    AlignedValid 12 1 missing336_337 records336_337 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check336
    maskCheck336 AlignedValid.nil

def missing337_338 : List (BitVec (edgeCount 12)) :=
  [missing337]
abbrev records337_338 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record337]
theorem aligned337_338 :
    AlignedValid 12 1 missing337_338 records337_338 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check337
    maskCheck337 AlignedValid.nil

def missing336_338 : List (BitVec (edgeCount 12)) :=
  missing336_337 ++ missing337_338
abbrev records336_338 : List Blob :=
  records336_337 ++ records337_338
theorem aligned336_338 :
    AlignedValid 12 1 missing336_338 records336_338 :=
  aligned336_337.append aligned337_338

def missing338_339 : List (BitVec (edgeCount 12)) :=
  [missing338]
abbrev records338_339 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record338]
theorem aligned338_339 :
    AlignedValid 12 1 missing338_339 records338_339 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check338
    maskCheck338 AlignedValid.nil

def missing339_340 : List (BitVec (edgeCount 12)) :=
  [missing339]
abbrev records339_340 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record339]
theorem aligned339_340 :
    AlignedValid 12 1 missing339_340 records339_340 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check339
    maskCheck339 AlignedValid.nil

def missing338_340 : List (BitVec (edgeCount 12)) :=
  missing338_339 ++ missing339_340
abbrev records338_340 : List Blob :=
  records338_339 ++ records339_340
theorem aligned338_340 :
    AlignedValid 12 1 missing338_340 records338_340 :=
  aligned338_339.append aligned339_340

def missing336_340 : List (BitVec (edgeCount 12)) :=
  missing336_338 ++ missing338_340
abbrev records336_340 : List Blob :=
  records336_338 ++ records338_340
theorem aligned336_340 :
    AlignedValid 12 1 missing336_340 records336_340 :=
  aligned336_338.append aligned338_340

def missing340_341 : List (BitVec (edgeCount 12)) :=
  [missing340]
abbrev records340_341 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record340]
theorem aligned340_341 :
    AlignedValid 12 1 missing340_341 records340_341 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check340
    maskCheck340 AlignedValid.nil

def missing341_342 : List (BitVec (edgeCount 12)) :=
  [missing341]
abbrev records341_342 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record341]
theorem aligned341_342 :
    AlignedValid 12 1 missing341_342 records341_342 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check341
    maskCheck341 AlignedValid.nil

def missing340_342 : List (BitVec (edgeCount 12)) :=
  missing340_341 ++ missing341_342
abbrev records340_342 : List Blob :=
  records340_341 ++ records341_342
theorem aligned340_342 :
    AlignedValid 12 1 missing340_342 records340_342 :=
  aligned340_341.append aligned341_342

def missing342_343 : List (BitVec (edgeCount 12)) :=
  [missing342]
abbrev records342_343 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record342]
theorem aligned342_343 :
    AlignedValid 12 1 missing342_343 records342_343 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check342
    maskCheck342 AlignedValid.nil

def missing343_344 : List (BitVec (edgeCount 12)) :=
  [missing343]
abbrev records343_344 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record343]
theorem aligned343_344 :
    AlignedValid 12 1 missing343_344 records343_344 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check343
    maskCheck343 AlignedValid.nil

def missing342_344 : List (BitVec (edgeCount 12)) :=
  missing342_343 ++ missing343_344
abbrev records342_344 : List Blob :=
  records342_343 ++ records343_344
theorem aligned342_344 :
    AlignedValid 12 1 missing342_344 records342_344 :=
  aligned342_343.append aligned343_344

def missing340_344 : List (BitVec (edgeCount 12)) :=
  missing340_342 ++ missing342_344
abbrev records340_344 : List Blob :=
  records340_342 ++ records342_344
theorem aligned340_344 :
    AlignedValid 12 1 missing340_344 records340_344 :=
  aligned340_342.append aligned342_344

def missing336_344 : List (BitVec (edgeCount 12)) :=
  missing336_340 ++ missing340_344
abbrev records336_344 : List Blob :=
  records336_340 ++ records340_344
theorem aligned336_344 :
    AlignedValid 12 1 missing336_344 records336_344 :=
  aligned336_340.append aligned340_344

def missing344_345 : List (BitVec (edgeCount 12)) :=
  [missing344]
abbrev records344_345 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record344]
theorem aligned344_345 :
    AlignedValid 12 1 missing344_345 records344_345 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check344
    maskCheck344 AlignedValid.nil

def missing345_346 : List (BitVec (edgeCount 12)) :=
  [missing345]
abbrev records345_346 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record345]
theorem aligned345_346 :
    AlignedValid 12 1 missing345_346 records345_346 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check345
    maskCheck345 AlignedValid.nil

def missing344_346 : List (BitVec (edgeCount 12)) :=
  missing344_345 ++ missing345_346
abbrev records344_346 : List Blob :=
  records344_345 ++ records345_346
theorem aligned344_346 :
    AlignedValid 12 1 missing344_346 records344_346 :=
  aligned344_345.append aligned345_346

def missing346_347 : List (BitVec (edgeCount 12)) :=
  [missing346]
abbrev records346_347 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record346]
theorem aligned346_347 :
    AlignedValid 12 1 missing346_347 records346_347 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check346
    maskCheck346 AlignedValid.nil

def missing347_348 : List (BitVec (edgeCount 12)) :=
  [missing347]
abbrev records347_348 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record347]
theorem aligned347_348 :
    AlignedValid 12 1 missing347_348 records347_348 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check347
    maskCheck347 AlignedValid.nil

def missing346_348 : List (BitVec (edgeCount 12)) :=
  missing346_347 ++ missing347_348
abbrev records346_348 : List Blob :=
  records346_347 ++ records347_348
theorem aligned346_348 :
    AlignedValid 12 1 missing346_348 records346_348 :=
  aligned346_347.append aligned347_348

def missing344_348 : List (BitVec (edgeCount 12)) :=
  missing344_346 ++ missing346_348
abbrev records344_348 : List Blob :=
  records344_346 ++ records346_348
theorem aligned344_348 :
    AlignedValid 12 1 missing344_348 records344_348 :=
  aligned344_346.append aligned346_348

def missing348_349 : List (BitVec (edgeCount 12)) :=
  [missing348]
abbrev records348_349 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record348]
theorem aligned348_349 :
    AlignedValid 12 1 missing348_349 records348_349 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check348
    maskCheck348 AlignedValid.nil

def missing349_350 : List (BitVec (edgeCount 12)) :=
  [missing349]
abbrev records349_350 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record349]
theorem aligned349_350 :
    AlignedValid 12 1 missing349_350 records349_350 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check349
    maskCheck349 AlignedValid.nil

def missing348_350 : List (BitVec (edgeCount 12)) :=
  missing348_349 ++ missing349_350
abbrev records348_350 : List Blob :=
  records348_349 ++ records349_350
theorem aligned348_350 :
    AlignedValid 12 1 missing348_350 records348_350 :=
  aligned348_349.append aligned349_350

def missing350_351 : List (BitVec (edgeCount 12)) :=
  [missing350]
abbrev records350_351 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record350]
theorem aligned350_351 :
    AlignedValid 12 1 missing350_351 records350_351 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check350
    maskCheck350 AlignedValid.nil

def missing351_352 : List (BitVec (edgeCount 12)) :=
  [missing351]
abbrev records351_352 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record351]
theorem aligned351_352 :
    AlignedValid 12 1 missing351_352 records351_352 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check351
    maskCheck351 AlignedValid.nil

def missing350_352 : List (BitVec (edgeCount 12)) :=
  missing350_351 ++ missing351_352
abbrev records350_352 : List Blob :=
  records350_351 ++ records351_352
theorem aligned350_352 :
    AlignedValid 12 1 missing350_352 records350_352 :=
  aligned350_351.append aligned351_352

def missing348_352 : List (BitVec (edgeCount 12)) :=
  missing348_350 ++ missing350_352
abbrev records348_352 : List Blob :=
  records348_350 ++ records350_352
theorem aligned348_352 :
    AlignedValid 12 1 missing348_352 records348_352 :=
  aligned348_350.append aligned350_352

def missing344_352 : List (BitVec (edgeCount 12)) :=
  missing344_348 ++ missing348_352
abbrev records344_352 : List Blob :=
  records344_348 ++ records348_352
theorem aligned344_352 :
    AlignedValid 12 1 missing344_352 records344_352 :=
  aligned344_348.append aligned348_352

def missing336_352 : List (BitVec (edgeCount 12)) :=
  missing336_344 ++ missing344_352
abbrev records336_352 : List Blob :=
  records336_344 ++ records344_352
theorem aligned336_352 :
    AlignedValid 12 1 missing336_352 records336_352 :=
  aligned336_344.append aligned344_352

def missing320_352 : List (BitVec (edgeCount 12)) :=
  missing320_336 ++ missing336_352
abbrev records320_352 : List Blob :=
  records320_336 ++ records336_352
theorem aligned320_352 :
    AlignedValid 12 1 missing320_352 records320_352 :=
  aligned320_336.append aligned336_352

def missing352_353 : List (BitVec (edgeCount 12)) :=
  [missing352]
abbrev records352_353 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record352]
theorem aligned352_353 :
    AlignedValid 12 1 missing352_353 records352_353 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check352
    maskCheck352 AlignedValid.nil

def missing353_354 : List (BitVec (edgeCount 12)) :=
  [missing353]
abbrev records353_354 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record353]
theorem aligned353_354 :
    AlignedValid 12 1 missing353_354 records353_354 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check353
    maskCheck353 AlignedValid.nil

def missing352_354 : List (BitVec (edgeCount 12)) :=
  missing352_353 ++ missing353_354
abbrev records352_354 : List Blob :=
  records352_353 ++ records353_354
theorem aligned352_354 :
    AlignedValid 12 1 missing352_354 records352_354 :=
  aligned352_353.append aligned353_354

def missing354_355 : List (BitVec (edgeCount 12)) :=
  [missing354]
abbrev records354_355 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record354]
theorem aligned354_355 :
    AlignedValid 12 1 missing354_355 records354_355 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check354
    maskCheck354 AlignedValid.nil

def missing355_356 : List (BitVec (edgeCount 12)) :=
  [missing355]
abbrev records355_356 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record355]
theorem aligned355_356 :
    AlignedValid 12 1 missing355_356 records355_356 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check355
    maskCheck355 AlignedValid.nil

def missing354_356 : List (BitVec (edgeCount 12)) :=
  missing354_355 ++ missing355_356
abbrev records354_356 : List Blob :=
  records354_355 ++ records355_356
theorem aligned354_356 :
    AlignedValid 12 1 missing354_356 records354_356 :=
  aligned354_355.append aligned355_356

def missing352_356 : List (BitVec (edgeCount 12)) :=
  missing352_354 ++ missing354_356
abbrev records352_356 : List Blob :=
  records352_354 ++ records354_356
theorem aligned352_356 :
    AlignedValid 12 1 missing352_356 records352_356 :=
  aligned352_354.append aligned354_356

def missing356_357 : List (BitVec (edgeCount 12)) :=
  [missing356]
abbrev records356_357 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record356]
theorem aligned356_357 :
    AlignedValid 12 1 missing356_357 records356_357 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check356
    maskCheck356 AlignedValid.nil

def missing357_358 : List (BitVec (edgeCount 12)) :=
  [missing357]
abbrev records357_358 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record357]
theorem aligned357_358 :
    AlignedValid 12 1 missing357_358 records357_358 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check357
    maskCheck357 AlignedValid.nil

def missing356_358 : List (BitVec (edgeCount 12)) :=
  missing356_357 ++ missing357_358
abbrev records356_358 : List Blob :=
  records356_357 ++ records357_358
theorem aligned356_358 :
    AlignedValid 12 1 missing356_358 records356_358 :=
  aligned356_357.append aligned357_358

def missing358_359 : List (BitVec (edgeCount 12)) :=
  [missing358]
abbrev records358_359 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record358]
theorem aligned358_359 :
    AlignedValid 12 1 missing358_359 records358_359 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check358
    maskCheck358 AlignedValid.nil

def missing359_360 : List (BitVec (edgeCount 12)) :=
  [missing359]
abbrev records359_360 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record359]
theorem aligned359_360 :
    AlignedValid 12 1 missing359_360 records359_360 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check359
    maskCheck359 AlignedValid.nil

def missing358_360 : List (BitVec (edgeCount 12)) :=
  missing358_359 ++ missing359_360
abbrev records358_360 : List Blob :=
  records358_359 ++ records359_360
theorem aligned358_360 :
    AlignedValid 12 1 missing358_360 records358_360 :=
  aligned358_359.append aligned359_360

def missing356_360 : List (BitVec (edgeCount 12)) :=
  missing356_358 ++ missing358_360
abbrev records356_360 : List Blob :=
  records356_358 ++ records358_360
theorem aligned356_360 :
    AlignedValid 12 1 missing356_360 records356_360 :=
  aligned356_358.append aligned358_360

def missing352_360 : List (BitVec (edgeCount 12)) :=
  missing352_356 ++ missing356_360
abbrev records352_360 : List Blob :=
  records352_356 ++ records356_360
theorem aligned352_360 :
    AlignedValid 12 1 missing352_360 records352_360 :=
  aligned352_356.append aligned356_360

def missing360_361 : List (BitVec (edgeCount 12)) :=
  [missing360]
abbrev records360_361 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record360]
theorem aligned360_361 :
    AlignedValid 12 1 missing360_361 records360_361 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check360
    maskCheck360 AlignedValid.nil

def missing361_362 : List (BitVec (edgeCount 12)) :=
  [missing361]
abbrev records361_362 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record361]
theorem aligned361_362 :
    AlignedValid 12 1 missing361_362 records361_362 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check361
    maskCheck361 AlignedValid.nil

def missing360_362 : List (BitVec (edgeCount 12)) :=
  missing360_361 ++ missing361_362
abbrev records360_362 : List Blob :=
  records360_361 ++ records361_362
theorem aligned360_362 :
    AlignedValid 12 1 missing360_362 records360_362 :=
  aligned360_361.append aligned361_362

def missing362_363 : List (BitVec (edgeCount 12)) :=
  [missing362]
abbrev records362_363 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record362]
theorem aligned362_363 :
    AlignedValid 12 1 missing362_363 records362_363 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check362
    maskCheck362 AlignedValid.nil

def missing363_364 : List (BitVec (edgeCount 12)) :=
  [missing363]
abbrev records363_364 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record363]
theorem aligned363_364 :
    AlignedValid 12 1 missing363_364 records363_364 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check363
    maskCheck363 AlignedValid.nil

def missing362_364 : List (BitVec (edgeCount 12)) :=
  missing362_363 ++ missing363_364
abbrev records362_364 : List Blob :=
  records362_363 ++ records363_364
theorem aligned362_364 :
    AlignedValid 12 1 missing362_364 records362_364 :=
  aligned362_363.append aligned363_364

def missing360_364 : List (BitVec (edgeCount 12)) :=
  missing360_362 ++ missing362_364
abbrev records360_364 : List Blob :=
  records360_362 ++ records362_364
theorem aligned360_364 :
    AlignedValid 12 1 missing360_364 records360_364 :=
  aligned360_362.append aligned362_364

def missing364_365 : List (BitVec (edgeCount 12)) :=
  [missing364]
abbrev records364_365 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record364]
theorem aligned364_365 :
    AlignedValid 12 1 missing364_365 records364_365 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check364
    maskCheck364 AlignedValid.nil

def missing365_366 : List (BitVec (edgeCount 12)) :=
  [missing365]
abbrev records365_366 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record365]
theorem aligned365_366 :
    AlignedValid 12 1 missing365_366 records365_366 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check365
    maskCheck365 AlignedValid.nil

def missing364_366 : List (BitVec (edgeCount 12)) :=
  missing364_365 ++ missing365_366
abbrev records364_366 : List Blob :=
  records364_365 ++ records365_366
theorem aligned364_366 :
    AlignedValid 12 1 missing364_366 records364_366 :=
  aligned364_365.append aligned365_366

def missing366_367 : List (BitVec (edgeCount 12)) :=
  [missing366]
abbrev records366_367 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record366]
theorem aligned366_367 :
    AlignedValid 12 1 missing366_367 records366_367 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check366
    maskCheck366 AlignedValid.nil

def missing367_368 : List (BitVec (edgeCount 12)) :=
  [missing367]
abbrev records367_368 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record367]
theorem aligned367_368 :
    AlignedValid 12 1 missing367_368 records367_368 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check367
    maskCheck367 AlignedValid.nil

def missing366_368 : List (BitVec (edgeCount 12)) :=
  missing366_367 ++ missing367_368
abbrev records366_368 : List Blob :=
  records366_367 ++ records367_368
theorem aligned366_368 :
    AlignedValid 12 1 missing366_368 records366_368 :=
  aligned366_367.append aligned367_368

def missing364_368 : List (BitVec (edgeCount 12)) :=
  missing364_366 ++ missing366_368
abbrev records364_368 : List Blob :=
  records364_366 ++ records366_368
theorem aligned364_368 :
    AlignedValid 12 1 missing364_368 records364_368 :=
  aligned364_366.append aligned366_368

def missing360_368 : List (BitVec (edgeCount 12)) :=
  missing360_364 ++ missing364_368
abbrev records360_368 : List Blob :=
  records360_364 ++ records364_368
theorem aligned360_368 :
    AlignedValid 12 1 missing360_368 records360_368 :=
  aligned360_364.append aligned364_368

def missing352_368 : List (BitVec (edgeCount 12)) :=
  missing352_360 ++ missing360_368
abbrev records352_368 : List Blob :=
  records352_360 ++ records360_368
theorem aligned352_368 :
    AlignedValid 12 1 missing352_368 records352_368 :=
  aligned352_360.append aligned360_368

def missing368_369 : List (BitVec (edgeCount 12)) :=
  [missing368]
abbrev records368_369 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record368]
theorem aligned368_369 :
    AlignedValid 12 1 missing368_369 records368_369 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check368
    maskCheck368 AlignedValid.nil

def missing369_370 : List (BitVec (edgeCount 12)) :=
  [missing369]
abbrev records369_370 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record369]
theorem aligned369_370 :
    AlignedValid 12 1 missing369_370 records369_370 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check369
    maskCheck369 AlignedValid.nil

def missing368_370 : List (BitVec (edgeCount 12)) :=
  missing368_369 ++ missing369_370
abbrev records368_370 : List Blob :=
  records368_369 ++ records369_370
theorem aligned368_370 :
    AlignedValid 12 1 missing368_370 records368_370 :=
  aligned368_369.append aligned369_370

def missing370_371 : List (BitVec (edgeCount 12)) :=
  [missing370]
abbrev records370_371 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record370]
theorem aligned370_371 :
    AlignedValid 12 1 missing370_371 records370_371 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check370
    maskCheck370 AlignedValid.nil

def missing371_372 : List (BitVec (edgeCount 12)) :=
  [missing371]
abbrev records371_372 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record371]
theorem aligned371_372 :
    AlignedValid 12 1 missing371_372 records371_372 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check371
    maskCheck371 AlignedValid.nil

def missing370_372 : List (BitVec (edgeCount 12)) :=
  missing370_371 ++ missing371_372
abbrev records370_372 : List Blob :=
  records370_371 ++ records371_372
theorem aligned370_372 :
    AlignedValid 12 1 missing370_372 records370_372 :=
  aligned370_371.append aligned371_372

def missing368_372 : List (BitVec (edgeCount 12)) :=
  missing368_370 ++ missing370_372
abbrev records368_372 : List Blob :=
  records368_370 ++ records370_372
theorem aligned368_372 :
    AlignedValid 12 1 missing368_372 records368_372 :=
  aligned368_370.append aligned370_372

def missing372_373 : List (BitVec (edgeCount 12)) :=
  [missing372]
abbrev records372_373 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record372]
theorem aligned372_373 :
    AlignedValid 12 1 missing372_373 records372_373 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check372
    maskCheck372 AlignedValid.nil

def missing373_374 : List (BitVec (edgeCount 12)) :=
  [missing373]
abbrev records373_374 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record373]
theorem aligned373_374 :
    AlignedValid 12 1 missing373_374 records373_374 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check373
    maskCheck373 AlignedValid.nil

def missing372_374 : List (BitVec (edgeCount 12)) :=
  missing372_373 ++ missing373_374
abbrev records372_374 : List Blob :=
  records372_373 ++ records373_374
theorem aligned372_374 :
    AlignedValid 12 1 missing372_374 records372_374 :=
  aligned372_373.append aligned373_374

def missing374_375 : List (BitVec (edgeCount 12)) :=
  [missing374]
abbrev records374_375 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record374]
theorem aligned374_375 :
    AlignedValid 12 1 missing374_375 records374_375 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check374
    maskCheck374 AlignedValid.nil

def missing375_376 : List (BitVec (edgeCount 12)) :=
  [missing375]
abbrev records375_376 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record375]
theorem aligned375_376 :
    AlignedValid 12 1 missing375_376 records375_376 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check375
    maskCheck375 AlignedValid.nil

def missing374_376 : List (BitVec (edgeCount 12)) :=
  missing374_375 ++ missing375_376
abbrev records374_376 : List Blob :=
  records374_375 ++ records375_376
theorem aligned374_376 :
    AlignedValid 12 1 missing374_376 records374_376 :=
  aligned374_375.append aligned375_376

def missing372_376 : List (BitVec (edgeCount 12)) :=
  missing372_374 ++ missing374_376
abbrev records372_376 : List Blob :=
  records372_374 ++ records374_376
theorem aligned372_376 :
    AlignedValid 12 1 missing372_376 records372_376 :=
  aligned372_374.append aligned374_376

def missing368_376 : List (BitVec (edgeCount 12)) :=
  missing368_372 ++ missing372_376
abbrev records368_376 : List Blob :=
  records368_372 ++ records372_376
theorem aligned368_376 :
    AlignedValid 12 1 missing368_376 records368_376 :=
  aligned368_372.append aligned372_376

def missing376_377 : List (BitVec (edgeCount 12)) :=
  [missing376]
abbrev records376_377 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record376]
theorem aligned376_377 :
    AlignedValid 12 1 missing376_377 records376_377 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check376
    maskCheck376 AlignedValid.nil

def missing377_378 : List (BitVec (edgeCount 12)) :=
  [missing377]
abbrev records377_378 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record377]
theorem aligned377_378 :
    AlignedValid 12 1 missing377_378 records377_378 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check377
    maskCheck377 AlignedValid.nil

def missing376_378 : List (BitVec (edgeCount 12)) :=
  missing376_377 ++ missing377_378
abbrev records376_378 : List Blob :=
  records376_377 ++ records377_378
theorem aligned376_378 :
    AlignedValid 12 1 missing376_378 records376_378 :=
  aligned376_377.append aligned377_378

def missing378_379 : List (BitVec (edgeCount 12)) :=
  [missing378]
abbrev records378_379 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record378]
theorem aligned378_379 :
    AlignedValid 12 1 missing378_379 records378_379 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check378
    maskCheck378 AlignedValid.nil

def missing379_380 : List (BitVec (edgeCount 12)) :=
  [missing379]
abbrev records379_380 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record379]
theorem aligned379_380 :
    AlignedValid 12 1 missing379_380 records379_380 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check379
    maskCheck379 AlignedValid.nil

def missing378_380 : List (BitVec (edgeCount 12)) :=
  missing378_379 ++ missing379_380
abbrev records378_380 : List Blob :=
  records378_379 ++ records379_380
theorem aligned378_380 :
    AlignedValid 12 1 missing378_380 records378_380 :=
  aligned378_379.append aligned379_380

def missing376_380 : List (BitVec (edgeCount 12)) :=
  missing376_378 ++ missing378_380
abbrev records376_380 : List Blob :=
  records376_378 ++ records378_380
theorem aligned376_380 :
    AlignedValid 12 1 missing376_380 records376_380 :=
  aligned376_378.append aligned378_380

def missing380_381 : List (BitVec (edgeCount 12)) :=
  [missing380]
abbrev records380_381 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record380]
theorem aligned380_381 :
    AlignedValid 12 1 missing380_381 records380_381 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check380
    maskCheck380 AlignedValid.nil

def missing381_382 : List (BitVec (edgeCount 12)) :=
  [missing381]
abbrev records381_382 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record381]
theorem aligned381_382 :
    AlignedValid 12 1 missing381_382 records381_382 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check381
    maskCheck381 AlignedValid.nil

def missing380_382 : List (BitVec (edgeCount 12)) :=
  missing380_381 ++ missing381_382
abbrev records380_382 : List Blob :=
  records380_381 ++ records381_382
theorem aligned380_382 :
    AlignedValid 12 1 missing380_382 records380_382 :=
  aligned380_381.append aligned381_382

def missing382_383 : List (BitVec (edgeCount 12)) :=
  [missing382]
abbrev records382_383 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record382]
theorem aligned382_383 :
    AlignedValid 12 1 missing382_383 records382_383 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check382
    maskCheck382 AlignedValid.nil

def missing383_384 : List (BitVec (edgeCount 12)) :=
  [missing383]
abbrev records383_384 : List Blob :=
  [StrongPackedBucketN12A1Shard002.record383]
theorem aligned383_384 :
    AlignedValid 12 1 missing383_384 records383_384 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard002.check383
    maskCheck383 AlignedValid.nil

def missing382_384 : List (BitVec (edgeCount 12)) :=
  missing382_383 ++ missing383_384
abbrev records382_384 : List Blob :=
  records382_383 ++ records383_384
theorem aligned382_384 :
    AlignedValid 12 1 missing382_384 records382_384 :=
  aligned382_383.append aligned383_384

def missing380_384 : List (BitVec (edgeCount 12)) :=
  missing380_382 ++ missing382_384
abbrev records380_384 : List Blob :=
  records380_382 ++ records382_384
theorem aligned380_384 :
    AlignedValid 12 1 missing380_384 records380_384 :=
  aligned380_382.append aligned382_384

def missing376_384 : List (BitVec (edgeCount 12)) :=
  missing376_380 ++ missing380_384
abbrev records376_384 : List Blob :=
  records376_380 ++ records380_384
theorem aligned376_384 :
    AlignedValid 12 1 missing376_384 records376_384 :=
  aligned376_380.append aligned380_384

def missing368_384 : List (BitVec (edgeCount 12)) :=
  missing368_376 ++ missing376_384
abbrev records368_384 : List Blob :=
  records368_376 ++ records376_384
theorem aligned368_384 :
    AlignedValid 12 1 missing368_384 records368_384 :=
  aligned368_376.append aligned376_384

def missing352_384 : List (BitVec (edgeCount 12)) :=
  missing352_368 ++ missing368_384
abbrev records352_384 : List Blob :=
  records352_368 ++ records368_384
theorem aligned352_384 :
    AlignedValid 12 1 missing352_384 records352_384 :=
  aligned352_368.append aligned368_384

def missing320_384 : List (BitVec (edgeCount 12)) :=
  missing320_352 ++ missing352_384
abbrev records320_384 : List Blob :=
  records320_352 ++ records352_384
theorem aligned320_384 :
    AlignedValid 12 1 missing320_384 records320_384 :=
  aligned320_352.append aligned352_384

def missing256_384 : List (BitVec (edgeCount 12)) :=
  missing256_320 ++ missing320_384
abbrev records256_384 : List Blob :=
  records256_320 ++ records320_384
theorem aligned256_384 :
    AlignedValid 12 1 missing256_384 records256_384 :=
  aligned256_320.append aligned320_384

abbrev missing : List (BitVec (edgeCount 12)) := missing256_384
abbrev records : List Blob := records256_384
theorem aligned : AlignedValid 12 1 missing records := aligned256_384

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A1AlignedShard002
