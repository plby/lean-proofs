/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard135

/-! Decode-only alignment checks for n=12, a=4, records 17280--17407. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard135

open PackedBucketCertificate

def missing17280 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4870116056592547840
theorem maskCheck17280 :
    checkMaskFor missing17280 StrongPackedBucketN12A4Shard135.record17280 = true := by
  decide

def missing17281 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5086288838706331648
theorem maskCheck17281 :
    checkMaskFor missing17281 StrongPackedBucketN12A4Shard135.record17281 = true := by
  decide

def missing17282 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5302461620820115456
theorem maskCheck17282 :
    checkMaskFor missing17282 StrongPackedBucketN12A4Shard135.record17282 = true := by
  decide

def missing17283 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5374519214858043392
theorem maskCheck17283 :
    checkMaskFor missing17283 StrongPackedBucketN12A4Shard135.record17283 = true := by
  decide

def missing17284 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6383325531389034496
theorem maskCheck17284 :
    checkMaskFor missing17284 StrongPackedBucketN12A4Shard135.record17284 = true := by
  decide

def missing17285 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7031843877730385920
theorem maskCheck17285 :
    checkMaskFor missing17285 StrongPackedBucketN12A4Shard135.record17285 = true := by
  decide

def missing17286 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7103901471768313856
theorem maskCheck17286 :
    checkMaskFor missing17286 StrongPackedBucketN12A4Shard135.record17286 = true := by
  decide

def missing17287 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7536247035995881472
theorem maskCheck17287 :
    checkMaskFor missing17287 StrongPackedBucketN12A4Shard135.record17287 = true := by
  decide

def missing17288 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9481802075019935744
theorem maskCheck17288 :
    checkMaskFor missing17288 StrongPackedBucketN12A4Shard135.record17288 = true := by
  decide

def missing17289 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9734003654152683520
theorem maskCheck17289 :
    checkMaskFor missing17289 StrongPackedBucketN12A4Shard135.record17289 = true := by
  decide

def missing17290 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9914147639247503360
theorem maskCheck17290 :
    checkMaskFor missing17290 StrongPackedBucketN12A4Shard135.record17290 = true := by
  decide

def missing17291 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10022234030304395264
theorem maskCheck17291 :
    checkMaskFor missing17291 StrongPackedBucketN12A4Shard135.record17291 = true := by
  decide

def missing17292 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11031040346835386368
theorem maskCheck17292 :
    checkMaskFor missing17292 StrongPackedBucketN12A4Shard135.record17292 = true := by
  decide

def missing17293 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11643529896157773824
theorem maskCheck17293 :
    checkMaskFor missing17293 StrongPackedBucketN12A4Shard135.record17293 = true := by
  decide

def missing17294 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11751616287214665728
theorem maskCheck17294 :
    checkMaskFor missing17294 StrongPackedBucketN12A4Shard135.record17294 = true := by
  decide

def missing17295 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12183961851442233344
theorem maskCheck17295 :
    checkMaskFor missing17295 StrongPackedBucketN12A4Shard135.record17295 = true := by
  decide

def missing17296 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13949372905371467776
theorem maskCheck17296 :
    checkMaskFor missing17296 StrongPackedBucketN12A4Shard135.record17296 = true := by
  decide

def missing17297 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18705174111874711552
theorem maskCheck17297 :
    checkMaskFor missing17297 StrongPackedBucketN12A4Shard135.record17297 = true := by
  decide

def missing17298 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18921346893988495360
theorem maskCheck17298 :
    checkMaskFor missing17298 StrongPackedBucketN12A4Shard135.record17298 = true := by
  decide

def missing17299 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18957375691007459328
theorem maskCheck17299 :
    checkMaskFor missing17299 StrongPackedBucketN12A4Shard135.record17299 = true := by
  decide

def missing17300 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23172744942226243584
theorem maskCheck17300 :
    checkMaskFor missing17300 StrongPackedBucketN12A4Shard135.record17300 = true := by
  decide

def missing17301 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23244802536264171520
theorem maskCheck17301 :
    checkMaskFor missing17301 StrongPackedBucketN12A4Shard135.record17301 = true := by
  decide

def missing17302 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27784430960653631488
theorem maskCheck17302 :
    checkMaskFor missing17302 StrongPackedBucketN12A4Shard135.record17302 = true := by
  decide

def missing17303 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27892517351710523392
theorem maskCheck17303 :
    checkMaskFor missing17303 StrongPackedBucketN12A4Shard135.record17303 = true := by
  decide

def missing17304 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13956761623510122496
theorem maskCheck17304 :
    checkMaskFor missing17304 StrongPackedBucketN12A4Shard135.record17304 = true := by
  decide

def missing17305 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 558693469571252224
theorem maskCheck17305 :
    checkMaskFor missing17305 StrongPackedBucketN12A4Shard135.record17305 = true := by
  decide

def missing17306 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 846923845722963968
theorem maskCheck17306 :
    checkMaskFor missing17306 StrongPackedBucketN12A4Shard135.record17306 = true := by
  decide

def missing17307 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 991039033798819840
theorem maskCheck17307 :
    checkMaskFor missing17307 StrongPackedBucketN12A4Shard135.record17307 = true := by
  decide

def missing17308 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4882149111846928384
theorem maskCheck17308 :
    checkMaskFor missing17308 StrongPackedBucketN12A4Shard135.record17308 = true := by
  decide

def missing17309 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5026264299922784256
theorem maskCheck17309 :
    checkMaskFor missing17309 StrongPackedBucketN12A4Shard135.record17309 = true := by
  decide

def missing17310 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5098321893960712192
theorem maskCheck17310 :
    checkMaskFor missing17310 StrongPackedBucketN12A4Shard135.record17310 = true := by
  decide

def missing17311 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5134350690979676160
theorem maskCheck17311 :
    checkMaskFor missing17311 StrongPackedBucketN12A4Shard135.record17311 = true := by
  decide

def missing17312 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5314494676074496000
theorem maskCheck17312 :
    checkMaskFor missing17312 StrongPackedBucketN12A4Shard135.record17312 = true := by
  decide

def missing17313 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5386552270112423936
theorem maskCheck17313 :
    checkMaskFor missing17313 StrongPackedBucketN12A4Shard135.record17313 = true := by
  decide

def missing17314 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5422581067131387904
theorem maskCheck17314 :
    checkMaskFor missing17314 StrongPackedBucketN12A4Shard135.record17314 = true := by
  decide

def missing17315 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5530667458188279808
theorem maskCheck17315 :
    checkMaskFor missing17315 StrongPackedBucketN12A4Shard135.record17315 = true := by
  decide

def missing17316 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5566696255207243776
theorem maskCheck17316 :
    checkMaskFor missing17316 StrongPackedBucketN12A4Shard135.record17316 = true := by
  decide

def missing17317 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13961405960625848320
theorem maskCheck17317 :
    checkMaskFor missing17317 StrongPackedBucketN12A4Shard135.record17317 = true := by
  decide

def missing17318 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14033463554663776256
theorem maskCheck17318 :
    checkMaskFor missing17318 StrongPackedBucketN12A4Shard135.record17318 = true := by
  decide

def missing17319 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14177578742739632128
theorem maskCheck17319 :
    checkMaskFor missing17319 StrongPackedBucketN12A4Shard135.record17319 = true := by
  decide

def missing17320 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14285665133796524032
theorem maskCheck17320 :
    checkMaskFor missing17320 StrongPackedBucketN12A4Shard135.record17320 = true := by
  decide

def missing17321 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14465809118891343872
theorem maskCheck17321 :
    checkMaskFor missing17321 StrongPackedBucketN12A4Shard135.record17321 = true := by
  decide

def missing17322 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14573895509948235776
theorem maskCheck17322 :
    checkMaskFor missing17322 StrongPackedBucketN12A4Shard135.record17322 = true := by
  decide

def missing17323 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14718010698024091648
theorem maskCheck17323 :
    checkMaskFor missing17323 StrongPackedBucketN12A4Shard135.record17323 = true := by
  decide

def missing17324 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 558904575803785216
theorem maskCheck17324 :
    checkMaskFor missing17324 StrongPackedBucketN12A4Shard135.record17324 = true := by
  decide

def missing17325 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 847134951955496960
theorem maskCheck17325 :
    checkMaskFor missing17325 StrongPackedBucketN12A4Shard135.record17325 = true := by
  decide

def missing17326 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1063307734069280768
theorem maskCheck17326 :
    checkMaskFor missing17326 StrongPackedBucketN12A4Shard135.record17326 = true := by
  decide

def missing17327 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1099336531088244736
theorem maskCheck17327 :
    checkMaskFor missing17327 StrongPackedBucketN12A4Shard135.record17327 = true := by
  decide

def missing17328 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4882360218079461376
theorem maskCheck17328 :
    checkMaskFor missing17328 StrongPackedBucketN12A4Shard135.record17328 = true := by
  decide

def missing17329 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5098533000193245184
theorem maskCheck17329 :
    checkMaskFor missing17329 StrongPackedBucketN12A4Shard135.record17329 = true := by
  decide

def missing17330 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5134561797212209152
theorem maskCheck17330 :
    checkMaskFor missing17330 StrongPackedBucketN12A4Shard135.record17330 = true := by
  decide

def missing17331 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5314705782307028992
theorem maskCheck17331 :
    checkMaskFor missing17331 StrongPackedBucketN12A4Shard135.record17331 = true := by
  decide

def missing17332 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5386763376344956928
theorem maskCheck17332 :
    checkMaskFor missing17332 StrongPackedBucketN12A4Shard135.record17332 = true := by
  decide

def missing17333 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5422792173363920896
theorem maskCheck17333 :
    checkMaskFor missing17333 StrongPackedBucketN12A4Shard135.record17333 = true := by
  decide

def missing17334 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5638964955477704704
theorem maskCheck17334 :
    checkMaskFor missing17334 StrongPackedBucketN12A4Shard135.record17334 = true := by
  decide

def missing17335 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9494046236506849280
theorem maskCheck17335 :
    checkMaskFor missing17335 StrongPackedBucketN12A4Shard135.record17335 = true := by
  decide

def missing17336 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9746247815639597056
theorem maskCheck17336 :
    checkMaskFor missing17336 StrongPackedBucketN12A4Shard135.record17336 = true := by
  decide

def missing17337 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9926391800734416896
theorem maskCheck17337 :
    checkMaskFor missing17337 StrongPackedBucketN12A4Shard135.record17337 = true := by
  decide

def missing17338 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10034478191791308800
theorem maskCheck17338 :
    checkMaskFor missing17338 StrongPackedBucketN12A4Shard135.record17338 = true := by
  decide

def missing17339 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13961617066858381312
theorem maskCheck17339 :
    checkMaskFor missing17339 StrongPackedBucketN12A4Shard135.record17339 = true := by
  decide

def missing17340 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14069703457915273216
theorem maskCheck17340 :
    checkMaskFor missing17340 StrongPackedBucketN12A4Shard135.record17340 = true := by
  decide

def missing17341 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14502049022142840832
theorem maskCheck17341 :
    checkMaskFor missing17341 StrongPackedBucketN12A4Shard135.record17341 = true := by
  decide

def missing17342 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 559115682036318208
theorem maskCheck17342 :
    checkMaskFor missing17342 StrongPackedBucketN12A4Shard135.record17342 = true := by
  decide

def missing17343 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 847346058188029952
theorem maskCheck17343 :
    checkMaskFor missing17343 StrongPackedBucketN12A4Shard135.record17343 = true := by
  decide

def missing17344 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1063518840301813760
theorem maskCheck17344 :
    checkMaskFor missing17344 StrongPackedBucketN12A4Shard135.record17344 = true := by
  decide

def missing17345 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1423806810491453440
theorem maskCheck17345 :
    checkMaskFor missing17345 StrongPackedBucketN12A4Shard135.record17345 = true := by
  decide

def missing17346 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1639979592605237248
theorem maskCheck17346 :
    checkMaskFor missing17346 StrongPackedBucketN12A4Shard135.record17346 = true := by
  decide

def missing17347 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1856152374719021056
theorem maskCheck17347 :
    checkMaskFor missing17347 StrongPackedBucketN12A4Shard135.record17347 = true := by
  decide

def missing17348 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3585534631629291520
theorem maskCheck17348 :
    checkMaskFor missing17348 StrongPackedBucketN12A4Shard135.record17348 = true := by
  decide

def missing17349 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4882571324311994368
theorem maskCheck17349 :
    checkMaskFor missing17349 StrongPackedBucketN12A4Shard135.record17349 = true := by
  decide

def missing17350 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5098744106425778176
theorem maskCheck17350 :
    checkMaskFor missing17350 StrongPackedBucketN12A4Shard135.record17350 = true := by
  decide

def missing17351 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5134772903444742144
theorem maskCheck17351 :
    checkMaskFor missing17351 StrongPackedBucketN12A4Shard135.record17351 = true := by
  decide

def missing17352 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5314916888539561984
theorem maskCheck17352 :
    checkMaskFor missing17352 StrongPackedBucketN12A4Shard135.record17352 = true := by
  decide

def missing17353 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5386974482577489920
theorem maskCheck17353 :
    checkMaskFor missing17353 StrongPackedBucketN12A4Shard135.record17353 = true := by
  decide

def missing17354 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5423003279596453888
theorem maskCheck17354 :
    checkMaskFor missing17354 StrongPackedBucketN12A4Shard135.record17354 = true := by
  decide

def missing17355 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5639176061710237696
theorem maskCheck17355 :
    checkMaskFor missing17355 StrongPackedBucketN12A4Shard135.record17355 = true := by
  decide

def missing17356 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5891377640842985472
theorem maskCheck17356 :
    checkMaskFor missing17356 StrongPackedBucketN12A4Shard135.record17356 = true := by
  decide

def missing17357 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5963435234880913408
theorem maskCheck17357 :
    checkMaskFor missing17357 StrongPackedBucketN12A4Shard135.record17357 = true := by
  decide

def missing17358 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5999464031899877376
theorem maskCheck17358 :
    checkMaskFor missing17358 StrongPackedBucketN12A4Shard135.record17358 = true := by
  decide

def missing17359 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6215636814013661184
theorem maskCheck17359 :
    checkMaskFor missing17359 StrongPackedBucketN12A4Shard135.record17359 = true := by
  decide

def missing17360 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6395780799108481024
theorem maskCheck17360 :
    checkMaskFor missing17360 StrongPackedBucketN12A4Shard135.record17360 = true := by
  decide

def missing17361 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6431809596127444992
theorem maskCheck17361 :
    checkMaskFor missing17361 StrongPackedBucketN12A4Shard135.record17361 = true := by
  decide

def missing17362 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8125163056018751488
theorem maskCheck17362 :
    checkMaskFor missing17362 StrongPackedBucketN12A4Shard135.record17362 = true := by
  decide

def missing17363 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8161191853037715456
theorem maskCheck17363 :
    checkMaskFor missing17363 StrongPackedBucketN12A4Shard135.record17363 = true := by
  decide

def missing17364 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13961828173090914304
theorem maskCheck17364 :
    checkMaskFor missing17364 StrongPackedBucketN12A4Shard135.record17364 = true := by
  decide

def missing17365 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14033885767128842240
theorem maskCheck17365 :
    checkMaskFor missing17365 StrongPackedBucketN12A4Shard135.record17365 = true := by
  decide

def missing17366 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14286087346261590016
theorem maskCheck17366 :
    checkMaskFor missing17366 StrongPackedBucketN12A4Shard135.record17366 = true := by
  decide

def missing17367 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14466231331356409856
theorem maskCheck17367 :
    checkMaskFor missing17367 StrongPackedBucketN12A4Shard135.record17367 = true := by
  decide

def missing17368 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14574317722413301760
theorem maskCheck17368 :
    checkMaskFor missing17368 StrongPackedBucketN12A4Shard135.record17368 = true := by
  decide

def missing17369 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15042692083659833344
theorem maskCheck17369 :
    checkMaskFor missing17369 StrongPackedBucketN12A4Shard135.record17369 = true := by
  decide

def missing17370 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15150778474716725248
theorem maskCheck17370 :
    checkMaskFor missing17370 StrongPackedBucketN12A4Shard135.record17370 = true := by
  decide

def missing17371 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15583124038944292864
theorem maskCheck17371 :
    checkMaskFor missing17371 StrongPackedBucketN12A4Shard135.record17371 = true := by
  decide

def missing17372 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17312506295854563328
theorem maskCheck17372 :
    checkMaskFor missing17372 StrongPackedBucketN12A4Shard135.record17372 = true := by
  decide

def missing17373 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 559186050780495872
theorem maskCheck17373 :
    checkMaskFor missing17373 StrongPackedBucketN12A4Shard135.record17373 = true := by
  decide

def missing17374 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 847416426932207616
theorem maskCheck17374 :
    checkMaskFor missing17374 StrongPackedBucketN12A4Shard135.record17374 = true := by
  decide

def missing17375 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 991531615008063488
theorem maskCheck17375 :
    checkMaskFor missing17375 StrongPackedBucketN12A4Shard135.record17375 = true := by
  decide

def missing17376 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1063589209045991424
theorem maskCheck17376 :
    checkMaskFor missing17376 StrongPackedBucketN12A4Shard135.record17376 = true := by
  decide

def missing17377 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1099618006064955392
theorem maskCheck17377 :
    checkMaskFor missing17377 StrongPackedBucketN12A4Shard135.record17377 = true := by
  decide

def missing17378 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1423877179235631104
theorem maskCheck17378 :
    checkMaskFor missing17378 StrongPackedBucketN12A4Shard135.record17378 = true := by
  decide

def missing17379 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1567992367311486976
theorem maskCheck17379 :
    checkMaskFor missing17379 StrongPackedBucketN12A4Shard135.record17379 = true := by
  decide

def missing17380 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1640049961349414912
theorem maskCheck17380 :
    checkMaskFor missing17380 StrongPackedBucketN12A4Shard135.record17380 = true := by
  decide

def missing17381 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1676078758368378880
theorem maskCheck17381 :
    checkMaskFor missing17381 StrongPackedBucketN12A4Shard135.record17381 = true := by
  decide

def missing17382 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1856222743463198720
theorem maskCheck17382 :
    checkMaskFor missing17382 StrongPackedBucketN12A4Shard135.record17382 = true := by
  decide

def missing17383 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1928280337501126656
theorem maskCheck17383 :
    checkMaskFor missing17383 StrongPackedBucketN12A4Shard135.record17383 = true := by
  decide

def missing17384 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1964309134520090624
theorem maskCheck17384 :
    checkMaskFor missing17384 StrongPackedBucketN12A4Shard135.record17384 = true := by
  decide

def missing17385 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2072395525576982528
theorem maskCheck17385 :
    checkMaskFor missing17385 StrongPackedBucketN12A4Shard135.record17385 = true := by
  decide

def missing17386 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2108424322595946496
theorem maskCheck17386 :
    checkMaskFor missing17386 StrongPackedBucketN12A4Shard135.record17386 = true := by
  decide

def missing17387 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3585605000373469184
theorem maskCheck17387 :
    checkMaskFor missing17387 StrongPackedBucketN12A4Shard135.record17387 = true := by
  decide

def missing17388 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3657662594411397120
theorem maskCheck17388 :
    checkMaskFor missing17388 StrongPackedBucketN12A4Shard135.record17388 = true := by
  decide

def missing17389 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3693691391430361088
theorem maskCheck17389 :
    checkMaskFor missing17389 StrongPackedBucketN12A4Shard135.record17389 = true := by
  decide

def missing17390 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3801777782487252992
theorem maskCheck17390 :
    checkMaskFor missing17390 StrongPackedBucketN12A4Shard135.record17390 = true := by
  decide

def missing17391 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3837806579506216960
theorem maskCheck17391 :
    checkMaskFor missing17391 StrongPackedBucketN12A4Shard135.record17391 = true := by
  decide

def missing17392 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4882641693056172032
theorem maskCheck17392 :
    checkMaskFor missing17392 StrongPackedBucketN12A4Shard135.record17392 = true := by
  decide

def missing17393 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5026756881132027904
theorem maskCheck17393 :
    checkMaskFor missing17393 StrongPackedBucketN12A4Shard135.record17393 = true := by
  decide

def missing17394 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5098814475169955840
theorem maskCheck17394 :
    checkMaskFor missing17394 StrongPackedBucketN12A4Shard135.record17394 = true := by
  decide

def missing17395 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5134843272188919808
theorem maskCheck17395 :
    checkMaskFor missing17395 StrongPackedBucketN12A4Shard135.record17395 = true := by
  decide

def missing17396 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5314987257283739648
theorem maskCheck17396 :
    checkMaskFor missing17396 StrongPackedBucketN12A4Shard135.record17396 = true := by
  decide

def missing17397 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5387044851321667584
theorem maskCheck17397 :
    checkMaskFor missing17397 StrongPackedBucketN12A4Shard135.record17397 = true := by
  decide

def missing17398 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5423073648340631552
theorem maskCheck17398 :
    checkMaskFor missing17398 StrongPackedBucketN12A4Shard135.record17398 = true := by
  decide

def missing17399 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5531160039397523456
theorem maskCheck17399 :
    checkMaskFor missing17399 StrongPackedBucketN12A4Shard135.record17399 = true := by
  decide

def missing17400 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5567188836416487424
theorem maskCheck17400 :
    checkMaskFor missing17400 StrongPackedBucketN12A4Shard135.record17400 = true := by
  decide

def missing17401 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5639246430454415360
theorem maskCheck17401 :
    checkMaskFor missing17401 StrongPackedBucketN12A4Shard135.record17401 = true := by
  decide

def missing17402 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5891448009587163136
theorem maskCheck17402 :
    checkMaskFor missing17402 StrongPackedBucketN12A4Shard135.record17402 = true := by
  decide

def missing17403 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5963505603625091072
theorem maskCheck17403 :
    checkMaskFor missing17403 StrongPackedBucketN12A4Shard135.record17403 = true := by
  decide

def missing17404 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5999534400644055040
theorem maskCheck17404 :
    checkMaskFor missing17404 StrongPackedBucketN12A4Shard135.record17404 = true := by
  decide

def missing17405 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6107620791700946944
theorem maskCheck17405 :
    checkMaskFor missing17405 StrongPackedBucketN12A4Shard135.record17405 = true := by
  decide

def missing17406 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6143649588719910912
theorem maskCheck17406 :
    checkMaskFor missing17406 StrongPackedBucketN12A4Shard135.record17406 = true := by
  decide

def missing17407 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6215707182757838848
theorem maskCheck17407 :
    checkMaskFor missing17407 StrongPackedBucketN12A4Shard135.record17407 = true := by
  decide

def missing17280_17281 : List (BitVec (edgeCount 12)) :=
  [missing17280]
abbrev records17280_17281 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17280]
theorem aligned17280_17281 :
    AlignedValid 12 4 missing17280_17281 records17280_17281 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17280
    maskCheck17280 AlignedValid.nil

def missing17281_17282 : List (BitVec (edgeCount 12)) :=
  [missing17281]
abbrev records17281_17282 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17281]
theorem aligned17281_17282 :
    AlignedValid 12 4 missing17281_17282 records17281_17282 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17281
    maskCheck17281 AlignedValid.nil

def missing17280_17282 : List (BitVec (edgeCount 12)) :=
  missing17280_17281 ++ missing17281_17282
abbrev records17280_17282 : List Blob :=
  records17280_17281 ++ records17281_17282
theorem aligned17280_17282 :
    AlignedValid 12 4 missing17280_17282 records17280_17282 :=
  aligned17280_17281.append aligned17281_17282

def missing17282_17283 : List (BitVec (edgeCount 12)) :=
  [missing17282]
abbrev records17282_17283 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17282]
theorem aligned17282_17283 :
    AlignedValid 12 4 missing17282_17283 records17282_17283 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17282
    maskCheck17282 AlignedValid.nil

def missing17283_17284 : List (BitVec (edgeCount 12)) :=
  [missing17283]
abbrev records17283_17284 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17283]
theorem aligned17283_17284 :
    AlignedValid 12 4 missing17283_17284 records17283_17284 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17283
    maskCheck17283 AlignedValid.nil

def missing17282_17284 : List (BitVec (edgeCount 12)) :=
  missing17282_17283 ++ missing17283_17284
abbrev records17282_17284 : List Blob :=
  records17282_17283 ++ records17283_17284
theorem aligned17282_17284 :
    AlignedValid 12 4 missing17282_17284 records17282_17284 :=
  aligned17282_17283.append aligned17283_17284

def missing17280_17284 : List (BitVec (edgeCount 12)) :=
  missing17280_17282 ++ missing17282_17284
abbrev records17280_17284 : List Blob :=
  records17280_17282 ++ records17282_17284
theorem aligned17280_17284 :
    AlignedValid 12 4 missing17280_17284 records17280_17284 :=
  aligned17280_17282.append aligned17282_17284

def missing17284_17285 : List (BitVec (edgeCount 12)) :=
  [missing17284]
abbrev records17284_17285 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17284]
theorem aligned17284_17285 :
    AlignedValid 12 4 missing17284_17285 records17284_17285 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17284
    maskCheck17284 AlignedValid.nil

def missing17285_17286 : List (BitVec (edgeCount 12)) :=
  [missing17285]
abbrev records17285_17286 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17285]
theorem aligned17285_17286 :
    AlignedValid 12 4 missing17285_17286 records17285_17286 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17285
    maskCheck17285 AlignedValid.nil

def missing17284_17286 : List (BitVec (edgeCount 12)) :=
  missing17284_17285 ++ missing17285_17286
abbrev records17284_17286 : List Blob :=
  records17284_17285 ++ records17285_17286
theorem aligned17284_17286 :
    AlignedValid 12 4 missing17284_17286 records17284_17286 :=
  aligned17284_17285.append aligned17285_17286

def missing17286_17287 : List (BitVec (edgeCount 12)) :=
  [missing17286]
abbrev records17286_17287 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17286]
theorem aligned17286_17287 :
    AlignedValid 12 4 missing17286_17287 records17286_17287 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17286
    maskCheck17286 AlignedValid.nil

def missing17287_17288 : List (BitVec (edgeCount 12)) :=
  [missing17287]
abbrev records17287_17288 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17287]
theorem aligned17287_17288 :
    AlignedValid 12 4 missing17287_17288 records17287_17288 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17287
    maskCheck17287 AlignedValid.nil

def missing17286_17288 : List (BitVec (edgeCount 12)) :=
  missing17286_17287 ++ missing17287_17288
abbrev records17286_17288 : List Blob :=
  records17286_17287 ++ records17287_17288
theorem aligned17286_17288 :
    AlignedValid 12 4 missing17286_17288 records17286_17288 :=
  aligned17286_17287.append aligned17287_17288

def missing17284_17288 : List (BitVec (edgeCount 12)) :=
  missing17284_17286 ++ missing17286_17288
abbrev records17284_17288 : List Blob :=
  records17284_17286 ++ records17286_17288
theorem aligned17284_17288 :
    AlignedValid 12 4 missing17284_17288 records17284_17288 :=
  aligned17284_17286.append aligned17286_17288

def missing17280_17288 : List (BitVec (edgeCount 12)) :=
  missing17280_17284 ++ missing17284_17288
abbrev records17280_17288 : List Blob :=
  records17280_17284 ++ records17284_17288
theorem aligned17280_17288 :
    AlignedValid 12 4 missing17280_17288 records17280_17288 :=
  aligned17280_17284.append aligned17284_17288

def missing17288_17289 : List (BitVec (edgeCount 12)) :=
  [missing17288]
abbrev records17288_17289 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17288]
theorem aligned17288_17289 :
    AlignedValid 12 4 missing17288_17289 records17288_17289 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17288
    maskCheck17288 AlignedValid.nil

def missing17289_17290 : List (BitVec (edgeCount 12)) :=
  [missing17289]
abbrev records17289_17290 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17289]
theorem aligned17289_17290 :
    AlignedValid 12 4 missing17289_17290 records17289_17290 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17289
    maskCheck17289 AlignedValid.nil

def missing17288_17290 : List (BitVec (edgeCount 12)) :=
  missing17288_17289 ++ missing17289_17290
abbrev records17288_17290 : List Blob :=
  records17288_17289 ++ records17289_17290
theorem aligned17288_17290 :
    AlignedValid 12 4 missing17288_17290 records17288_17290 :=
  aligned17288_17289.append aligned17289_17290

def missing17290_17291 : List (BitVec (edgeCount 12)) :=
  [missing17290]
abbrev records17290_17291 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17290]
theorem aligned17290_17291 :
    AlignedValid 12 4 missing17290_17291 records17290_17291 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17290
    maskCheck17290 AlignedValid.nil

def missing17291_17292 : List (BitVec (edgeCount 12)) :=
  [missing17291]
abbrev records17291_17292 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17291]
theorem aligned17291_17292 :
    AlignedValid 12 4 missing17291_17292 records17291_17292 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17291
    maskCheck17291 AlignedValid.nil

def missing17290_17292 : List (BitVec (edgeCount 12)) :=
  missing17290_17291 ++ missing17291_17292
abbrev records17290_17292 : List Blob :=
  records17290_17291 ++ records17291_17292
theorem aligned17290_17292 :
    AlignedValid 12 4 missing17290_17292 records17290_17292 :=
  aligned17290_17291.append aligned17291_17292

def missing17288_17292 : List (BitVec (edgeCount 12)) :=
  missing17288_17290 ++ missing17290_17292
abbrev records17288_17292 : List Blob :=
  records17288_17290 ++ records17290_17292
theorem aligned17288_17292 :
    AlignedValid 12 4 missing17288_17292 records17288_17292 :=
  aligned17288_17290.append aligned17290_17292

def missing17292_17293 : List (BitVec (edgeCount 12)) :=
  [missing17292]
abbrev records17292_17293 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17292]
theorem aligned17292_17293 :
    AlignedValid 12 4 missing17292_17293 records17292_17293 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17292
    maskCheck17292 AlignedValid.nil

def missing17293_17294 : List (BitVec (edgeCount 12)) :=
  [missing17293]
abbrev records17293_17294 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17293]
theorem aligned17293_17294 :
    AlignedValid 12 4 missing17293_17294 records17293_17294 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17293
    maskCheck17293 AlignedValid.nil

def missing17292_17294 : List (BitVec (edgeCount 12)) :=
  missing17292_17293 ++ missing17293_17294
abbrev records17292_17294 : List Blob :=
  records17292_17293 ++ records17293_17294
theorem aligned17292_17294 :
    AlignedValid 12 4 missing17292_17294 records17292_17294 :=
  aligned17292_17293.append aligned17293_17294

def missing17294_17295 : List (BitVec (edgeCount 12)) :=
  [missing17294]
abbrev records17294_17295 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17294]
theorem aligned17294_17295 :
    AlignedValid 12 4 missing17294_17295 records17294_17295 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17294
    maskCheck17294 AlignedValid.nil

def missing17295_17296 : List (BitVec (edgeCount 12)) :=
  [missing17295]
abbrev records17295_17296 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17295]
theorem aligned17295_17296 :
    AlignedValid 12 4 missing17295_17296 records17295_17296 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17295
    maskCheck17295 AlignedValid.nil

def missing17294_17296 : List (BitVec (edgeCount 12)) :=
  missing17294_17295 ++ missing17295_17296
abbrev records17294_17296 : List Blob :=
  records17294_17295 ++ records17295_17296
theorem aligned17294_17296 :
    AlignedValid 12 4 missing17294_17296 records17294_17296 :=
  aligned17294_17295.append aligned17295_17296

def missing17292_17296 : List (BitVec (edgeCount 12)) :=
  missing17292_17294 ++ missing17294_17296
abbrev records17292_17296 : List Blob :=
  records17292_17294 ++ records17294_17296
theorem aligned17292_17296 :
    AlignedValid 12 4 missing17292_17296 records17292_17296 :=
  aligned17292_17294.append aligned17294_17296

def missing17288_17296 : List (BitVec (edgeCount 12)) :=
  missing17288_17292 ++ missing17292_17296
abbrev records17288_17296 : List Blob :=
  records17288_17292 ++ records17292_17296
theorem aligned17288_17296 :
    AlignedValid 12 4 missing17288_17296 records17288_17296 :=
  aligned17288_17292.append aligned17292_17296

def missing17280_17296 : List (BitVec (edgeCount 12)) :=
  missing17280_17288 ++ missing17288_17296
abbrev records17280_17296 : List Blob :=
  records17280_17288 ++ records17288_17296
theorem aligned17280_17296 :
    AlignedValid 12 4 missing17280_17296 records17280_17296 :=
  aligned17280_17288.append aligned17288_17296

def missing17296_17297 : List (BitVec (edgeCount 12)) :=
  [missing17296]
abbrev records17296_17297 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17296]
theorem aligned17296_17297 :
    AlignedValid 12 4 missing17296_17297 records17296_17297 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17296
    maskCheck17296 AlignedValid.nil

def missing17297_17298 : List (BitVec (edgeCount 12)) :=
  [missing17297]
abbrev records17297_17298 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17297]
theorem aligned17297_17298 :
    AlignedValid 12 4 missing17297_17298 records17297_17298 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17297
    maskCheck17297 AlignedValid.nil

def missing17296_17298 : List (BitVec (edgeCount 12)) :=
  missing17296_17297 ++ missing17297_17298
abbrev records17296_17298 : List Blob :=
  records17296_17297 ++ records17297_17298
theorem aligned17296_17298 :
    AlignedValid 12 4 missing17296_17298 records17296_17298 :=
  aligned17296_17297.append aligned17297_17298

def missing17298_17299 : List (BitVec (edgeCount 12)) :=
  [missing17298]
abbrev records17298_17299 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17298]
theorem aligned17298_17299 :
    AlignedValid 12 4 missing17298_17299 records17298_17299 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17298
    maskCheck17298 AlignedValid.nil

def missing17299_17300 : List (BitVec (edgeCount 12)) :=
  [missing17299]
abbrev records17299_17300 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17299]
theorem aligned17299_17300 :
    AlignedValid 12 4 missing17299_17300 records17299_17300 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17299
    maskCheck17299 AlignedValid.nil

def missing17298_17300 : List (BitVec (edgeCount 12)) :=
  missing17298_17299 ++ missing17299_17300
abbrev records17298_17300 : List Blob :=
  records17298_17299 ++ records17299_17300
theorem aligned17298_17300 :
    AlignedValid 12 4 missing17298_17300 records17298_17300 :=
  aligned17298_17299.append aligned17299_17300

def missing17296_17300 : List (BitVec (edgeCount 12)) :=
  missing17296_17298 ++ missing17298_17300
abbrev records17296_17300 : List Blob :=
  records17296_17298 ++ records17298_17300
theorem aligned17296_17300 :
    AlignedValid 12 4 missing17296_17300 records17296_17300 :=
  aligned17296_17298.append aligned17298_17300

def missing17300_17301 : List (BitVec (edgeCount 12)) :=
  [missing17300]
abbrev records17300_17301 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17300]
theorem aligned17300_17301 :
    AlignedValid 12 4 missing17300_17301 records17300_17301 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17300
    maskCheck17300 AlignedValid.nil

def missing17301_17302 : List (BitVec (edgeCount 12)) :=
  [missing17301]
abbrev records17301_17302 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17301]
theorem aligned17301_17302 :
    AlignedValid 12 4 missing17301_17302 records17301_17302 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17301
    maskCheck17301 AlignedValid.nil

def missing17300_17302 : List (BitVec (edgeCount 12)) :=
  missing17300_17301 ++ missing17301_17302
abbrev records17300_17302 : List Blob :=
  records17300_17301 ++ records17301_17302
theorem aligned17300_17302 :
    AlignedValid 12 4 missing17300_17302 records17300_17302 :=
  aligned17300_17301.append aligned17301_17302

def missing17302_17303 : List (BitVec (edgeCount 12)) :=
  [missing17302]
abbrev records17302_17303 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17302]
theorem aligned17302_17303 :
    AlignedValid 12 4 missing17302_17303 records17302_17303 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17302
    maskCheck17302 AlignedValid.nil

def missing17303_17304 : List (BitVec (edgeCount 12)) :=
  [missing17303]
abbrev records17303_17304 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17303]
theorem aligned17303_17304 :
    AlignedValid 12 4 missing17303_17304 records17303_17304 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17303
    maskCheck17303 AlignedValid.nil

def missing17302_17304 : List (BitVec (edgeCount 12)) :=
  missing17302_17303 ++ missing17303_17304
abbrev records17302_17304 : List Blob :=
  records17302_17303 ++ records17303_17304
theorem aligned17302_17304 :
    AlignedValid 12 4 missing17302_17304 records17302_17304 :=
  aligned17302_17303.append aligned17303_17304

def missing17300_17304 : List (BitVec (edgeCount 12)) :=
  missing17300_17302 ++ missing17302_17304
abbrev records17300_17304 : List Blob :=
  records17300_17302 ++ records17302_17304
theorem aligned17300_17304 :
    AlignedValid 12 4 missing17300_17304 records17300_17304 :=
  aligned17300_17302.append aligned17302_17304

def missing17296_17304 : List (BitVec (edgeCount 12)) :=
  missing17296_17300 ++ missing17300_17304
abbrev records17296_17304 : List Blob :=
  records17296_17300 ++ records17300_17304
theorem aligned17296_17304 :
    AlignedValid 12 4 missing17296_17304 records17296_17304 :=
  aligned17296_17300.append aligned17300_17304

def missing17304_17305 : List (BitVec (edgeCount 12)) :=
  [missing17304]
abbrev records17304_17305 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17304]
theorem aligned17304_17305 :
    AlignedValid 12 4 missing17304_17305 records17304_17305 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17304
    maskCheck17304 AlignedValid.nil

def missing17305_17306 : List (BitVec (edgeCount 12)) :=
  [missing17305]
abbrev records17305_17306 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17305]
theorem aligned17305_17306 :
    AlignedValid 12 4 missing17305_17306 records17305_17306 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17305
    maskCheck17305 AlignedValid.nil

def missing17304_17306 : List (BitVec (edgeCount 12)) :=
  missing17304_17305 ++ missing17305_17306
abbrev records17304_17306 : List Blob :=
  records17304_17305 ++ records17305_17306
theorem aligned17304_17306 :
    AlignedValid 12 4 missing17304_17306 records17304_17306 :=
  aligned17304_17305.append aligned17305_17306

def missing17306_17307 : List (BitVec (edgeCount 12)) :=
  [missing17306]
abbrev records17306_17307 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17306]
theorem aligned17306_17307 :
    AlignedValid 12 4 missing17306_17307 records17306_17307 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17306
    maskCheck17306 AlignedValid.nil

def missing17307_17308 : List (BitVec (edgeCount 12)) :=
  [missing17307]
abbrev records17307_17308 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17307]
theorem aligned17307_17308 :
    AlignedValid 12 4 missing17307_17308 records17307_17308 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17307
    maskCheck17307 AlignedValid.nil

def missing17306_17308 : List (BitVec (edgeCount 12)) :=
  missing17306_17307 ++ missing17307_17308
abbrev records17306_17308 : List Blob :=
  records17306_17307 ++ records17307_17308
theorem aligned17306_17308 :
    AlignedValid 12 4 missing17306_17308 records17306_17308 :=
  aligned17306_17307.append aligned17307_17308

def missing17304_17308 : List (BitVec (edgeCount 12)) :=
  missing17304_17306 ++ missing17306_17308
abbrev records17304_17308 : List Blob :=
  records17304_17306 ++ records17306_17308
theorem aligned17304_17308 :
    AlignedValid 12 4 missing17304_17308 records17304_17308 :=
  aligned17304_17306.append aligned17306_17308

def missing17308_17309 : List (BitVec (edgeCount 12)) :=
  [missing17308]
abbrev records17308_17309 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17308]
theorem aligned17308_17309 :
    AlignedValid 12 4 missing17308_17309 records17308_17309 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17308
    maskCheck17308 AlignedValid.nil

def missing17309_17310 : List (BitVec (edgeCount 12)) :=
  [missing17309]
abbrev records17309_17310 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17309]
theorem aligned17309_17310 :
    AlignedValid 12 4 missing17309_17310 records17309_17310 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17309
    maskCheck17309 AlignedValid.nil

def missing17308_17310 : List (BitVec (edgeCount 12)) :=
  missing17308_17309 ++ missing17309_17310
abbrev records17308_17310 : List Blob :=
  records17308_17309 ++ records17309_17310
theorem aligned17308_17310 :
    AlignedValid 12 4 missing17308_17310 records17308_17310 :=
  aligned17308_17309.append aligned17309_17310

def missing17310_17311 : List (BitVec (edgeCount 12)) :=
  [missing17310]
abbrev records17310_17311 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17310]
theorem aligned17310_17311 :
    AlignedValid 12 4 missing17310_17311 records17310_17311 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17310
    maskCheck17310 AlignedValid.nil

def missing17311_17312 : List (BitVec (edgeCount 12)) :=
  [missing17311]
abbrev records17311_17312 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17311]
theorem aligned17311_17312 :
    AlignedValid 12 4 missing17311_17312 records17311_17312 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17311
    maskCheck17311 AlignedValid.nil

def missing17310_17312 : List (BitVec (edgeCount 12)) :=
  missing17310_17311 ++ missing17311_17312
abbrev records17310_17312 : List Blob :=
  records17310_17311 ++ records17311_17312
theorem aligned17310_17312 :
    AlignedValid 12 4 missing17310_17312 records17310_17312 :=
  aligned17310_17311.append aligned17311_17312

def missing17308_17312 : List (BitVec (edgeCount 12)) :=
  missing17308_17310 ++ missing17310_17312
abbrev records17308_17312 : List Blob :=
  records17308_17310 ++ records17310_17312
theorem aligned17308_17312 :
    AlignedValid 12 4 missing17308_17312 records17308_17312 :=
  aligned17308_17310.append aligned17310_17312

def missing17304_17312 : List (BitVec (edgeCount 12)) :=
  missing17304_17308 ++ missing17308_17312
abbrev records17304_17312 : List Blob :=
  records17304_17308 ++ records17308_17312
theorem aligned17304_17312 :
    AlignedValid 12 4 missing17304_17312 records17304_17312 :=
  aligned17304_17308.append aligned17308_17312

def missing17296_17312 : List (BitVec (edgeCount 12)) :=
  missing17296_17304 ++ missing17304_17312
abbrev records17296_17312 : List Blob :=
  records17296_17304 ++ records17304_17312
theorem aligned17296_17312 :
    AlignedValid 12 4 missing17296_17312 records17296_17312 :=
  aligned17296_17304.append aligned17304_17312

def missing17280_17312 : List (BitVec (edgeCount 12)) :=
  missing17280_17296 ++ missing17296_17312
abbrev records17280_17312 : List Blob :=
  records17280_17296 ++ records17296_17312
theorem aligned17280_17312 :
    AlignedValid 12 4 missing17280_17312 records17280_17312 :=
  aligned17280_17296.append aligned17296_17312

def missing17312_17313 : List (BitVec (edgeCount 12)) :=
  [missing17312]
abbrev records17312_17313 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17312]
theorem aligned17312_17313 :
    AlignedValid 12 4 missing17312_17313 records17312_17313 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17312
    maskCheck17312 AlignedValid.nil

def missing17313_17314 : List (BitVec (edgeCount 12)) :=
  [missing17313]
abbrev records17313_17314 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17313]
theorem aligned17313_17314 :
    AlignedValid 12 4 missing17313_17314 records17313_17314 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17313
    maskCheck17313 AlignedValid.nil

def missing17312_17314 : List (BitVec (edgeCount 12)) :=
  missing17312_17313 ++ missing17313_17314
abbrev records17312_17314 : List Blob :=
  records17312_17313 ++ records17313_17314
theorem aligned17312_17314 :
    AlignedValid 12 4 missing17312_17314 records17312_17314 :=
  aligned17312_17313.append aligned17313_17314

def missing17314_17315 : List (BitVec (edgeCount 12)) :=
  [missing17314]
abbrev records17314_17315 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17314]
theorem aligned17314_17315 :
    AlignedValid 12 4 missing17314_17315 records17314_17315 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17314
    maskCheck17314 AlignedValid.nil

def missing17315_17316 : List (BitVec (edgeCount 12)) :=
  [missing17315]
abbrev records17315_17316 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17315]
theorem aligned17315_17316 :
    AlignedValid 12 4 missing17315_17316 records17315_17316 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17315
    maskCheck17315 AlignedValid.nil

def missing17314_17316 : List (BitVec (edgeCount 12)) :=
  missing17314_17315 ++ missing17315_17316
abbrev records17314_17316 : List Blob :=
  records17314_17315 ++ records17315_17316
theorem aligned17314_17316 :
    AlignedValid 12 4 missing17314_17316 records17314_17316 :=
  aligned17314_17315.append aligned17315_17316

def missing17312_17316 : List (BitVec (edgeCount 12)) :=
  missing17312_17314 ++ missing17314_17316
abbrev records17312_17316 : List Blob :=
  records17312_17314 ++ records17314_17316
theorem aligned17312_17316 :
    AlignedValid 12 4 missing17312_17316 records17312_17316 :=
  aligned17312_17314.append aligned17314_17316

def missing17316_17317 : List (BitVec (edgeCount 12)) :=
  [missing17316]
abbrev records17316_17317 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17316]
theorem aligned17316_17317 :
    AlignedValid 12 4 missing17316_17317 records17316_17317 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17316
    maskCheck17316 AlignedValid.nil

def missing17317_17318 : List (BitVec (edgeCount 12)) :=
  [missing17317]
abbrev records17317_17318 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17317]
theorem aligned17317_17318 :
    AlignedValid 12 4 missing17317_17318 records17317_17318 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17317
    maskCheck17317 AlignedValid.nil

def missing17316_17318 : List (BitVec (edgeCount 12)) :=
  missing17316_17317 ++ missing17317_17318
abbrev records17316_17318 : List Blob :=
  records17316_17317 ++ records17317_17318
theorem aligned17316_17318 :
    AlignedValid 12 4 missing17316_17318 records17316_17318 :=
  aligned17316_17317.append aligned17317_17318

def missing17318_17319 : List (BitVec (edgeCount 12)) :=
  [missing17318]
abbrev records17318_17319 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17318]
theorem aligned17318_17319 :
    AlignedValid 12 4 missing17318_17319 records17318_17319 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17318
    maskCheck17318 AlignedValid.nil

def missing17319_17320 : List (BitVec (edgeCount 12)) :=
  [missing17319]
abbrev records17319_17320 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17319]
theorem aligned17319_17320 :
    AlignedValid 12 4 missing17319_17320 records17319_17320 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17319
    maskCheck17319 AlignedValid.nil

def missing17318_17320 : List (BitVec (edgeCount 12)) :=
  missing17318_17319 ++ missing17319_17320
abbrev records17318_17320 : List Blob :=
  records17318_17319 ++ records17319_17320
theorem aligned17318_17320 :
    AlignedValid 12 4 missing17318_17320 records17318_17320 :=
  aligned17318_17319.append aligned17319_17320

def missing17316_17320 : List (BitVec (edgeCount 12)) :=
  missing17316_17318 ++ missing17318_17320
abbrev records17316_17320 : List Blob :=
  records17316_17318 ++ records17318_17320
theorem aligned17316_17320 :
    AlignedValid 12 4 missing17316_17320 records17316_17320 :=
  aligned17316_17318.append aligned17318_17320

def missing17312_17320 : List (BitVec (edgeCount 12)) :=
  missing17312_17316 ++ missing17316_17320
abbrev records17312_17320 : List Blob :=
  records17312_17316 ++ records17316_17320
theorem aligned17312_17320 :
    AlignedValid 12 4 missing17312_17320 records17312_17320 :=
  aligned17312_17316.append aligned17316_17320

def missing17320_17321 : List (BitVec (edgeCount 12)) :=
  [missing17320]
abbrev records17320_17321 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17320]
theorem aligned17320_17321 :
    AlignedValid 12 4 missing17320_17321 records17320_17321 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17320
    maskCheck17320 AlignedValid.nil

def missing17321_17322 : List (BitVec (edgeCount 12)) :=
  [missing17321]
abbrev records17321_17322 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17321]
theorem aligned17321_17322 :
    AlignedValid 12 4 missing17321_17322 records17321_17322 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17321
    maskCheck17321 AlignedValid.nil

def missing17320_17322 : List (BitVec (edgeCount 12)) :=
  missing17320_17321 ++ missing17321_17322
abbrev records17320_17322 : List Blob :=
  records17320_17321 ++ records17321_17322
theorem aligned17320_17322 :
    AlignedValid 12 4 missing17320_17322 records17320_17322 :=
  aligned17320_17321.append aligned17321_17322

def missing17322_17323 : List (BitVec (edgeCount 12)) :=
  [missing17322]
abbrev records17322_17323 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17322]
theorem aligned17322_17323 :
    AlignedValid 12 4 missing17322_17323 records17322_17323 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17322
    maskCheck17322 AlignedValid.nil

def missing17323_17324 : List (BitVec (edgeCount 12)) :=
  [missing17323]
abbrev records17323_17324 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17323]
theorem aligned17323_17324 :
    AlignedValid 12 4 missing17323_17324 records17323_17324 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17323
    maskCheck17323 AlignedValid.nil

def missing17322_17324 : List (BitVec (edgeCount 12)) :=
  missing17322_17323 ++ missing17323_17324
abbrev records17322_17324 : List Blob :=
  records17322_17323 ++ records17323_17324
theorem aligned17322_17324 :
    AlignedValid 12 4 missing17322_17324 records17322_17324 :=
  aligned17322_17323.append aligned17323_17324

def missing17320_17324 : List (BitVec (edgeCount 12)) :=
  missing17320_17322 ++ missing17322_17324
abbrev records17320_17324 : List Blob :=
  records17320_17322 ++ records17322_17324
theorem aligned17320_17324 :
    AlignedValid 12 4 missing17320_17324 records17320_17324 :=
  aligned17320_17322.append aligned17322_17324

def missing17324_17325 : List (BitVec (edgeCount 12)) :=
  [missing17324]
abbrev records17324_17325 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17324]
theorem aligned17324_17325 :
    AlignedValid 12 4 missing17324_17325 records17324_17325 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17324
    maskCheck17324 AlignedValid.nil

def missing17325_17326 : List (BitVec (edgeCount 12)) :=
  [missing17325]
abbrev records17325_17326 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17325]
theorem aligned17325_17326 :
    AlignedValid 12 4 missing17325_17326 records17325_17326 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17325
    maskCheck17325 AlignedValid.nil

def missing17324_17326 : List (BitVec (edgeCount 12)) :=
  missing17324_17325 ++ missing17325_17326
abbrev records17324_17326 : List Blob :=
  records17324_17325 ++ records17325_17326
theorem aligned17324_17326 :
    AlignedValid 12 4 missing17324_17326 records17324_17326 :=
  aligned17324_17325.append aligned17325_17326

def missing17326_17327 : List (BitVec (edgeCount 12)) :=
  [missing17326]
abbrev records17326_17327 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17326]
theorem aligned17326_17327 :
    AlignedValid 12 4 missing17326_17327 records17326_17327 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17326
    maskCheck17326 AlignedValid.nil

def missing17327_17328 : List (BitVec (edgeCount 12)) :=
  [missing17327]
abbrev records17327_17328 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17327]
theorem aligned17327_17328 :
    AlignedValid 12 4 missing17327_17328 records17327_17328 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17327
    maskCheck17327 AlignedValid.nil

def missing17326_17328 : List (BitVec (edgeCount 12)) :=
  missing17326_17327 ++ missing17327_17328
abbrev records17326_17328 : List Blob :=
  records17326_17327 ++ records17327_17328
theorem aligned17326_17328 :
    AlignedValid 12 4 missing17326_17328 records17326_17328 :=
  aligned17326_17327.append aligned17327_17328

def missing17324_17328 : List (BitVec (edgeCount 12)) :=
  missing17324_17326 ++ missing17326_17328
abbrev records17324_17328 : List Blob :=
  records17324_17326 ++ records17326_17328
theorem aligned17324_17328 :
    AlignedValid 12 4 missing17324_17328 records17324_17328 :=
  aligned17324_17326.append aligned17326_17328

def missing17320_17328 : List (BitVec (edgeCount 12)) :=
  missing17320_17324 ++ missing17324_17328
abbrev records17320_17328 : List Blob :=
  records17320_17324 ++ records17324_17328
theorem aligned17320_17328 :
    AlignedValid 12 4 missing17320_17328 records17320_17328 :=
  aligned17320_17324.append aligned17324_17328

def missing17312_17328 : List (BitVec (edgeCount 12)) :=
  missing17312_17320 ++ missing17320_17328
abbrev records17312_17328 : List Blob :=
  records17312_17320 ++ records17320_17328
theorem aligned17312_17328 :
    AlignedValid 12 4 missing17312_17328 records17312_17328 :=
  aligned17312_17320.append aligned17320_17328

def missing17328_17329 : List (BitVec (edgeCount 12)) :=
  [missing17328]
abbrev records17328_17329 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17328]
theorem aligned17328_17329 :
    AlignedValid 12 4 missing17328_17329 records17328_17329 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17328
    maskCheck17328 AlignedValid.nil

def missing17329_17330 : List (BitVec (edgeCount 12)) :=
  [missing17329]
abbrev records17329_17330 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17329]
theorem aligned17329_17330 :
    AlignedValid 12 4 missing17329_17330 records17329_17330 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17329
    maskCheck17329 AlignedValid.nil

def missing17328_17330 : List (BitVec (edgeCount 12)) :=
  missing17328_17329 ++ missing17329_17330
abbrev records17328_17330 : List Blob :=
  records17328_17329 ++ records17329_17330
theorem aligned17328_17330 :
    AlignedValid 12 4 missing17328_17330 records17328_17330 :=
  aligned17328_17329.append aligned17329_17330

def missing17330_17331 : List (BitVec (edgeCount 12)) :=
  [missing17330]
abbrev records17330_17331 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17330]
theorem aligned17330_17331 :
    AlignedValid 12 4 missing17330_17331 records17330_17331 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17330
    maskCheck17330 AlignedValid.nil

def missing17331_17332 : List (BitVec (edgeCount 12)) :=
  [missing17331]
abbrev records17331_17332 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17331]
theorem aligned17331_17332 :
    AlignedValid 12 4 missing17331_17332 records17331_17332 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17331
    maskCheck17331 AlignedValid.nil

def missing17330_17332 : List (BitVec (edgeCount 12)) :=
  missing17330_17331 ++ missing17331_17332
abbrev records17330_17332 : List Blob :=
  records17330_17331 ++ records17331_17332
theorem aligned17330_17332 :
    AlignedValid 12 4 missing17330_17332 records17330_17332 :=
  aligned17330_17331.append aligned17331_17332

def missing17328_17332 : List (BitVec (edgeCount 12)) :=
  missing17328_17330 ++ missing17330_17332
abbrev records17328_17332 : List Blob :=
  records17328_17330 ++ records17330_17332
theorem aligned17328_17332 :
    AlignedValid 12 4 missing17328_17332 records17328_17332 :=
  aligned17328_17330.append aligned17330_17332

def missing17332_17333 : List (BitVec (edgeCount 12)) :=
  [missing17332]
abbrev records17332_17333 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17332]
theorem aligned17332_17333 :
    AlignedValid 12 4 missing17332_17333 records17332_17333 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17332
    maskCheck17332 AlignedValid.nil

def missing17333_17334 : List (BitVec (edgeCount 12)) :=
  [missing17333]
abbrev records17333_17334 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17333]
theorem aligned17333_17334 :
    AlignedValid 12 4 missing17333_17334 records17333_17334 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17333
    maskCheck17333 AlignedValid.nil

def missing17332_17334 : List (BitVec (edgeCount 12)) :=
  missing17332_17333 ++ missing17333_17334
abbrev records17332_17334 : List Blob :=
  records17332_17333 ++ records17333_17334
theorem aligned17332_17334 :
    AlignedValid 12 4 missing17332_17334 records17332_17334 :=
  aligned17332_17333.append aligned17333_17334

def missing17334_17335 : List (BitVec (edgeCount 12)) :=
  [missing17334]
abbrev records17334_17335 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17334]
theorem aligned17334_17335 :
    AlignedValid 12 4 missing17334_17335 records17334_17335 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17334
    maskCheck17334 AlignedValid.nil

def missing17335_17336 : List (BitVec (edgeCount 12)) :=
  [missing17335]
abbrev records17335_17336 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17335]
theorem aligned17335_17336 :
    AlignedValid 12 4 missing17335_17336 records17335_17336 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17335
    maskCheck17335 AlignedValid.nil

def missing17334_17336 : List (BitVec (edgeCount 12)) :=
  missing17334_17335 ++ missing17335_17336
abbrev records17334_17336 : List Blob :=
  records17334_17335 ++ records17335_17336
theorem aligned17334_17336 :
    AlignedValid 12 4 missing17334_17336 records17334_17336 :=
  aligned17334_17335.append aligned17335_17336

def missing17332_17336 : List (BitVec (edgeCount 12)) :=
  missing17332_17334 ++ missing17334_17336
abbrev records17332_17336 : List Blob :=
  records17332_17334 ++ records17334_17336
theorem aligned17332_17336 :
    AlignedValid 12 4 missing17332_17336 records17332_17336 :=
  aligned17332_17334.append aligned17334_17336

def missing17328_17336 : List (BitVec (edgeCount 12)) :=
  missing17328_17332 ++ missing17332_17336
abbrev records17328_17336 : List Blob :=
  records17328_17332 ++ records17332_17336
theorem aligned17328_17336 :
    AlignedValid 12 4 missing17328_17336 records17328_17336 :=
  aligned17328_17332.append aligned17332_17336

def missing17336_17337 : List (BitVec (edgeCount 12)) :=
  [missing17336]
abbrev records17336_17337 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17336]
theorem aligned17336_17337 :
    AlignedValid 12 4 missing17336_17337 records17336_17337 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17336
    maskCheck17336 AlignedValid.nil

def missing17337_17338 : List (BitVec (edgeCount 12)) :=
  [missing17337]
abbrev records17337_17338 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17337]
theorem aligned17337_17338 :
    AlignedValid 12 4 missing17337_17338 records17337_17338 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17337
    maskCheck17337 AlignedValid.nil

def missing17336_17338 : List (BitVec (edgeCount 12)) :=
  missing17336_17337 ++ missing17337_17338
abbrev records17336_17338 : List Blob :=
  records17336_17337 ++ records17337_17338
theorem aligned17336_17338 :
    AlignedValid 12 4 missing17336_17338 records17336_17338 :=
  aligned17336_17337.append aligned17337_17338

def missing17338_17339 : List (BitVec (edgeCount 12)) :=
  [missing17338]
abbrev records17338_17339 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17338]
theorem aligned17338_17339 :
    AlignedValid 12 4 missing17338_17339 records17338_17339 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17338
    maskCheck17338 AlignedValid.nil

def missing17339_17340 : List (BitVec (edgeCount 12)) :=
  [missing17339]
abbrev records17339_17340 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17339]
theorem aligned17339_17340 :
    AlignedValid 12 4 missing17339_17340 records17339_17340 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17339
    maskCheck17339 AlignedValid.nil

def missing17338_17340 : List (BitVec (edgeCount 12)) :=
  missing17338_17339 ++ missing17339_17340
abbrev records17338_17340 : List Blob :=
  records17338_17339 ++ records17339_17340
theorem aligned17338_17340 :
    AlignedValid 12 4 missing17338_17340 records17338_17340 :=
  aligned17338_17339.append aligned17339_17340

def missing17336_17340 : List (BitVec (edgeCount 12)) :=
  missing17336_17338 ++ missing17338_17340
abbrev records17336_17340 : List Blob :=
  records17336_17338 ++ records17338_17340
theorem aligned17336_17340 :
    AlignedValid 12 4 missing17336_17340 records17336_17340 :=
  aligned17336_17338.append aligned17338_17340

def missing17340_17341 : List (BitVec (edgeCount 12)) :=
  [missing17340]
abbrev records17340_17341 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17340]
theorem aligned17340_17341 :
    AlignedValid 12 4 missing17340_17341 records17340_17341 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17340
    maskCheck17340 AlignedValid.nil

def missing17341_17342 : List (BitVec (edgeCount 12)) :=
  [missing17341]
abbrev records17341_17342 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17341]
theorem aligned17341_17342 :
    AlignedValid 12 4 missing17341_17342 records17341_17342 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17341
    maskCheck17341 AlignedValid.nil

def missing17340_17342 : List (BitVec (edgeCount 12)) :=
  missing17340_17341 ++ missing17341_17342
abbrev records17340_17342 : List Blob :=
  records17340_17341 ++ records17341_17342
theorem aligned17340_17342 :
    AlignedValid 12 4 missing17340_17342 records17340_17342 :=
  aligned17340_17341.append aligned17341_17342

def missing17342_17343 : List (BitVec (edgeCount 12)) :=
  [missing17342]
abbrev records17342_17343 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17342]
theorem aligned17342_17343 :
    AlignedValid 12 4 missing17342_17343 records17342_17343 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17342
    maskCheck17342 AlignedValid.nil

def missing17343_17344 : List (BitVec (edgeCount 12)) :=
  [missing17343]
abbrev records17343_17344 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17343]
theorem aligned17343_17344 :
    AlignedValid 12 4 missing17343_17344 records17343_17344 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17343
    maskCheck17343 AlignedValid.nil

def missing17342_17344 : List (BitVec (edgeCount 12)) :=
  missing17342_17343 ++ missing17343_17344
abbrev records17342_17344 : List Blob :=
  records17342_17343 ++ records17343_17344
theorem aligned17342_17344 :
    AlignedValid 12 4 missing17342_17344 records17342_17344 :=
  aligned17342_17343.append aligned17343_17344

def missing17340_17344 : List (BitVec (edgeCount 12)) :=
  missing17340_17342 ++ missing17342_17344
abbrev records17340_17344 : List Blob :=
  records17340_17342 ++ records17342_17344
theorem aligned17340_17344 :
    AlignedValid 12 4 missing17340_17344 records17340_17344 :=
  aligned17340_17342.append aligned17342_17344

def missing17336_17344 : List (BitVec (edgeCount 12)) :=
  missing17336_17340 ++ missing17340_17344
abbrev records17336_17344 : List Blob :=
  records17336_17340 ++ records17340_17344
theorem aligned17336_17344 :
    AlignedValid 12 4 missing17336_17344 records17336_17344 :=
  aligned17336_17340.append aligned17340_17344

def missing17328_17344 : List (BitVec (edgeCount 12)) :=
  missing17328_17336 ++ missing17336_17344
abbrev records17328_17344 : List Blob :=
  records17328_17336 ++ records17336_17344
theorem aligned17328_17344 :
    AlignedValid 12 4 missing17328_17344 records17328_17344 :=
  aligned17328_17336.append aligned17336_17344

def missing17312_17344 : List (BitVec (edgeCount 12)) :=
  missing17312_17328 ++ missing17328_17344
abbrev records17312_17344 : List Blob :=
  records17312_17328 ++ records17328_17344
theorem aligned17312_17344 :
    AlignedValid 12 4 missing17312_17344 records17312_17344 :=
  aligned17312_17328.append aligned17328_17344

def missing17280_17344 : List (BitVec (edgeCount 12)) :=
  missing17280_17312 ++ missing17312_17344
abbrev records17280_17344 : List Blob :=
  records17280_17312 ++ records17312_17344
theorem aligned17280_17344 :
    AlignedValid 12 4 missing17280_17344 records17280_17344 :=
  aligned17280_17312.append aligned17312_17344

def missing17344_17345 : List (BitVec (edgeCount 12)) :=
  [missing17344]
abbrev records17344_17345 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17344]
theorem aligned17344_17345 :
    AlignedValid 12 4 missing17344_17345 records17344_17345 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17344
    maskCheck17344 AlignedValid.nil

def missing17345_17346 : List (BitVec (edgeCount 12)) :=
  [missing17345]
abbrev records17345_17346 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17345]
theorem aligned17345_17346 :
    AlignedValid 12 4 missing17345_17346 records17345_17346 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17345
    maskCheck17345 AlignedValid.nil

def missing17344_17346 : List (BitVec (edgeCount 12)) :=
  missing17344_17345 ++ missing17345_17346
abbrev records17344_17346 : List Blob :=
  records17344_17345 ++ records17345_17346
theorem aligned17344_17346 :
    AlignedValid 12 4 missing17344_17346 records17344_17346 :=
  aligned17344_17345.append aligned17345_17346

def missing17346_17347 : List (BitVec (edgeCount 12)) :=
  [missing17346]
abbrev records17346_17347 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17346]
theorem aligned17346_17347 :
    AlignedValid 12 4 missing17346_17347 records17346_17347 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17346
    maskCheck17346 AlignedValid.nil

def missing17347_17348 : List (BitVec (edgeCount 12)) :=
  [missing17347]
abbrev records17347_17348 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17347]
theorem aligned17347_17348 :
    AlignedValid 12 4 missing17347_17348 records17347_17348 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17347
    maskCheck17347 AlignedValid.nil

def missing17346_17348 : List (BitVec (edgeCount 12)) :=
  missing17346_17347 ++ missing17347_17348
abbrev records17346_17348 : List Blob :=
  records17346_17347 ++ records17347_17348
theorem aligned17346_17348 :
    AlignedValid 12 4 missing17346_17348 records17346_17348 :=
  aligned17346_17347.append aligned17347_17348

def missing17344_17348 : List (BitVec (edgeCount 12)) :=
  missing17344_17346 ++ missing17346_17348
abbrev records17344_17348 : List Blob :=
  records17344_17346 ++ records17346_17348
theorem aligned17344_17348 :
    AlignedValid 12 4 missing17344_17348 records17344_17348 :=
  aligned17344_17346.append aligned17346_17348

def missing17348_17349 : List (BitVec (edgeCount 12)) :=
  [missing17348]
abbrev records17348_17349 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17348]
theorem aligned17348_17349 :
    AlignedValid 12 4 missing17348_17349 records17348_17349 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17348
    maskCheck17348 AlignedValid.nil

def missing17349_17350 : List (BitVec (edgeCount 12)) :=
  [missing17349]
abbrev records17349_17350 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17349]
theorem aligned17349_17350 :
    AlignedValid 12 4 missing17349_17350 records17349_17350 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17349
    maskCheck17349 AlignedValid.nil

def missing17348_17350 : List (BitVec (edgeCount 12)) :=
  missing17348_17349 ++ missing17349_17350
abbrev records17348_17350 : List Blob :=
  records17348_17349 ++ records17349_17350
theorem aligned17348_17350 :
    AlignedValid 12 4 missing17348_17350 records17348_17350 :=
  aligned17348_17349.append aligned17349_17350

def missing17350_17351 : List (BitVec (edgeCount 12)) :=
  [missing17350]
abbrev records17350_17351 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17350]
theorem aligned17350_17351 :
    AlignedValid 12 4 missing17350_17351 records17350_17351 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17350
    maskCheck17350 AlignedValid.nil

def missing17351_17352 : List (BitVec (edgeCount 12)) :=
  [missing17351]
abbrev records17351_17352 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17351]
theorem aligned17351_17352 :
    AlignedValid 12 4 missing17351_17352 records17351_17352 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17351
    maskCheck17351 AlignedValid.nil

def missing17350_17352 : List (BitVec (edgeCount 12)) :=
  missing17350_17351 ++ missing17351_17352
abbrev records17350_17352 : List Blob :=
  records17350_17351 ++ records17351_17352
theorem aligned17350_17352 :
    AlignedValid 12 4 missing17350_17352 records17350_17352 :=
  aligned17350_17351.append aligned17351_17352

def missing17348_17352 : List (BitVec (edgeCount 12)) :=
  missing17348_17350 ++ missing17350_17352
abbrev records17348_17352 : List Blob :=
  records17348_17350 ++ records17350_17352
theorem aligned17348_17352 :
    AlignedValid 12 4 missing17348_17352 records17348_17352 :=
  aligned17348_17350.append aligned17350_17352

def missing17344_17352 : List (BitVec (edgeCount 12)) :=
  missing17344_17348 ++ missing17348_17352
abbrev records17344_17352 : List Blob :=
  records17344_17348 ++ records17348_17352
theorem aligned17344_17352 :
    AlignedValid 12 4 missing17344_17352 records17344_17352 :=
  aligned17344_17348.append aligned17348_17352

def missing17352_17353 : List (BitVec (edgeCount 12)) :=
  [missing17352]
abbrev records17352_17353 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17352]
theorem aligned17352_17353 :
    AlignedValid 12 4 missing17352_17353 records17352_17353 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17352
    maskCheck17352 AlignedValid.nil

def missing17353_17354 : List (BitVec (edgeCount 12)) :=
  [missing17353]
abbrev records17353_17354 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17353]
theorem aligned17353_17354 :
    AlignedValid 12 4 missing17353_17354 records17353_17354 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17353
    maskCheck17353 AlignedValid.nil

def missing17352_17354 : List (BitVec (edgeCount 12)) :=
  missing17352_17353 ++ missing17353_17354
abbrev records17352_17354 : List Blob :=
  records17352_17353 ++ records17353_17354
theorem aligned17352_17354 :
    AlignedValid 12 4 missing17352_17354 records17352_17354 :=
  aligned17352_17353.append aligned17353_17354

def missing17354_17355 : List (BitVec (edgeCount 12)) :=
  [missing17354]
abbrev records17354_17355 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17354]
theorem aligned17354_17355 :
    AlignedValid 12 4 missing17354_17355 records17354_17355 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17354
    maskCheck17354 AlignedValid.nil

def missing17355_17356 : List (BitVec (edgeCount 12)) :=
  [missing17355]
abbrev records17355_17356 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17355]
theorem aligned17355_17356 :
    AlignedValid 12 4 missing17355_17356 records17355_17356 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17355
    maskCheck17355 AlignedValid.nil

def missing17354_17356 : List (BitVec (edgeCount 12)) :=
  missing17354_17355 ++ missing17355_17356
abbrev records17354_17356 : List Blob :=
  records17354_17355 ++ records17355_17356
theorem aligned17354_17356 :
    AlignedValid 12 4 missing17354_17356 records17354_17356 :=
  aligned17354_17355.append aligned17355_17356

def missing17352_17356 : List (BitVec (edgeCount 12)) :=
  missing17352_17354 ++ missing17354_17356
abbrev records17352_17356 : List Blob :=
  records17352_17354 ++ records17354_17356
theorem aligned17352_17356 :
    AlignedValid 12 4 missing17352_17356 records17352_17356 :=
  aligned17352_17354.append aligned17354_17356

def missing17356_17357 : List (BitVec (edgeCount 12)) :=
  [missing17356]
abbrev records17356_17357 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17356]
theorem aligned17356_17357 :
    AlignedValid 12 4 missing17356_17357 records17356_17357 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17356
    maskCheck17356 AlignedValid.nil

def missing17357_17358 : List (BitVec (edgeCount 12)) :=
  [missing17357]
abbrev records17357_17358 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17357]
theorem aligned17357_17358 :
    AlignedValid 12 4 missing17357_17358 records17357_17358 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17357
    maskCheck17357 AlignedValid.nil

def missing17356_17358 : List (BitVec (edgeCount 12)) :=
  missing17356_17357 ++ missing17357_17358
abbrev records17356_17358 : List Blob :=
  records17356_17357 ++ records17357_17358
theorem aligned17356_17358 :
    AlignedValid 12 4 missing17356_17358 records17356_17358 :=
  aligned17356_17357.append aligned17357_17358

def missing17358_17359 : List (BitVec (edgeCount 12)) :=
  [missing17358]
abbrev records17358_17359 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17358]
theorem aligned17358_17359 :
    AlignedValid 12 4 missing17358_17359 records17358_17359 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17358
    maskCheck17358 AlignedValid.nil

def missing17359_17360 : List (BitVec (edgeCount 12)) :=
  [missing17359]
abbrev records17359_17360 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17359]
theorem aligned17359_17360 :
    AlignedValid 12 4 missing17359_17360 records17359_17360 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17359
    maskCheck17359 AlignedValid.nil

def missing17358_17360 : List (BitVec (edgeCount 12)) :=
  missing17358_17359 ++ missing17359_17360
abbrev records17358_17360 : List Blob :=
  records17358_17359 ++ records17359_17360
theorem aligned17358_17360 :
    AlignedValid 12 4 missing17358_17360 records17358_17360 :=
  aligned17358_17359.append aligned17359_17360

def missing17356_17360 : List (BitVec (edgeCount 12)) :=
  missing17356_17358 ++ missing17358_17360
abbrev records17356_17360 : List Blob :=
  records17356_17358 ++ records17358_17360
theorem aligned17356_17360 :
    AlignedValid 12 4 missing17356_17360 records17356_17360 :=
  aligned17356_17358.append aligned17358_17360

def missing17352_17360 : List (BitVec (edgeCount 12)) :=
  missing17352_17356 ++ missing17356_17360
abbrev records17352_17360 : List Blob :=
  records17352_17356 ++ records17356_17360
theorem aligned17352_17360 :
    AlignedValid 12 4 missing17352_17360 records17352_17360 :=
  aligned17352_17356.append aligned17356_17360

def missing17344_17360 : List (BitVec (edgeCount 12)) :=
  missing17344_17352 ++ missing17352_17360
abbrev records17344_17360 : List Blob :=
  records17344_17352 ++ records17352_17360
theorem aligned17344_17360 :
    AlignedValid 12 4 missing17344_17360 records17344_17360 :=
  aligned17344_17352.append aligned17352_17360

def missing17360_17361 : List (BitVec (edgeCount 12)) :=
  [missing17360]
abbrev records17360_17361 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17360]
theorem aligned17360_17361 :
    AlignedValid 12 4 missing17360_17361 records17360_17361 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17360
    maskCheck17360 AlignedValid.nil

def missing17361_17362 : List (BitVec (edgeCount 12)) :=
  [missing17361]
abbrev records17361_17362 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17361]
theorem aligned17361_17362 :
    AlignedValid 12 4 missing17361_17362 records17361_17362 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17361
    maskCheck17361 AlignedValid.nil

def missing17360_17362 : List (BitVec (edgeCount 12)) :=
  missing17360_17361 ++ missing17361_17362
abbrev records17360_17362 : List Blob :=
  records17360_17361 ++ records17361_17362
theorem aligned17360_17362 :
    AlignedValid 12 4 missing17360_17362 records17360_17362 :=
  aligned17360_17361.append aligned17361_17362

def missing17362_17363 : List (BitVec (edgeCount 12)) :=
  [missing17362]
abbrev records17362_17363 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17362]
theorem aligned17362_17363 :
    AlignedValid 12 4 missing17362_17363 records17362_17363 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17362
    maskCheck17362 AlignedValid.nil

def missing17363_17364 : List (BitVec (edgeCount 12)) :=
  [missing17363]
abbrev records17363_17364 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17363]
theorem aligned17363_17364 :
    AlignedValid 12 4 missing17363_17364 records17363_17364 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17363
    maskCheck17363 AlignedValid.nil

def missing17362_17364 : List (BitVec (edgeCount 12)) :=
  missing17362_17363 ++ missing17363_17364
abbrev records17362_17364 : List Blob :=
  records17362_17363 ++ records17363_17364
theorem aligned17362_17364 :
    AlignedValid 12 4 missing17362_17364 records17362_17364 :=
  aligned17362_17363.append aligned17363_17364

def missing17360_17364 : List (BitVec (edgeCount 12)) :=
  missing17360_17362 ++ missing17362_17364
abbrev records17360_17364 : List Blob :=
  records17360_17362 ++ records17362_17364
theorem aligned17360_17364 :
    AlignedValid 12 4 missing17360_17364 records17360_17364 :=
  aligned17360_17362.append aligned17362_17364

def missing17364_17365 : List (BitVec (edgeCount 12)) :=
  [missing17364]
abbrev records17364_17365 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17364]
theorem aligned17364_17365 :
    AlignedValid 12 4 missing17364_17365 records17364_17365 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17364
    maskCheck17364 AlignedValid.nil

def missing17365_17366 : List (BitVec (edgeCount 12)) :=
  [missing17365]
abbrev records17365_17366 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17365]
theorem aligned17365_17366 :
    AlignedValid 12 4 missing17365_17366 records17365_17366 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17365
    maskCheck17365 AlignedValid.nil

def missing17364_17366 : List (BitVec (edgeCount 12)) :=
  missing17364_17365 ++ missing17365_17366
abbrev records17364_17366 : List Blob :=
  records17364_17365 ++ records17365_17366
theorem aligned17364_17366 :
    AlignedValid 12 4 missing17364_17366 records17364_17366 :=
  aligned17364_17365.append aligned17365_17366

def missing17366_17367 : List (BitVec (edgeCount 12)) :=
  [missing17366]
abbrev records17366_17367 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17366]
theorem aligned17366_17367 :
    AlignedValid 12 4 missing17366_17367 records17366_17367 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17366
    maskCheck17366 AlignedValid.nil

def missing17367_17368 : List (BitVec (edgeCount 12)) :=
  [missing17367]
abbrev records17367_17368 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17367]
theorem aligned17367_17368 :
    AlignedValid 12 4 missing17367_17368 records17367_17368 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17367
    maskCheck17367 AlignedValid.nil

def missing17366_17368 : List (BitVec (edgeCount 12)) :=
  missing17366_17367 ++ missing17367_17368
abbrev records17366_17368 : List Blob :=
  records17366_17367 ++ records17367_17368
theorem aligned17366_17368 :
    AlignedValid 12 4 missing17366_17368 records17366_17368 :=
  aligned17366_17367.append aligned17367_17368

def missing17364_17368 : List (BitVec (edgeCount 12)) :=
  missing17364_17366 ++ missing17366_17368
abbrev records17364_17368 : List Blob :=
  records17364_17366 ++ records17366_17368
theorem aligned17364_17368 :
    AlignedValid 12 4 missing17364_17368 records17364_17368 :=
  aligned17364_17366.append aligned17366_17368

def missing17360_17368 : List (BitVec (edgeCount 12)) :=
  missing17360_17364 ++ missing17364_17368
abbrev records17360_17368 : List Blob :=
  records17360_17364 ++ records17364_17368
theorem aligned17360_17368 :
    AlignedValid 12 4 missing17360_17368 records17360_17368 :=
  aligned17360_17364.append aligned17364_17368

def missing17368_17369 : List (BitVec (edgeCount 12)) :=
  [missing17368]
abbrev records17368_17369 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17368]
theorem aligned17368_17369 :
    AlignedValid 12 4 missing17368_17369 records17368_17369 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17368
    maskCheck17368 AlignedValid.nil

def missing17369_17370 : List (BitVec (edgeCount 12)) :=
  [missing17369]
abbrev records17369_17370 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17369]
theorem aligned17369_17370 :
    AlignedValid 12 4 missing17369_17370 records17369_17370 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17369
    maskCheck17369 AlignedValid.nil

def missing17368_17370 : List (BitVec (edgeCount 12)) :=
  missing17368_17369 ++ missing17369_17370
abbrev records17368_17370 : List Blob :=
  records17368_17369 ++ records17369_17370
theorem aligned17368_17370 :
    AlignedValid 12 4 missing17368_17370 records17368_17370 :=
  aligned17368_17369.append aligned17369_17370

def missing17370_17371 : List (BitVec (edgeCount 12)) :=
  [missing17370]
abbrev records17370_17371 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17370]
theorem aligned17370_17371 :
    AlignedValid 12 4 missing17370_17371 records17370_17371 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17370
    maskCheck17370 AlignedValid.nil

def missing17371_17372 : List (BitVec (edgeCount 12)) :=
  [missing17371]
abbrev records17371_17372 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17371]
theorem aligned17371_17372 :
    AlignedValid 12 4 missing17371_17372 records17371_17372 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17371
    maskCheck17371 AlignedValid.nil

def missing17370_17372 : List (BitVec (edgeCount 12)) :=
  missing17370_17371 ++ missing17371_17372
abbrev records17370_17372 : List Blob :=
  records17370_17371 ++ records17371_17372
theorem aligned17370_17372 :
    AlignedValid 12 4 missing17370_17372 records17370_17372 :=
  aligned17370_17371.append aligned17371_17372

def missing17368_17372 : List (BitVec (edgeCount 12)) :=
  missing17368_17370 ++ missing17370_17372
abbrev records17368_17372 : List Blob :=
  records17368_17370 ++ records17370_17372
theorem aligned17368_17372 :
    AlignedValid 12 4 missing17368_17372 records17368_17372 :=
  aligned17368_17370.append aligned17370_17372

def missing17372_17373 : List (BitVec (edgeCount 12)) :=
  [missing17372]
abbrev records17372_17373 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17372]
theorem aligned17372_17373 :
    AlignedValid 12 4 missing17372_17373 records17372_17373 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17372
    maskCheck17372 AlignedValid.nil

def missing17373_17374 : List (BitVec (edgeCount 12)) :=
  [missing17373]
abbrev records17373_17374 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17373]
theorem aligned17373_17374 :
    AlignedValid 12 4 missing17373_17374 records17373_17374 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17373
    maskCheck17373 AlignedValid.nil

def missing17372_17374 : List (BitVec (edgeCount 12)) :=
  missing17372_17373 ++ missing17373_17374
abbrev records17372_17374 : List Blob :=
  records17372_17373 ++ records17373_17374
theorem aligned17372_17374 :
    AlignedValid 12 4 missing17372_17374 records17372_17374 :=
  aligned17372_17373.append aligned17373_17374

def missing17374_17375 : List (BitVec (edgeCount 12)) :=
  [missing17374]
abbrev records17374_17375 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17374]
theorem aligned17374_17375 :
    AlignedValid 12 4 missing17374_17375 records17374_17375 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17374
    maskCheck17374 AlignedValid.nil

def missing17375_17376 : List (BitVec (edgeCount 12)) :=
  [missing17375]
abbrev records17375_17376 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17375]
theorem aligned17375_17376 :
    AlignedValid 12 4 missing17375_17376 records17375_17376 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17375
    maskCheck17375 AlignedValid.nil

def missing17374_17376 : List (BitVec (edgeCount 12)) :=
  missing17374_17375 ++ missing17375_17376
abbrev records17374_17376 : List Blob :=
  records17374_17375 ++ records17375_17376
theorem aligned17374_17376 :
    AlignedValid 12 4 missing17374_17376 records17374_17376 :=
  aligned17374_17375.append aligned17375_17376

def missing17372_17376 : List (BitVec (edgeCount 12)) :=
  missing17372_17374 ++ missing17374_17376
abbrev records17372_17376 : List Blob :=
  records17372_17374 ++ records17374_17376
theorem aligned17372_17376 :
    AlignedValid 12 4 missing17372_17376 records17372_17376 :=
  aligned17372_17374.append aligned17374_17376

def missing17368_17376 : List (BitVec (edgeCount 12)) :=
  missing17368_17372 ++ missing17372_17376
abbrev records17368_17376 : List Blob :=
  records17368_17372 ++ records17372_17376
theorem aligned17368_17376 :
    AlignedValid 12 4 missing17368_17376 records17368_17376 :=
  aligned17368_17372.append aligned17372_17376

def missing17360_17376 : List (BitVec (edgeCount 12)) :=
  missing17360_17368 ++ missing17368_17376
abbrev records17360_17376 : List Blob :=
  records17360_17368 ++ records17368_17376
theorem aligned17360_17376 :
    AlignedValid 12 4 missing17360_17376 records17360_17376 :=
  aligned17360_17368.append aligned17368_17376

def missing17344_17376 : List (BitVec (edgeCount 12)) :=
  missing17344_17360 ++ missing17360_17376
abbrev records17344_17376 : List Blob :=
  records17344_17360 ++ records17360_17376
theorem aligned17344_17376 :
    AlignedValid 12 4 missing17344_17376 records17344_17376 :=
  aligned17344_17360.append aligned17360_17376

def missing17376_17377 : List (BitVec (edgeCount 12)) :=
  [missing17376]
abbrev records17376_17377 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17376]
theorem aligned17376_17377 :
    AlignedValid 12 4 missing17376_17377 records17376_17377 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17376
    maskCheck17376 AlignedValid.nil

def missing17377_17378 : List (BitVec (edgeCount 12)) :=
  [missing17377]
abbrev records17377_17378 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17377]
theorem aligned17377_17378 :
    AlignedValid 12 4 missing17377_17378 records17377_17378 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17377
    maskCheck17377 AlignedValid.nil

def missing17376_17378 : List (BitVec (edgeCount 12)) :=
  missing17376_17377 ++ missing17377_17378
abbrev records17376_17378 : List Blob :=
  records17376_17377 ++ records17377_17378
theorem aligned17376_17378 :
    AlignedValid 12 4 missing17376_17378 records17376_17378 :=
  aligned17376_17377.append aligned17377_17378

def missing17378_17379 : List (BitVec (edgeCount 12)) :=
  [missing17378]
abbrev records17378_17379 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17378]
theorem aligned17378_17379 :
    AlignedValid 12 4 missing17378_17379 records17378_17379 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17378
    maskCheck17378 AlignedValid.nil

def missing17379_17380 : List (BitVec (edgeCount 12)) :=
  [missing17379]
abbrev records17379_17380 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17379]
theorem aligned17379_17380 :
    AlignedValid 12 4 missing17379_17380 records17379_17380 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17379
    maskCheck17379 AlignedValid.nil

def missing17378_17380 : List (BitVec (edgeCount 12)) :=
  missing17378_17379 ++ missing17379_17380
abbrev records17378_17380 : List Blob :=
  records17378_17379 ++ records17379_17380
theorem aligned17378_17380 :
    AlignedValid 12 4 missing17378_17380 records17378_17380 :=
  aligned17378_17379.append aligned17379_17380

def missing17376_17380 : List (BitVec (edgeCount 12)) :=
  missing17376_17378 ++ missing17378_17380
abbrev records17376_17380 : List Blob :=
  records17376_17378 ++ records17378_17380
theorem aligned17376_17380 :
    AlignedValid 12 4 missing17376_17380 records17376_17380 :=
  aligned17376_17378.append aligned17378_17380

def missing17380_17381 : List (BitVec (edgeCount 12)) :=
  [missing17380]
abbrev records17380_17381 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17380]
theorem aligned17380_17381 :
    AlignedValid 12 4 missing17380_17381 records17380_17381 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17380
    maskCheck17380 AlignedValid.nil

def missing17381_17382 : List (BitVec (edgeCount 12)) :=
  [missing17381]
abbrev records17381_17382 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17381]
theorem aligned17381_17382 :
    AlignedValid 12 4 missing17381_17382 records17381_17382 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17381
    maskCheck17381 AlignedValid.nil

def missing17380_17382 : List (BitVec (edgeCount 12)) :=
  missing17380_17381 ++ missing17381_17382
abbrev records17380_17382 : List Blob :=
  records17380_17381 ++ records17381_17382
theorem aligned17380_17382 :
    AlignedValid 12 4 missing17380_17382 records17380_17382 :=
  aligned17380_17381.append aligned17381_17382

def missing17382_17383 : List (BitVec (edgeCount 12)) :=
  [missing17382]
abbrev records17382_17383 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17382]
theorem aligned17382_17383 :
    AlignedValid 12 4 missing17382_17383 records17382_17383 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17382
    maskCheck17382 AlignedValid.nil

def missing17383_17384 : List (BitVec (edgeCount 12)) :=
  [missing17383]
abbrev records17383_17384 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17383]
theorem aligned17383_17384 :
    AlignedValid 12 4 missing17383_17384 records17383_17384 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17383
    maskCheck17383 AlignedValid.nil

def missing17382_17384 : List (BitVec (edgeCount 12)) :=
  missing17382_17383 ++ missing17383_17384
abbrev records17382_17384 : List Blob :=
  records17382_17383 ++ records17383_17384
theorem aligned17382_17384 :
    AlignedValid 12 4 missing17382_17384 records17382_17384 :=
  aligned17382_17383.append aligned17383_17384

def missing17380_17384 : List (BitVec (edgeCount 12)) :=
  missing17380_17382 ++ missing17382_17384
abbrev records17380_17384 : List Blob :=
  records17380_17382 ++ records17382_17384
theorem aligned17380_17384 :
    AlignedValid 12 4 missing17380_17384 records17380_17384 :=
  aligned17380_17382.append aligned17382_17384

def missing17376_17384 : List (BitVec (edgeCount 12)) :=
  missing17376_17380 ++ missing17380_17384
abbrev records17376_17384 : List Blob :=
  records17376_17380 ++ records17380_17384
theorem aligned17376_17384 :
    AlignedValid 12 4 missing17376_17384 records17376_17384 :=
  aligned17376_17380.append aligned17380_17384

def missing17384_17385 : List (BitVec (edgeCount 12)) :=
  [missing17384]
abbrev records17384_17385 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17384]
theorem aligned17384_17385 :
    AlignedValid 12 4 missing17384_17385 records17384_17385 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17384
    maskCheck17384 AlignedValid.nil

def missing17385_17386 : List (BitVec (edgeCount 12)) :=
  [missing17385]
abbrev records17385_17386 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17385]
theorem aligned17385_17386 :
    AlignedValid 12 4 missing17385_17386 records17385_17386 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17385
    maskCheck17385 AlignedValid.nil

def missing17384_17386 : List (BitVec (edgeCount 12)) :=
  missing17384_17385 ++ missing17385_17386
abbrev records17384_17386 : List Blob :=
  records17384_17385 ++ records17385_17386
theorem aligned17384_17386 :
    AlignedValid 12 4 missing17384_17386 records17384_17386 :=
  aligned17384_17385.append aligned17385_17386

def missing17386_17387 : List (BitVec (edgeCount 12)) :=
  [missing17386]
abbrev records17386_17387 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17386]
theorem aligned17386_17387 :
    AlignedValid 12 4 missing17386_17387 records17386_17387 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17386
    maskCheck17386 AlignedValid.nil

def missing17387_17388 : List (BitVec (edgeCount 12)) :=
  [missing17387]
abbrev records17387_17388 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17387]
theorem aligned17387_17388 :
    AlignedValid 12 4 missing17387_17388 records17387_17388 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17387
    maskCheck17387 AlignedValid.nil

def missing17386_17388 : List (BitVec (edgeCount 12)) :=
  missing17386_17387 ++ missing17387_17388
abbrev records17386_17388 : List Blob :=
  records17386_17387 ++ records17387_17388
theorem aligned17386_17388 :
    AlignedValid 12 4 missing17386_17388 records17386_17388 :=
  aligned17386_17387.append aligned17387_17388

def missing17384_17388 : List (BitVec (edgeCount 12)) :=
  missing17384_17386 ++ missing17386_17388
abbrev records17384_17388 : List Blob :=
  records17384_17386 ++ records17386_17388
theorem aligned17384_17388 :
    AlignedValid 12 4 missing17384_17388 records17384_17388 :=
  aligned17384_17386.append aligned17386_17388

def missing17388_17389 : List (BitVec (edgeCount 12)) :=
  [missing17388]
abbrev records17388_17389 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17388]
theorem aligned17388_17389 :
    AlignedValid 12 4 missing17388_17389 records17388_17389 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17388
    maskCheck17388 AlignedValid.nil

def missing17389_17390 : List (BitVec (edgeCount 12)) :=
  [missing17389]
abbrev records17389_17390 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17389]
theorem aligned17389_17390 :
    AlignedValid 12 4 missing17389_17390 records17389_17390 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17389
    maskCheck17389 AlignedValid.nil

def missing17388_17390 : List (BitVec (edgeCount 12)) :=
  missing17388_17389 ++ missing17389_17390
abbrev records17388_17390 : List Blob :=
  records17388_17389 ++ records17389_17390
theorem aligned17388_17390 :
    AlignedValid 12 4 missing17388_17390 records17388_17390 :=
  aligned17388_17389.append aligned17389_17390

def missing17390_17391 : List (BitVec (edgeCount 12)) :=
  [missing17390]
abbrev records17390_17391 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17390]
theorem aligned17390_17391 :
    AlignedValid 12 4 missing17390_17391 records17390_17391 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17390
    maskCheck17390 AlignedValid.nil

def missing17391_17392 : List (BitVec (edgeCount 12)) :=
  [missing17391]
abbrev records17391_17392 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17391]
theorem aligned17391_17392 :
    AlignedValid 12 4 missing17391_17392 records17391_17392 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17391
    maskCheck17391 AlignedValid.nil

def missing17390_17392 : List (BitVec (edgeCount 12)) :=
  missing17390_17391 ++ missing17391_17392
abbrev records17390_17392 : List Blob :=
  records17390_17391 ++ records17391_17392
theorem aligned17390_17392 :
    AlignedValid 12 4 missing17390_17392 records17390_17392 :=
  aligned17390_17391.append aligned17391_17392

def missing17388_17392 : List (BitVec (edgeCount 12)) :=
  missing17388_17390 ++ missing17390_17392
abbrev records17388_17392 : List Blob :=
  records17388_17390 ++ records17390_17392
theorem aligned17388_17392 :
    AlignedValid 12 4 missing17388_17392 records17388_17392 :=
  aligned17388_17390.append aligned17390_17392

def missing17384_17392 : List (BitVec (edgeCount 12)) :=
  missing17384_17388 ++ missing17388_17392
abbrev records17384_17392 : List Blob :=
  records17384_17388 ++ records17388_17392
theorem aligned17384_17392 :
    AlignedValid 12 4 missing17384_17392 records17384_17392 :=
  aligned17384_17388.append aligned17388_17392

def missing17376_17392 : List (BitVec (edgeCount 12)) :=
  missing17376_17384 ++ missing17384_17392
abbrev records17376_17392 : List Blob :=
  records17376_17384 ++ records17384_17392
theorem aligned17376_17392 :
    AlignedValid 12 4 missing17376_17392 records17376_17392 :=
  aligned17376_17384.append aligned17384_17392

def missing17392_17393 : List (BitVec (edgeCount 12)) :=
  [missing17392]
abbrev records17392_17393 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17392]
theorem aligned17392_17393 :
    AlignedValid 12 4 missing17392_17393 records17392_17393 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17392
    maskCheck17392 AlignedValid.nil

def missing17393_17394 : List (BitVec (edgeCount 12)) :=
  [missing17393]
abbrev records17393_17394 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17393]
theorem aligned17393_17394 :
    AlignedValid 12 4 missing17393_17394 records17393_17394 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17393
    maskCheck17393 AlignedValid.nil

def missing17392_17394 : List (BitVec (edgeCount 12)) :=
  missing17392_17393 ++ missing17393_17394
abbrev records17392_17394 : List Blob :=
  records17392_17393 ++ records17393_17394
theorem aligned17392_17394 :
    AlignedValid 12 4 missing17392_17394 records17392_17394 :=
  aligned17392_17393.append aligned17393_17394

def missing17394_17395 : List (BitVec (edgeCount 12)) :=
  [missing17394]
abbrev records17394_17395 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17394]
theorem aligned17394_17395 :
    AlignedValid 12 4 missing17394_17395 records17394_17395 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17394
    maskCheck17394 AlignedValid.nil

def missing17395_17396 : List (BitVec (edgeCount 12)) :=
  [missing17395]
abbrev records17395_17396 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17395]
theorem aligned17395_17396 :
    AlignedValid 12 4 missing17395_17396 records17395_17396 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17395
    maskCheck17395 AlignedValid.nil

def missing17394_17396 : List (BitVec (edgeCount 12)) :=
  missing17394_17395 ++ missing17395_17396
abbrev records17394_17396 : List Blob :=
  records17394_17395 ++ records17395_17396
theorem aligned17394_17396 :
    AlignedValid 12 4 missing17394_17396 records17394_17396 :=
  aligned17394_17395.append aligned17395_17396

def missing17392_17396 : List (BitVec (edgeCount 12)) :=
  missing17392_17394 ++ missing17394_17396
abbrev records17392_17396 : List Blob :=
  records17392_17394 ++ records17394_17396
theorem aligned17392_17396 :
    AlignedValid 12 4 missing17392_17396 records17392_17396 :=
  aligned17392_17394.append aligned17394_17396

def missing17396_17397 : List (BitVec (edgeCount 12)) :=
  [missing17396]
abbrev records17396_17397 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17396]
theorem aligned17396_17397 :
    AlignedValid 12 4 missing17396_17397 records17396_17397 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17396
    maskCheck17396 AlignedValid.nil

def missing17397_17398 : List (BitVec (edgeCount 12)) :=
  [missing17397]
abbrev records17397_17398 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17397]
theorem aligned17397_17398 :
    AlignedValid 12 4 missing17397_17398 records17397_17398 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17397
    maskCheck17397 AlignedValid.nil

def missing17396_17398 : List (BitVec (edgeCount 12)) :=
  missing17396_17397 ++ missing17397_17398
abbrev records17396_17398 : List Blob :=
  records17396_17397 ++ records17397_17398
theorem aligned17396_17398 :
    AlignedValid 12 4 missing17396_17398 records17396_17398 :=
  aligned17396_17397.append aligned17397_17398

def missing17398_17399 : List (BitVec (edgeCount 12)) :=
  [missing17398]
abbrev records17398_17399 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17398]
theorem aligned17398_17399 :
    AlignedValid 12 4 missing17398_17399 records17398_17399 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17398
    maskCheck17398 AlignedValid.nil

def missing17399_17400 : List (BitVec (edgeCount 12)) :=
  [missing17399]
abbrev records17399_17400 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17399]
theorem aligned17399_17400 :
    AlignedValid 12 4 missing17399_17400 records17399_17400 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17399
    maskCheck17399 AlignedValid.nil

def missing17398_17400 : List (BitVec (edgeCount 12)) :=
  missing17398_17399 ++ missing17399_17400
abbrev records17398_17400 : List Blob :=
  records17398_17399 ++ records17399_17400
theorem aligned17398_17400 :
    AlignedValid 12 4 missing17398_17400 records17398_17400 :=
  aligned17398_17399.append aligned17399_17400

def missing17396_17400 : List (BitVec (edgeCount 12)) :=
  missing17396_17398 ++ missing17398_17400
abbrev records17396_17400 : List Blob :=
  records17396_17398 ++ records17398_17400
theorem aligned17396_17400 :
    AlignedValid 12 4 missing17396_17400 records17396_17400 :=
  aligned17396_17398.append aligned17398_17400

def missing17392_17400 : List (BitVec (edgeCount 12)) :=
  missing17392_17396 ++ missing17396_17400
abbrev records17392_17400 : List Blob :=
  records17392_17396 ++ records17396_17400
theorem aligned17392_17400 :
    AlignedValid 12 4 missing17392_17400 records17392_17400 :=
  aligned17392_17396.append aligned17396_17400

def missing17400_17401 : List (BitVec (edgeCount 12)) :=
  [missing17400]
abbrev records17400_17401 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17400]
theorem aligned17400_17401 :
    AlignedValid 12 4 missing17400_17401 records17400_17401 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17400
    maskCheck17400 AlignedValid.nil

def missing17401_17402 : List (BitVec (edgeCount 12)) :=
  [missing17401]
abbrev records17401_17402 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17401]
theorem aligned17401_17402 :
    AlignedValid 12 4 missing17401_17402 records17401_17402 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17401
    maskCheck17401 AlignedValid.nil

def missing17400_17402 : List (BitVec (edgeCount 12)) :=
  missing17400_17401 ++ missing17401_17402
abbrev records17400_17402 : List Blob :=
  records17400_17401 ++ records17401_17402
theorem aligned17400_17402 :
    AlignedValid 12 4 missing17400_17402 records17400_17402 :=
  aligned17400_17401.append aligned17401_17402

def missing17402_17403 : List (BitVec (edgeCount 12)) :=
  [missing17402]
abbrev records17402_17403 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17402]
theorem aligned17402_17403 :
    AlignedValid 12 4 missing17402_17403 records17402_17403 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17402
    maskCheck17402 AlignedValid.nil

def missing17403_17404 : List (BitVec (edgeCount 12)) :=
  [missing17403]
abbrev records17403_17404 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17403]
theorem aligned17403_17404 :
    AlignedValid 12 4 missing17403_17404 records17403_17404 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17403
    maskCheck17403 AlignedValid.nil

def missing17402_17404 : List (BitVec (edgeCount 12)) :=
  missing17402_17403 ++ missing17403_17404
abbrev records17402_17404 : List Blob :=
  records17402_17403 ++ records17403_17404
theorem aligned17402_17404 :
    AlignedValid 12 4 missing17402_17404 records17402_17404 :=
  aligned17402_17403.append aligned17403_17404

def missing17400_17404 : List (BitVec (edgeCount 12)) :=
  missing17400_17402 ++ missing17402_17404
abbrev records17400_17404 : List Blob :=
  records17400_17402 ++ records17402_17404
theorem aligned17400_17404 :
    AlignedValid 12 4 missing17400_17404 records17400_17404 :=
  aligned17400_17402.append aligned17402_17404

def missing17404_17405 : List (BitVec (edgeCount 12)) :=
  [missing17404]
abbrev records17404_17405 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17404]
theorem aligned17404_17405 :
    AlignedValid 12 4 missing17404_17405 records17404_17405 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17404
    maskCheck17404 AlignedValid.nil

def missing17405_17406 : List (BitVec (edgeCount 12)) :=
  [missing17405]
abbrev records17405_17406 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17405]
theorem aligned17405_17406 :
    AlignedValid 12 4 missing17405_17406 records17405_17406 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17405
    maskCheck17405 AlignedValid.nil

def missing17404_17406 : List (BitVec (edgeCount 12)) :=
  missing17404_17405 ++ missing17405_17406
abbrev records17404_17406 : List Blob :=
  records17404_17405 ++ records17405_17406
theorem aligned17404_17406 :
    AlignedValid 12 4 missing17404_17406 records17404_17406 :=
  aligned17404_17405.append aligned17405_17406

def missing17406_17407 : List (BitVec (edgeCount 12)) :=
  [missing17406]
abbrev records17406_17407 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17406]
theorem aligned17406_17407 :
    AlignedValid 12 4 missing17406_17407 records17406_17407 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17406
    maskCheck17406 AlignedValid.nil

def missing17407_17408 : List (BitVec (edgeCount 12)) :=
  [missing17407]
abbrev records17407_17408 : List Blob :=
  [StrongPackedBucketN12A4Shard135.record17407]
theorem aligned17407_17408 :
    AlignedValid 12 4 missing17407_17408 records17407_17408 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard135.check17407
    maskCheck17407 AlignedValid.nil

def missing17406_17408 : List (BitVec (edgeCount 12)) :=
  missing17406_17407 ++ missing17407_17408
abbrev records17406_17408 : List Blob :=
  records17406_17407 ++ records17407_17408
theorem aligned17406_17408 :
    AlignedValid 12 4 missing17406_17408 records17406_17408 :=
  aligned17406_17407.append aligned17407_17408

def missing17404_17408 : List (BitVec (edgeCount 12)) :=
  missing17404_17406 ++ missing17406_17408
abbrev records17404_17408 : List Blob :=
  records17404_17406 ++ records17406_17408
theorem aligned17404_17408 :
    AlignedValid 12 4 missing17404_17408 records17404_17408 :=
  aligned17404_17406.append aligned17406_17408

def missing17400_17408 : List (BitVec (edgeCount 12)) :=
  missing17400_17404 ++ missing17404_17408
abbrev records17400_17408 : List Blob :=
  records17400_17404 ++ records17404_17408
theorem aligned17400_17408 :
    AlignedValid 12 4 missing17400_17408 records17400_17408 :=
  aligned17400_17404.append aligned17404_17408

def missing17392_17408 : List (BitVec (edgeCount 12)) :=
  missing17392_17400 ++ missing17400_17408
abbrev records17392_17408 : List Blob :=
  records17392_17400 ++ records17400_17408
theorem aligned17392_17408 :
    AlignedValid 12 4 missing17392_17408 records17392_17408 :=
  aligned17392_17400.append aligned17400_17408

def missing17376_17408 : List (BitVec (edgeCount 12)) :=
  missing17376_17392 ++ missing17392_17408
abbrev records17376_17408 : List Blob :=
  records17376_17392 ++ records17392_17408
theorem aligned17376_17408 :
    AlignedValid 12 4 missing17376_17408 records17376_17408 :=
  aligned17376_17392.append aligned17392_17408

def missing17344_17408 : List (BitVec (edgeCount 12)) :=
  missing17344_17376 ++ missing17376_17408
abbrev records17344_17408 : List Blob :=
  records17344_17376 ++ records17376_17408
theorem aligned17344_17408 :
    AlignedValid 12 4 missing17344_17408 records17344_17408 :=
  aligned17344_17376.append aligned17376_17408

def missing17280_17408 : List (BitVec (edgeCount 12)) :=
  missing17280_17344 ++ missing17344_17408
abbrev records17280_17408 : List Blob :=
  records17280_17344 ++ records17344_17408
theorem aligned17280_17408 :
    AlignedValid 12 4 missing17280_17408 records17280_17408 :=
  aligned17280_17344.append aligned17344_17408

abbrev missing : List (BitVec (edgeCount 12)) := missing17280_17408
abbrev records : List Blob := records17280_17408
theorem aligned : AlignedValid 12 4 missing records := aligned17280_17408

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard135
