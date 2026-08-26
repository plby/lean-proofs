/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard080

/-! Decode-only alignment checks for n=12, a=4, records 10240--10367. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard080

open PackedBucketCertificate

def missing10240 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40065326031805874176
theorem maskCheck10240 :
    checkMaskFor missing10240 StrongPackedBucketN12A4Shard080.record10240 = true := by
  decide

def missing10241 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55449622358903488512
theorem maskCheck10241 :
    checkMaskFor missing10241 StrongPackedBucketN12A4Shard080.record10241 = true := by
  decide

def missing10242 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55521679952941416448
theorem maskCheck10242 :
    checkMaskFor missing10242 StrongPackedBucketN12A4Shard080.record10242 = true := by
  decide

def missing10243 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55557708749960380416
theorem maskCheck10243 :
    checkMaskFor missing10243 StrongPackedBucketN12A4Shard080.record10243 = true := by
  decide

def missing10244 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55665795141017272320
theorem maskCheck10244 :
    checkMaskFor missing10244 StrongPackedBucketN12A4Shard080.record10244 = true := by
  decide

def missing10245 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55701823938036236288
theorem maskCheck10245 :
    checkMaskFor missing10245 StrongPackedBucketN12A4Shard080.record10245 = true := by
  decide

def missing10246 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55773881532074164224
theorem maskCheck10246 :
    checkMaskFor missing10246 StrongPackedBucketN12A4Shard080.record10246 = true := by
  decide

def missing10247 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56206227096301731840
theorem maskCheck10247 :
    checkMaskFor missing10247 StrongPackedBucketN12A4Shard080.record10247 = true := by
  decide

def missing10248 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56530486269472407552
theorem maskCheck10248 :
    checkMaskFor missing10248 StrongPackedBucketN12A4Shard080.record10248 = true := by
  decide

def missing10249 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56566515066491371520
theorem maskCheck10249 :
    checkMaskFor missing10249 StrongPackedBucketN12A4Shard080.record10249 = true := by
  decide

def missing10250 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56638572660529299456
theorem maskCheck10250 :
    checkMaskFor missing10250 StrongPackedBucketN12A4Shard080.record10250 = true := by
  decide

def missing10251 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56782687848605155328
theorem maskCheck10251 :
    checkMaskFor missing10251 StrongPackedBucketN12A4Shard080.record10251 = true := by
  decide

def missing10252 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57683407774079254528
theorem maskCheck10252 :
    checkMaskFor missing10252 StrongPackedBucketN12A4Shard080.record10252 = true := by
  decide

def missing10253 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57719436571098218496
theorem maskCheck10253 :
    checkMaskFor missing10253 StrongPackedBucketN12A4Shard080.record10253 = true := by
  decide

def missing10254 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57791494165136146432
theorem maskCheck10254 :
    checkMaskFor missing10254 StrongPackedBucketN12A4Shard080.record10254 = true := by
  decide

def missing10255 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57935609353212002304
theorem maskCheck10255 :
    checkMaskFor missing10255 StrongPackedBucketN12A4Shard080.record10255 = true := by
  decide

def missing10256 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58800300481667137536
theorem maskCheck10256 :
    checkMaskFor missing10256 StrongPackedBucketN12A4Shard080.record10256 = true := by
  decide

def missing10257 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 62259064995487678464
theorem maskCheck10257 :
    checkMaskFor missing10257 StrongPackedBucketN12A4Shard080.record10257 = true := by
  decide

def missing10258 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64600936801720336384
theorem maskCheck10258 :
    checkMaskFor missing10258 StrongPackedBucketN12A4Shard080.record10258 = true := by
  decide

def missing10259 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64636965598739300352
theorem maskCheck10259 :
    checkMaskFor missing10259 StrongPackedBucketN12A4Shard080.record10259 = true := by
  decide

def missing10260 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64709023192777228288
theorem maskCheck10260 :
    checkMaskFor missing10260 StrongPackedBucketN12A4Shard080.record10260 = true := by
  decide

def missing10261 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64853138380853084160
theorem maskCheck10261 :
    checkMaskFor missing10261 StrongPackedBucketN12A4Shard080.record10261 = true := by
  decide

def missing10262 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65717829509308219392
theorem maskCheck10262 :
    checkMaskFor missing10262 StrongPackedBucketN12A4Shard080.record10262 = true := by
  decide

def missing10263 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 66870751013915066368
theorem maskCheck10263 :
    checkMaskFor missing10263 StrongPackedBucketN12A4Shard080.record10263 = true := by
  decide

def missing10264 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 541981992607023104
theorem maskCheck10264 :
    checkMaskFor missing10264 StrongPackedBucketN12A4Shard080.record10264 = true := by
  decide

def missing10265 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 830212368758734848
theorem maskCheck10265 :
    checkMaskFor missing10265 StrongPackedBucketN12A4Shard080.record10265 = true := by
  decide

def missing10266 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1046385150872518656
theorem maskCheck10266 :
    checkMaskFor missing10266 StrongPackedBucketN12A4Shard080.record10266 = true := by
  decide

def missing10267 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1839018685289725952
theorem maskCheck10267 :
    checkMaskFor missing10267 StrongPackedBucketN12A4Shard080.record10267 = true := by
  decide

def missing10268 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1911076279327653888
theorem maskCheck10268 :
    checkMaskFor missing10268 StrongPackedBucketN12A4Shard080.record10268 = true := by
  decide

def missing10269 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2163277858460401664
theorem maskCheck10269 :
    checkMaskFor missing10269 StrongPackedBucketN12A4Shard080.record10269 = true := by
  decide

def missing10270 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2559594625669005312
theorem maskCheck10270 :
    checkMaskFor missing10270 StrongPackedBucketN12A4Shard080.record10270 = true := by
  decide

def missing10271 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2775767407782789120
theorem maskCheck10271 :
    checkMaskFor missing10271 StrongPackedBucketN12A4Shard080.record10271 = true := by
  decide

def missing10272 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2991940189896572928
theorem maskCheck10272 :
    checkMaskFor missing10272 StrongPackedBucketN12A4Shard080.record10272 = true := by
  decide

def missing10273 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3063997783934500864
theorem maskCheck10273 :
    checkMaskFor missing10273 StrongPackedBucketN12A4Shard080.record10273 = true := by
  decide

def missing10274 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3316199363067248640
theorem maskCheck10274 :
    checkMaskFor missing10274 StrongPackedBucketN12A4Shard080.record10274 = true := by
  decide

def missing10275 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4072804100465491968
theorem maskCheck10275 :
    checkMaskFor missing10275 StrongPackedBucketN12A4Shard080.record10275 = true := by
  decide

def missing10276 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4180890491522383872
theorem maskCheck10276 :
    checkMaskFor missing10276 StrongPackedBucketN12A4Shard080.record10276 = true := by
  decide

def missing10277 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7027165456020537344
theorem maskCheck10277 :
    checkMaskFor missing10277 StrongPackedBucketN12A4Shard080.record10277 = true := by
  decide

def missing10278 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7099223050058465280
theorem maskCheck10278 :
    checkMaskFor missing10278 StrongPackedBucketN12A4Shard080.record10278 = true := by
  decide

def missing10279 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7351424629191213056
theorem maskCheck10279 :
    checkMaskFor missing10279 StrongPackedBucketN12A4Shard080.record10279 = true := by
  decide

def missing10280 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7531568614286032896
theorem maskCheck10280 :
    checkMaskFor missing10280 StrongPackedBucketN12A4Shard080.record10280 = true := by
  decide

def missing10281 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7639655005342924800
theorem maskCheck10281 :
    checkMaskFor missing10281 StrongPackedBucketN12A4Shard080.record10281 = true := by
  decide

def missing10282 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8648461321873915904
theorem maskCheck10282 :
    checkMaskFor missing10282 StrongPackedBucketN12A4Shard080.record10282 = true := by
  decide

def missing10283 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9477123653310087168
theorem maskCheck10283 :
    checkMaskFor missing10283 StrongPackedBucketN12A4Shard080.record10283 = true := by
  decide

def missing10284 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9693296435423870976
theorem maskCheck10284 :
    checkMaskFor missing10284 StrongPackedBucketN12A4Shard080.record10284 = true := by
  decide

def missing10285 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9909469217537654784
theorem maskCheck10285 :
    checkMaskFor missing10285 StrongPackedBucketN12A4Shard080.record10285 = true := by
  decide

def missing10286 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9981526811575582720
theorem maskCheck10286 :
    checkMaskFor missing10286 StrongPackedBucketN12A4Shard080.record10286 = true := by
  decide

def missing10287 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10233728390708330496
theorem maskCheck10287 :
    checkMaskFor missing10287 StrongPackedBucketN12A4Shard080.record10287 = true := by
  decide

def missing10288 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10990333128106573824
theorem maskCheck10288 :
    checkMaskFor missing10288 StrongPackedBucketN12A4Shard080.record10288 = true := by
  decide

def missing10289 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11098419519163465728
theorem maskCheck10289 :
    checkMaskFor missing10289 StrongPackedBucketN12A4Shard080.record10289 = true := by
  decide

def missing10290 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11638851474447925248
theorem maskCheck10290 :
    checkMaskFor missing10290 StrongPackedBucketN12A4Shard080.record10290 = true := by
  decide

def missing10291 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11710909068485853184
theorem maskCheck10291 :
    checkMaskFor missing10291 StrongPackedBucketN12A4Shard080.record10291 = true := by
  decide

def missing10292 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11963110647618600960
theorem maskCheck10292 :
    checkMaskFor missing10292 StrongPackedBucketN12A4Shard080.record10292 = true := by
  decide

def missing10293 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12143254632713420800
theorem maskCheck10293 :
    checkMaskFor missing10293 StrongPackedBucketN12A4Shard080.record10293 = true := by
  decide

def missing10294 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12251341023770312704
theorem maskCheck10294 :
    checkMaskFor missing10294 StrongPackedBucketN12A4Shard080.record10294 = true := by
  decide

def missing10295 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13260147340301303808
theorem maskCheck10295 :
    checkMaskFor missing10295 StrongPackedBucketN12A4Shard080.record10295 = true := by
  decide

def missing10296 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16178479898837385216
theorem maskCheck10296 :
    checkMaskFor missing10296 StrongPackedBucketN12A4Shard080.record10296 = true := by
  decide

def missing10297 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16286566289894277120
theorem maskCheck10297 :
    checkMaskFor missing10297 StrongPackedBucketN12A4Shard080.record10297 = true := by
  decide

def missing10298 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16718911854121844736
theorem maskCheck10298 :
    checkMaskFor missing10298 StrongPackedBucketN12A4Shard080.record10298 = true := by
  decide

def missing10299 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18700495690164862976
theorem maskCheck10299 :
    checkMaskFor missing10299 StrongPackedBucketN12A4Shard080.record10299 = true := by
  decide

def missing10300 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18916668472278646784
theorem maskCheck10300 :
    checkMaskFor missing10300 StrongPackedBucketN12A4Shard080.record10300 = true := by
  decide

def missing10301 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19457100427563106304
theorem maskCheck10301 :
    checkMaskFor missing10301 StrongPackedBucketN12A4Shard080.record10301 = true := by
  decide

def missing10302 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19709302006695854080
theorem maskCheck10302 :
    checkMaskFor missing10302 StrongPackedBucketN12A4Shard080.record10302 = true := by
  decide

def missing10303 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19781359600733782016
theorem maskCheck10303 :
    checkMaskFor missing10303 StrongPackedBucketN12A4Shard080.record10303 = true := by
  decide

def missing10304 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20033561179866529792
theorem maskCheck10304 :
    checkMaskFor missing10304 StrongPackedBucketN12A4Shard080.record10304 = true := by
  decide

def missing10305 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20321791556018241536
theorem maskCheck10305 :
    checkMaskFor missing10305 StrongPackedBucketN12A4Shard080.record10305 = true := by
  decide

def missing10306 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21186482684473376768
theorem maskCheck10306 :
    checkMaskFor missing10306 StrongPackedBucketN12A4Shard080.record10306 = true := by
  decide

def missing10307 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22051173812928512000
theorem maskCheck10307 :
    checkMaskFor missing10307 StrongPackedBucketN12A4Shard080.record10307 = true := by
  decide

def missing10308 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55449868649508110336
theorem maskCheck10308 :
    checkMaskFor missing10308 StrongPackedBucketN12A4Shard080.record10308 = true := by
  decide

def missing10309 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55521926243546038272
theorem maskCheck10309 :
    checkMaskFor missing10309 StrongPackedBucketN12A4Shard080.record10309 = true := by
  decide

def missing10310 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55774127822678786048
theorem maskCheck10310 :
    checkMaskFor missing10310 StrongPackedBucketN12A4Shard080.record10310 = true := by
  decide

def missing10311 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55954271807773605888
theorem maskCheck10311 :
    checkMaskFor missing10311 StrongPackedBucketN12A4Shard080.record10311 = true := by
  decide

def missing10312 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56062358198830497792
theorem maskCheck10312 :
    checkMaskFor missing10312 StrongPackedBucketN12A4Shard080.record10312 = true := by
  decide

def missing10313 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57071164515361488896
theorem maskCheck10313 :
    checkMaskFor missing10313 StrongPackedBucketN12A4Shard080.record10313 = true := by
  decide

def missing10314 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57683654064683876352
theorem maskCheck10314 :
    checkMaskFor missing10314 StrongPackedBucketN12A4Shard080.record10314 = true := by
  decide

def missing10315 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57791740455740768256
theorem maskCheck10315 :
    checkMaskFor missing10315 StrongPackedBucketN12A4Shard080.record10315 = true := by
  decide

def missing10316 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 58224086019968335872
theorem maskCheck10316 :
    checkMaskFor missing10316 StrongPackedBucketN12A4Shard080.record10316 = true := by
  decide

def missing10317 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 62259311286092300288
theorem maskCheck10317 :
    checkMaskFor missing10317 StrongPackedBucketN12A4Shard080.record10317 = true := by
  decide

def missing10318 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64601183092324958208
theorem maskCheck10318 :
    checkMaskFor missing10318 StrongPackedBucketN12A4Shard080.record10318 = true := by
  decide

def missing10319 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64709269483381850112
theorem maskCheck10319 :
    checkMaskFor missing10319 StrongPackedBucketN12A4Shard080.record10319 = true := by
  decide

def missing10320 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65141615047609417728
theorem maskCheck10320 :
    checkMaskFor missing10320 StrongPackedBucketN12A4Shard080.record10320 = true := by
  decide

def missing10321 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 66870997304519688192
theorem maskCheck10321 :
    checkMaskFor missing10321 StrongPackedBucketN12A4Shard080.record10321 = true := by
  decide

def missing10322 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 543846764327731200
theorem maskCheck10322 :
    checkMaskFor missing10322 StrongPackedBucketN12A4Shard080.record10322 = true := by
  decide

def missing10323 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1048249922593226752
theorem maskCheck10323 :
    checkMaskFor missing10323 StrongPackedBucketN12A4Shard080.record10323 = true := by
  decide

def missing10324 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1084278719612190720
theorem maskCheck10324 :
    checkMaskFor missing10324 StrongPackedBucketN12A4Shard080.record10324 = true := by
  decide

def missing10325 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1408537892782866432
theorem maskCheck10325 :
    checkMaskFor missing10325 StrongPackedBucketN12A4Shard080.record10325 = true := by
  decide

def missing10326 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1624710674896650240
theorem maskCheck10326 :
    checkMaskFor missing10326 StrongPackedBucketN12A4Shard080.record10326 = true := by
  decide

def missing10327 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1660739471915614208
theorem maskCheck10327 :
    checkMaskFor missing10327 StrongPackedBucketN12A4Shard080.record10327 = true := by
  decide

def missing10328 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2165142630181109760
theorem maskCheck10328 :
    checkMaskFor missing10328 StrongPackedBucketN12A4Shard080.record10328 = true := by
  decide

def missing10329 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3570265713920704512
theorem maskCheck10329 :
    checkMaskFor missing10329 StrongPackedBucketN12A4Shard080.record10329 = true := by
  decide

def missing10330 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3642323307958632448
theorem maskCheck10330 :
    checkMaskFor missing10330 StrongPackedBucketN12A4Shard080.record10330 = true := by
  decide

def missing10331 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3678352104977596416
theorem maskCheck10331 :
    checkMaskFor missing10331 StrongPackedBucketN12A4Shard080.record10331 = true := by
  decide

def missing10332 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3894524887091380224
theorem maskCheck10332 :
    checkMaskFor missing10332 StrongPackedBucketN12A4Shard080.record10332 = true := by
  decide

def missing10333 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4867302406603407360
theorem maskCheck10333 :
    checkMaskFor missing10333 StrongPackedBucketN12A4Shard080.record10333 = true := by
  decide

def missing10334 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5083475188717191168
theorem maskCheck10334 :
    checkMaskFor missing10334 StrongPackedBucketN12A4Shard080.record10334 = true := by
  decide

def missing10335 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5119503985736155136
theorem maskCheck10335 :
    checkMaskFor missing10335 StrongPackedBucketN12A4Shard080.record10335 = true := by
  decide

def missing10336 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5623907144001650688
theorem maskCheck10336 :
    checkMaskFor missing10336 StrongPackedBucketN12A4Shard080.record10336 = true := by
  decide

def missing10337 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5876108723134398464
theorem maskCheck10337 :
    checkMaskFor missing10337 StrongPackedBucketN12A4Shard080.record10337 = true := by
  decide

def missing10338 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5948166317172326400
theorem maskCheck10338 :
    checkMaskFor missing10338 StrongPackedBucketN12A4Shard080.record10338 = true := by
  decide

def missing10339 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5984195114191290368
theorem maskCheck10339 :
    checkMaskFor missing10339 StrongPackedBucketN12A4Shard080.record10339 = true := by
  decide

def missing10340 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6200367896305074176
theorem maskCheck10340 :
    checkMaskFor missing10340 StrongPackedBucketN12A4Shard080.record10340 = true := by
  decide

def missing10341 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8109894138310164480
theorem maskCheck10341 :
    checkMaskFor missing10341 StrongPackedBucketN12A4Shard080.record10341 = true := by
  decide

def missing10342 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8145922935329128448
theorem maskCheck10342 :
    checkMaskFor missing10342 StrongPackedBucketN12A4Shard080.record10342 = true := by
  decide

def missing10343 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8217980529367056384
theorem maskCheck10343 :
    checkMaskFor missing10343 StrongPackedBucketN12A4Shard080.record10343 = true := by
  decide

def missing10344 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9478988425030795264
theorem maskCheck10344 :
    checkMaskFor missing10344 StrongPackedBucketN12A4Shard080.record10344 = true := by
  decide

def missing10345 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9695161207144579072
theorem maskCheck10345 :
    checkMaskFor missing10345 StrongPackedBucketN12A4Shard080.record10345 = true := by
  decide

def missing10346 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9731190004163543040
theorem maskCheck10346 :
    checkMaskFor missing10346 StrongPackedBucketN12A4Shard080.record10346 = true := by
  decide

def missing10347 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10235593162429038592
theorem maskCheck10347 :
    checkMaskFor missing10347 StrongPackedBucketN12A4Shard080.record10347 = true := by
  decide

def missing10348 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10487794741561786368
theorem maskCheck10348 :
    checkMaskFor missing10348 StrongPackedBucketN12A4Shard080.record10348 = true := by
  decide

def missing10349 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10559852335599714304
theorem maskCheck10349 :
    checkMaskFor missing10349 StrongPackedBucketN12A4Shard080.record10349 = true := by
  decide

def missing10350 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10595881132618678272
theorem maskCheck10350 :
    checkMaskFor missing10350 StrongPackedBucketN12A4Shard080.record10350 = true := by
  decide

def missing10351 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10812053914732462080
theorem maskCheck10351 :
    checkMaskFor missing10351 StrongPackedBucketN12A4Shard080.record10351 = true := by
  decide

def missing10352 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12721580156737552384
theorem maskCheck10352 :
    checkMaskFor missing10352 StrongPackedBucketN12A4Shard080.record10352 = true := by
  decide

def missing10353 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12757608953756516352
theorem maskCheck10353 :
    checkMaskFor missing10353 StrongPackedBucketN12A4Shard080.record10353 = true := by
  decide

def missing10354 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12829666547794444288
theorem maskCheck10354 :
    checkMaskFor missing10354 StrongPackedBucketN12A4Shard080.record10354 = true := by
  decide

def missing10355 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13946559255382327296
theorem maskCheck10355 :
    checkMaskFor missing10355 StrongPackedBucketN12A4Shard080.record10355 = true := by
  decide

def missing10356 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14018616849420255232
theorem maskCheck10356 :
    checkMaskFor missing10356 StrongPackedBucketN12A4Shard080.record10356 = true := by
  decide

def missing10357 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14054645646439219200
theorem maskCheck10357 :
    checkMaskFor missing10357 StrongPackedBucketN12A4Shard080.record10357 = true := by
  decide

def missing10358 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14270818428553003008
theorem maskCheck10358 :
    checkMaskFor missing10358 StrongPackedBucketN12A4Shard080.record10358 = true := by
  decide

def missing10359 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15027423165951246336
theorem maskCheck10359 :
    checkMaskFor missing10359 StrongPackedBucketN12A4Shard080.record10359 = true := by
  decide

def missing10360 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15063451962970210304
theorem maskCheck10360 :
    checkMaskFor missing10360 StrongPackedBucketN12A4Shard080.record10360 = true := by
  decide

def missing10361 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 15135509557008138240
theorem maskCheck10361 :
    checkMaskFor missing10361 StrongPackedBucketN12A4Shard080.record10361 = true := by
  decide

def missing10362 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17297237378145976320
theorem maskCheck10362 :
    checkMaskFor missing10362 StrongPackedBucketN12A4Shard080.record10362 = true := by
  decide

def missing10363 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18702360461885571072
theorem maskCheck10363 :
    checkMaskFor missing10363 StrongPackedBucketN12A4Shard080.record10363 = true := by
  decide

def missing10364 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18954562041018318848
theorem maskCheck10364 :
    checkMaskFor missing10364 StrongPackedBucketN12A4Shard080.record10364 = true := by
  decide

def missing10365 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19458965199283814400
theorem maskCheck10365 :
    checkMaskFor missing10365 StrongPackedBucketN12A4Shard080.record10365 = true := by
  decide

def missing10366 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19711166778416562176
theorem maskCheck10366 :
    checkMaskFor missing10366 StrongPackedBucketN12A4Shard080.record10366 = true := by
  decide

def missing10367 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19783224372454490112
theorem maskCheck10367 :
    checkMaskFor missing10367 StrongPackedBucketN12A4Shard080.record10367 = true := by
  decide

def missing10240_10241 : List (BitVec (edgeCount 12)) :=
  [missing10240]
abbrev records10240_10241 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10240]
theorem aligned10240_10241 :
    AlignedValid 12 4 missing10240_10241 records10240_10241 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10240
    maskCheck10240 AlignedValid.nil

def missing10241_10242 : List (BitVec (edgeCount 12)) :=
  [missing10241]
abbrev records10241_10242 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10241]
theorem aligned10241_10242 :
    AlignedValid 12 4 missing10241_10242 records10241_10242 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10241
    maskCheck10241 AlignedValid.nil

def missing10240_10242 : List (BitVec (edgeCount 12)) :=
  missing10240_10241 ++ missing10241_10242
abbrev records10240_10242 : List Blob :=
  records10240_10241 ++ records10241_10242
theorem aligned10240_10242 :
    AlignedValid 12 4 missing10240_10242 records10240_10242 :=
  aligned10240_10241.append aligned10241_10242

def missing10242_10243 : List (BitVec (edgeCount 12)) :=
  [missing10242]
abbrev records10242_10243 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10242]
theorem aligned10242_10243 :
    AlignedValid 12 4 missing10242_10243 records10242_10243 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10242
    maskCheck10242 AlignedValid.nil

def missing10243_10244 : List (BitVec (edgeCount 12)) :=
  [missing10243]
abbrev records10243_10244 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10243]
theorem aligned10243_10244 :
    AlignedValid 12 4 missing10243_10244 records10243_10244 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10243
    maskCheck10243 AlignedValid.nil

def missing10242_10244 : List (BitVec (edgeCount 12)) :=
  missing10242_10243 ++ missing10243_10244
abbrev records10242_10244 : List Blob :=
  records10242_10243 ++ records10243_10244
theorem aligned10242_10244 :
    AlignedValid 12 4 missing10242_10244 records10242_10244 :=
  aligned10242_10243.append aligned10243_10244

def missing10240_10244 : List (BitVec (edgeCount 12)) :=
  missing10240_10242 ++ missing10242_10244
abbrev records10240_10244 : List Blob :=
  records10240_10242 ++ records10242_10244
theorem aligned10240_10244 :
    AlignedValid 12 4 missing10240_10244 records10240_10244 :=
  aligned10240_10242.append aligned10242_10244

def missing10244_10245 : List (BitVec (edgeCount 12)) :=
  [missing10244]
abbrev records10244_10245 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10244]
theorem aligned10244_10245 :
    AlignedValid 12 4 missing10244_10245 records10244_10245 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10244
    maskCheck10244 AlignedValid.nil

def missing10245_10246 : List (BitVec (edgeCount 12)) :=
  [missing10245]
abbrev records10245_10246 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10245]
theorem aligned10245_10246 :
    AlignedValid 12 4 missing10245_10246 records10245_10246 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10245
    maskCheck10245 AlignedValid.nil

def missing10244_10246 : List (BitVec (edgeCount 12)) :=
  missing10244_10245 ++ missing10245_10246
abbrev records10244_10246 : List Blob :=
  records10244_10245 ++ records10245_10246
theorem aligned10244_10246 :
    AlignedValid 12 4 missing10244_10246 records10244_10246 :=
  aligned10244_10245.append aligned10245_10246

def missing10246_10247 : List (BitVec (edgeCount 12)) :=
  [missing10246]
abbrev records10246_10247 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10246]
theorem aligned10246_10247 :
    AlignedValid 12 4 missing10246_10247 records10246_10247 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10246
    maskCheck10246 AlignedValid.nil

def missing10247_10248 : List (BitVec (edgeCount 12)) :=
  [missing10247]
abbrev records10247_10248 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10247]
theorem aligned10247_10248 :
    AlignedValid 12 4 missing10247_10248 records10247_10248 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10247
    maskCheck10247 AlignedValid.nil

def missing10246_10248 : List (BitVec (edgeCount 12)) :=
  missing10246_10247 ++ missing10247_10248
abbrev records10246_10248 : List Blob :=
  records10246_10247 ++ records10247_10248
theorem aligned10246_10248 :
    AlignedValid 12 4 missing10246_10248 records10246_10248 :=
  aligned10246_10247.append aligned10247_10248

def missing10244_10248 : List (BitVec (edgeCount 12)) :=
  missing10244_10246 ++ missing10246_10248
abbrev records10244_10248 : List Blob :=
  records10244_10246 ++ records10246_10248
theorem aligned10244_10248 :
    AlignedValid 12 4 missing10244_10248 records10244_10248 :=
  aligned10244_10246.append aligned10246_10248

def missing10240_10248 : List (BitVec (edgeCount 12)) :=
  missing10240_10244 ++ missing10244_10248
abbrev records10240_10248 : List Blob :=
  records10240_10244 ++ records10244_10248
theorem aligned10240_10248 :
    AlignedValid 12 4 missing10240_10248 records10240_10248 :=
  aligned10240_10244.append aligned10244_10248

def missing10248_10249 : List (BitVec (edgeCount 12)) :=
  [missing10248]
abbrev records10248_10249 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10248]
theorem aligned10248_10249 :
    AlignedValid 12 4 missing10248_10249 records10248_10249 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10248
    maskCheck10248 AlignedValid.nil

def missing10249_10250 : List (BitVec (edgeCount 12)) :=
  [missing10249]
abbrev records10249_10250 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10249]
theorem aligned10249_10250 :
    AlignedValid 12 4 missing10249_10250 records10249_10250 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10249
    maskCheck10249 AlignedValid.nil

def missing10248_10250 : List (BitVec (edgeCount 12)) :=
  missing10248_10249 ++ missing10249_10250
abbrev records10248_10250 : List Blob :=
  records10248_10249 ++ records10249_10250
theorem aligned10248_10250 :
    AlignedValid 12 4 missing10248_10250 records10248_10250 :=
  aligned10248_10249.append aligned10249_10250

def missing10250_10251 : List (BitVec (edgeCount 12)) :=
  [missing10250]
abbrev records10250_10251 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10250]
theorem aligned10250_10251 :
    AlignedValid 12 4 missing10250_10251 records10250_10251 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10250
    maskCheck10250 AlignedValid.nil

def missing10251_10252 : List (BitVec (edgeCount 12)) :=
  [missing10251]
abbrev records10251_10252 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10251]
theorem aligned10251_10252 :
    AlignedValid 12 4 missing10251_10252 records10251_10252 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10251
    maskCheck10251 AlignedValid.nil

def missing10250_10252 : List (BitVec (edgeCount 12)) :=
  missing10250_10251 ++ missing10251_10252
abbrev records10250_10252 : List Blob :=
  records10250_10251 ++ records10251_10252
theorem aligned10250_10252 :
    AlignedValid 12 4 missing10250_10252 records10250_10252 :=
  aligned10250_10251.append aligned10251_10252

def missing10248_10252 : List (BitVec (edgeCount 12)) :=
  missing10248_10250 ++ missing10250_10252
abbrev records10248_10252 : List Blob :=
  records10248_10250 ++ records10250_10252
theorem aligned10248_10252 :
    AlignedValid 12 4 missing10248_10252 records10248_10252 :=
  aligned10248_10250.append aligned10250_10252

def missing10252_10253 : List (BitVec (edgeCount 12)) :=
  [missing10252]
abbrev records10252_10253 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10252]
theorem aligned10252_10253 :
    AlignedValid 12 4 missing10252_10253 records10252_10253 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10252
    maskCheck10252 AlignedValid.nil

def missing10253_10254 : List (BitVec (edgeCount 12)) :=
  [missing10253]
abbrev records10253_10254 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10253]
theorem aligned10253_10254 :
    AlignedValid 12 4 missing10253_10254 records10253_10254 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10253
    maskCheck10253 AlignedValid.nil

def missing10252_10254 : List (BitVec (edgeCount 12)) :=
  missing10252_10253 ++ missing10253_10254
abbrev records10252_10254 : List Blob :=
  records10252_10253 ++ records10253_10254
theorem aligned10252_10254 :
    AlignedValid 12 4 missing10252_10254 records10252_10254 :=
  aligned10252_10253.append aligned10253_10254

def missing10254_10255 : List (BitVec (edgeCount 12)) :=
  [missing10254]
abbrev records10254_10255 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10254]
theorem aligned10254_10255 :
    AlignedValid 12 4 missing10254_10255 records10254_10255 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10254
    maskCheck10254 AlignedValid.nil

def missing10255_10256 : List (BitVec (edgeCount 12)) :=
  [missing10255]
abbrev records10255_10256 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10255]
theorem aligned10255_10256 :
    AlignedValid 12 4 missing10255_10256 records10255_10256 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10255
    maskCheck10255 AlignedValid.nil

def missing10254_10256 : List (BitVec (edgeCount 12)) :=
  missing10254_10255 ++ missing10255_10256
abbrev records10254_10256 : List Blob :=
  records10254_10255 ++ records10255_10256
theorem aligned10254_10256 :
    AlignedValid 12 4 missing10254_10256 records10254_10256 :=
  aligned10254_10255.append aligned10255_10256

def missing10252_10256 : List (BitVec (edgeCount 12)) :=
  missing10252_10254 ++ missing10254_10256
abbrev records10252_10256 : List Blob :=
  records10252_10254 ++ records10254_10256
theorem aligned10252_10256 :
    AlignedValid 12 4 missing10252_10256 records10252_10256 :=
  aligned10252_10254.append aligned10254_10256

def missing10248_10256 : List (BitVec (edgeCount 12)) :=
  missing10248_10252 ++ missing10252_10256
abbrev records10248_10256 : List Blob :=
  records10248_10252 ++ records10252_10256
theorem aligned10248_10256 :
    AlignedValid 12 4 missing10248_10256 records10248_10256 :=
  aligned10248_10252.append aligned10252_10256

def missing10240_10256 : List (BitVec (edgeCount 12)) :=
  missing10240_10248 ++ missing10248_10256
abbrev records10240_10256 : List Blob :=
  records10240_10248 ++ records10248_10256
theorem aligned10240_10256 :
    AlignedValid 12 4 missing10240_10256 records10240_10256 :=
  aligned10240_10248.append aligned10248_10256

def missing10256_10257 : List (BitVec (edgeCount 12)) :=
  [missing10256]
abbrev records10256_10257 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10256]
theorem aligned10256_10257 :
    AlignedValid 12 4 missing10256_10257 records10256_10257 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10256
    maskCheck10256 AlignedValid.nil

def missing10257_10258 : List (BitVec (edgeCount 12)) :=
  [missing10257]
abbrev records10257_10258 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10257]
theorem aligned10257_10258 :
    AlignedValid 12 4 missing10257_10258 records10257_10258 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10257
    maskCheck10257 AlignedValid.nil

def missing10256_10258 : List (BitVec (edgeCount 12)) :=
  missing10256_10257 ++ missing10257_10258
abbrev records10256_10258 : List Blob :=
  records10256_10257 ++ records10257_10258
theorem aligned10256_10258 :
    AlignedValid 12 4 missing10256_10258 records10256_10258 :=
  aligned10256_10257.append aligned10257_10258

def missing10258_10259 : List (BitVec (edgeCount 12)) :=
  [missing10258]
abbrev records10258_10259 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10258]
theorem aligned10258_10259 :
    AlignedValid 12 4 missing10258_10259 records10258_10259 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10258
    maskCheck10258 AlignedValid.nil

def missing10259_10260 : List (BitVec (edgeCount 12)) :=
  [missing10259]
abbrev records10259_10260 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10259]
theorem aligned10259_10260 :
    AlignedValid 12 4 missing10259_10260 records10259_10260 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10259
    maskCheck10259 AlignedValid.nil

def missing10258_10260 : List (BitVec (edgeCount 12)) :=
  missing10258_10259 ++ missing10259_10260
abbrev records10258_10260 : List Blob :=
  records10258_10259 ++ records10259_10260
theorem aligned10258_10260 :
    AlignedValid 12 4 missing10258_10260 records10258_10260 :=
  aligned10258_10259.append aligned10259_10260

def missing10256_10260 : List (BitVec (edgeCount 12)) :=
  missing10256_10258 ++ missing10258_10260
abbrev records10256_10260 : List Blob :=
  records10256_10258 ++ records10258_10260
theorem aligned10256_10260 :
    AlignedValid 12 4 missing10256_10260 records10256_10260 :=
  aligned10256_10258.append aligned10258_10260

def missing10260_10261 : List (BitVec (edgeCount 12)) :=
  [missing10260]
abbrev records10260_10261 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10260]
theorem aligned10260_10261 :
    AlignedValid 12 4 missing10260_10261 records10260_10261 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10260
    maskCheck10260 AlignedValid.nil

def missing10261_10262 : List (BitVec (edgeCount 12)) :=
  [missing10261]
abbrev records10261_10262 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10261]
theorem aligned10261_10262 :
    AlignedValid 12 4 missing10261_10262 records10261_10262 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10261
    maskCheck10261 AlignedValid.nil

def missing10260_10262 : List (BitVec (edgeCount 12)) :=
  missing10260_10261 ++ missing10261_10262
abbrev records10260_10262 : List Blob :=
  records10260_10261 ++ records10261_10262
theorem aligned10260_10262 :
    AlignedValid 12 4 missing10260_10262 records10260_10262 :=
  aligned10260_10261.append aligned10261_10262

def missing10262_10263 : List (BitVec (edgeCount 12)) :=
  [missing10262]
abbrev records10262_10263 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10262]
theorem aligned10262_10263 :
    AlignedValid 12 4 missing10262_10263 records10262_10263 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10262
    maskCheck10262 AlignedValid.nil

def missing10263_10264 : List (BitVec (edgeCount 12)) :=
  [missing10263]
abbrev records10263_10264 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10263]
theorem aligned10263_10264 :
    AlignedValid 12 4 missing10263_10264 records10263_10264 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10263
    maskCheck10263 AlignedValid.nil

def missing10262_10264 : List (BitVec (edgeCount 12)) :=
  missing10262_10263 ++ missing10263_10264
abbrev records10262_10264 : List Blob :=
  records10262_10263 ++ records10263_10264
theorem aligned10262_10264 :
    AlignedValid 12 4 missing10262_10264 records10262_10264 :=
  aligned10262_10263.append aligned10263_10264

def missing10260_10264 : List (BitVec (edgeCount 12)) :=
  missing10260_10262 ++ missing10262_10264
abbrev records10260_10264 : List Blob :=
  records10260_10262 ++ records10262_10264
theorem aligned10260_10264 :
    AlignedValid 12 4 missing10260_10264 records10260_10264 :=
  aligned10260_10262.append aligned10262_10264

def missing10256_10264 : List (BitVec (edgeCount 12)) :=
  missing10256_10260 ++ missing10260_10264
abbrev records10256_10264 : List Blob :=
  records10256_10260 ++ records10260_10264
theorem aligned10256_10264 :
    AlignedValid 12 4 missing10256_10264 records10256_10264 :=
  aligned10256_10260.append aligned10260_10264

def missing10264_10265 : List (BitVec (edgeCount 12)) :=
  [missing10264]
abbrev records10264_10265 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10264]
theorem aligned10264_10265 :
    AlignedValid 12 4 missing10264_10265 records10264_10265 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10264
    maskCheck10264 AlignedValid.nil

def missing10265_10266 : List (BitVec (edgeCount 12)) :=
  [missing10265]
abbrev records10265_10266 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10265]
theorem aligned10265_10266 :
    AlignedValid 12 4 missing10265_10266 records10265_10266 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10265
    maskCheck10265 AlignedValid.nil

def missing10264_10266 : List (BitVec (edgeCount 12)) :=
  missing10264_10265 ++ missing10265_10266
abbrev records10264_10266 : List Blob :=
  records10264_10265 ++ records10265_10266
theorem aligned10264_10266 :
    AlignedValid 12 4 missing10264_10266 records10264_10266 :=
  aligned10264_10265.append aligned10265_10266

def missing10266_10267 : List (BitVec (edgeCount 12)) :=
  [missing10266]
abbrev records10266_10267 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10266]
theorem aligned10266_10267 :
    AlignedValid 12 4 missing10266_10267 records10266_10267 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10266
    maskCheck10266 AlignedValid.nil

def missing10267_10268 : List (BitVec (edgeCount 12)) :=
  [missing10267]
abbrev records10267_10268 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10267]
theorem aligned10267_10268 :
    AlignedValid 12 4 missing10267_10268 records10267_10268 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10267
    maskCheck10267 AlignedValid.nil

def missing10266_10268 : List (BitVec (edgeCount 12)) :=
  missing10266_10267 ++ missing10267_10268
abbrev records10266_10268 : List Blob :=
  records10266_10267 ++ records10267_10268
theorem aligned10266_10268 :
    AlignedValid 12 4 missing10266_10268 records10266_10268 :=
  aligned10266_10267.append aligned10267_10268

def missing10264_10268 : List (BitVec (edgeCount 12)) :=
  missing10264_10266 ++ missing10266_10268
abbrev records10264_10268 : List Blob :=
  records10264_10266 ++ records10266_10268
theorem aligned10264_10268 :
    AlignedValid 12 4 missing10264_10268 records10264_10268 :=
  aligned10264_10266.append aligned10266_10268

def missing10268_10269 : List (BitVec (edgeCount 12)) :=
  [missing10268]
abbrev records10268_10269 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10268]
theorem aligned10268_10269 :
    AlignedValid 12 4 missing10268_10269 records10268_10269 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10268
    maskCheck10268 AlignedValid.nil

def missing10269_10270 : List (BitVec (edgeCount 12)) :=
  [missing10269]
abbrev records10269_10270 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10269]
theorem aligned10269_10270 :
    AlignedValid 12 4 missing10269_10270 records10269_10270 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10269
    maskCheck10269 AlignedValid.nil

def missing10268_10270 : List (BitVec (edgeCount 12)) :=
  missing10268_10269 ++ missing10269_10270
abbrev records10268_10270 : List Blob :=
  records10268_10269 ++ records10269_10270
theorem aligned10268_10270 :
    AlignedValid 12 4 missing10268_10270 records10268_10270 :=
  aligned10268_10269.append aligned10269_10270

def missing10270_10271 : List (BitVec (edgeCount 12)) :=
  [missing10270]
abbrev records10270_10271 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10270]
theorem aligned10270_10271 :
    AlignedValid 12 4 missing10270_10271 records10270_10271 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10270
    maskCheck10270 AlignedValid.nil

def missing10271_10272 : List (BitVec (edgeCount 12)) :=
  [missing10271]
abbrev records10271_10272 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10271]
theorem aligned10271_10272 :
    AlignedValid 12 4 missing10271_10272 records10271_10272 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10271
    maskCheck10271 AlignedValid.nil

def missing10270_10272 : List (BitVec (edgeCount 12)) :=
  missing10270_10271 ++ missing10271_10272
abbrev records10270_10272 : List Blob :=
  records10270_10271 ++ records10271_10272
theorem aligned10270_10272 :
    AlignedValid 12 4 missing10270_10272 records10270_10272 :=
  aligned10270_10271.append aligned10271_10272

def missing10268_10272 : List (BitVec (edgeCount 12)) :=
  missing10268_10270 ++ missing10270_10272
abbrev records10268_10272 : List Blob :=
  records10268_10270 ++ records10270_10272
theorem aligned10268_10272 :
    AlignedValid 12 4 missing10268_10272 records10268_10272 :=
  aligned10268_10270.append aligned10270_10272

def missing10264_10272 : List (BitVec (edgeCount 12)) :=
  missing10264_10268 ++ missing10268_10272
abbrev records10264_10272 : List Blob :=
  records10264_10268 ++ records10268_10272
theorem aligned10264_10272 :
    AlignedValid 12 4 missing10264_10272 records10264_10272 :=
  aligned10264_10268.append aligned10268_10272

def missing10256_10272 : List (BitVec (edgeCount 12)) :=
  missing10256_10264 ++ missing10264_10272
abbrev records10256_10272 : List Blob :=
  records10256_10264 ++ records10264_10272
theorem aligned10256_10272 :
    AlignedValid 12 4 missing10256_10272 records10256_10272 :=
  aligned10256_10264.append aligned10264_10272

def missing10240_10272 : List (BitVec (edgeCount 12)) :=
  missing10240_10256 ++ missing10256_10272
abbrev records10240_10272 : List Blob :=
  records10240_10256 ++ records10256_10272
theorem aligned10240_10272 :
    AlignedValid 12 4 missing10240_10272 records10240_10272 :=
  aligned10240_10256.append aligned10256_10272

def missing10272_10273 : List (BitVec (edgeCount 12)) :=
  [missing10272]
abbrev records10272_10273 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10272]
theorem aligned10272_10273 :
    AlignedValid 12 4 missing10272_10273 records10272_10273 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10272
    maskCheck10272 AlignedValid.nil

def missing10273_10274 : List (BitVec (edgeCount 12)) :=
  [missing10273]
abbrev records10273_10274 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10273]
theorem aligned10273_10274 :
    AlignedValid 12 4 missing10273_10274 records10273_10274 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10273
    maskCheck10273 AlignedValid.nil

def missing10272_10274 : List (BitVec (edgeCount 12)) :=
  missing10272_10273 ++ missing10273_10274
abbrev records10272_10274 : List Blob :=
  records10272_10273 ++ records10273_10274
theorem aligned10272_10274 :
    AlignedValid 12 4 missing10272_10274 records10272_10274 :=
  aligned10272_10273.append aligned10273_10274

def missing10274_10275 : List (BitVec (edgeCount 12)) :=
  [missing10274]
abbrev records10274_10275 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10274]
theorem aligned10274_10275 :
    AlignedValid 12 4 missing10274_10275 records10274_10275 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10274
    maskCheck10274 AlignedValid.nil

def missing10275_10276 : List (BitVec (edgeCount 12)) :=
  [missing10275]
abbrev records10275_10276 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10275]
theorem aligned10275_10276 :
    AlignedValid 12 4 missing10275_10276 records10275_10276 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10275
    maskCheck10275 AlignedValid.nil

def missing10274_10276 : List (BitVec (edgeCount 12)) :=
  missing10274_10275 ++ missing10275_10276
abbrev records10274_10276 : List Blob :=
  records10274_10275 ++ records10275_10276
theorem aligned10274_10276 :
    AlignedValid 12 4 missing10274_10276 records10274_10276 :=
  aligned10274_10275.append aligned10275_10276

def missing10272_10276 : List (BitVec (edgeCount 12)) :=
  missing10272_10274 ++ missing10274_10276
abbrev records10272_10276 : List Blob :=
  records10272_10274 ++ records10274_10276
theorem aligned10272_10276 :
    AlignedValid 12 4 missing10272_10276 records10272_10276 :=
  aligned10272_10274.append aligned10274_10276

def missing10276_10277 : List (BitVec (edgeCount 12)) :=
  [missing10276]
abbrev records10276_10277 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10276]
theorem aligned10276_10277 :
    AlignedValid 12 4 missing10276_10277 records10276_10277 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10276
    maskCheck10276 AlignedValid.nil

def missing10277_10278 : List (BitVec (edgeCount 12)) :=
  [missing10277]
abbrev records10277_10278 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10277]
theorem aligned10277_10278 :
    AlignedValid 12 4 missing10277_10278 records10277_10278 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10277
    maskCheck10277 AlignedValid.nil

def missing10276_10278 : List (BitVec (edgeCount 12)) :=
  missing10276_10277 ++ missing10277_10278
abbrev records10276_10278 : List Blob :=
  records10276_10277 ++ records10277_10278
theorem aligned10276_10278 :
    AlignedValid 12 4 missing10276_10278 records10276_10278 :=
  aligned10276_10277.append aligned10277_10278

def missing10278_10279 : List (BitVec (edgeCount 12)) :=
  [missing10278]
abbrev records10278_10279 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10278]
theorem aligned10278_10279 :
    AlignedValid 12 4 missing10278_10279 records10278_10279 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10278
    maskCheck10278 AlignedValid.nil

def missing10279_10280 : List (BitVec (edgeCount 12)) :=
  [missing10279]
abbrev records10279_10280 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10279]
theorem aligned10279_10280 :
    AlignedValid 12 4 missing10279_10280 records10279_10280 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10279
    maskCheck10279 AlignedValid.nil

def missing10278_10280 : List (BitVec (edgeCount 12)) :=
  missing10278_10279 ++ missing10279_10280
abbrev records10278_10280 : List Blob :=
  records10278_10279 ++ records10279_10280
theorem aligned10278_10280 :
    AlignedValid 12 4 missing10278_10280 records10278_10280 :=
  aligned10278_10279.append aligned10279_10280

def missing10276_10280 : List (BitVec (edgeCount 12)) :=
  missing10276_10278 ++ missing10278_10280
abbrev records10276_10280 : List Blob :=
  records10276_10278 ++ records10278_10280
theorem aligned10276_10280 :
    AlignedValid 12 4 missing10276_10280 records10276_10280 :=
  aligned10276_10278.append aligned10278_10280

def missing10272_10280 : List (BitVec (edgeCount 12)) :=
  missing10272_10276 ++ missing10276_10280
abbrev records10272_10280 : List Blob :=
  records10272_10276 ++ records10276_10280
theorem aligned10272_10280 :
    AlignedValid 12 4 missing10272_10280 records10272_10280 :=
  aligned10272_10276.append aligned10276_10280

def missing10280_10281 : List (BitVec (edgeCount 12)) :=
  [missing10280]
abbrev records10280_10281 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10280]
theorem aligned10280_10281 :
    AlignedValid 12 4 missing10280_10281 records10280_10281 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10280
    maskCheck10280 AlignedValid.nil

def missing10281_10282 : List (BitVec (edgeCount 12)) :=
  [missing10281]
abbrev records10281_10282 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10281]
theorem aligned10281_10282 :
    AlignedValid 12 4 missing10281_10282 records10281_10282 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10281
    maskCheck10281 AlignedValid.nil

def missing10280_10282 : List (BitVec (edgeCount 12)) :=
  missing10280_10281 ++ missing10281_10282
abbrev records10280_10282 : List Blob :=
  records10280_10281 ++ records10281_10282
theorem aligned10280_10282 :
    AlignedValid 12 4 missing10280_10282 records10280_10282 :=
  aligned10280_10281.append aligned10281_10282

def missing10282_10283 : List (BitVec (edgeCount 12)) :=
  [missing10282]
abbrev records10282_10283 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10282]
theorem aligned10282_10283 :
    AlignedValid 12 4 missing10282_10283 records10282_10283 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10282
    maskCheck10282 AlignedValid.nil

def missing10283_10284 : List (BitVec (edgeCount 12)) :=
  [missing10283]
abbrev records10283_10284 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10283]
theorem aligned10283_10284 :
    AlignedValid 12 4 missing10283_10284 records10283_10284 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10283
    maskCheck10283 AlignedValid.nil

def missing10282_10284 : List (BitVec (edgeCount 12)) :=
  missing10282_10283 ++ missing10283_10284
abbrev records10282_10284 : List Blob :=
  records10282_10283 ++ records10283_10284
theorem aligned10282_10284 :
    AlignedValid 12 4 missing10282_10284 records10282_10284 :=
  aligned10282_10283.append aligned10283_10284

def missing10280_10284 : List (BitVec (edgeCount 12)) :=
  missing10280_10282 ++ missing10282_10284
abbrev records10280_10284 : List Blob :=
  records10280_10282 ++ records10282_10284
theorem aligned10280_10284 :
    AlignedValid 12 4 missing10280_10284 records10280_10284 :=
  aligned10280_10282.append aligned10282_10284

def missing10284_10285 : List (BitVec (edgeCount 12)) :=
  [missing10284]
abbrev records10284_10285 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10284]
theorem aligned10284_10285 :
    AlignedValid 12 4 missing10284_10285 records10284_10285 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10284
    maskCheck10284 AlignedValid.nil

def missing10285_10286 : List (BitVec (edgeCount 12)) :=
  [missing10285]
abbrev records10285_10286 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10285]
theorem aligned10285_10286 :
    AlignedValid 12 4 missing10285_10286 records10285_10286 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10285
    maskCheck10285 AlignedValid.nil

def missing10284_10286 : List (BitVec (edgeCount 12)) :=
  missing10284_10285 ++ missing10285_10286
abbrev records10284_10286 : List Blob :=
  records10284_10285 ++ records10285_10286
theorem aligned10284_10286 :
    AlignedValid 12 4 missing10284_10286 records10284_10286 :=
  aligned10284_10285.append aligned10285_10286

def missing10286_10287 : List (BitVec (edgeCount 12)) :=
  [missing10286]
abbrev records10286_10287 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10286]
theorem aligned10286_10287 :
    AlignedValid 12 4 missing10286_10287 records10286_10287 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10286
    maskCheck10286 AlignedValid.nil

def missing10287_10288 : List (BitVec (edgeCount 12)) :=
  [missing10287]
abbrev records10287_10288 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10287]
theorem aligned10287_10288 :
    AlignedValid 12 4 missing10287_10288 records10287_10288 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10287
    maskCheck10287 AlignedValid.nil

def missing10286_10288 : List (BitVec (edgeCount 12)) :=
  missing10286_10287 ++ missing10287_10288
abbrev records10286_10288 : List Blob :=
  records10286_10287 ++ records10287_10288
theorem aligned10286_10288 :
    AlignedValid 12 4 missing10286_10288 records10286_10288 :=
  aligned10286_10287.append aligned10287_10288

def missing10284_10288 : List (BitVec (edgeCount 12)) :=
  missing10284_10286 ++ missing10286_10288
abbrev records10284_10288 : List Blob :=
  records10284_10286 ++ records10286_10288
theorem aligned10284_10288 :
    AlignedValid 12 4 missing10284_10288 records10284_10288 :=
  aligned10284_10286.append aligned10286_10288

def missing10280_10288 : List (BitVec (edgeCount 12)) :=
  missing10280_10284 ++ missing10284_10288
abbrev records10280_10288 : List Blob :=
  records10280_10284 ++ records10284_10288
theorem aligned10280_10288 :
    AlignedValid 12 4 missing10280_10288 records10280_10288 :=
  aligned10280_10284.append aligned10284_10288

def missing10272_10288 : List (BitVec (edgeCount 12)) :=
  missing10272_10280 ++ missing10280_10288
abbrev records10272_10288 : List Blob :=
  records10272_10280 ++ records10280_10288
theorem aligned10272_10288 :
    AlignedValid 12 4 missing10272_10288 records10272_10288 :=
  aligned10272_10280.append aligned10280_10288

def missing10288_10289 : List (BitVec (edgeCount 12)) :=
  [missing10288]
abbrev records10288_10289 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10288]
theorem aligned10288_10289 :
    AlignedValid 12 4 missing10288_10289 records10288_10289 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10288
    maskCheck10288 AlignedValid.nil

def missing10289_10290 : List (BitVec (edgeCount 12)) :=
  [missing10289]
abbrev records10289_10290 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10289]
theorem aligned10289_10290 :
    AlignedValid 12 4 missing10289_10290 records10289_10290 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10289
    maskCheck10289 AlignedValid.nil

def missing10288_10290 : List (BitVec (edgeCount 12)) :=
  missing10288_10289 ++ missing10289_10290
abbrev records10288_10290 : List Blob :=
  records10288_10289 ++ records10289_10290
theorem aligned10288_10290 :
    AlignedValid 12 4 missing10288_10290 records10288_10290 :=
  aligned10288_10289.append aligned10289_10290

def missing10290_10291 : List (BitVec (edgeCount 12)) :=
  [missing10290]
abbrev records10290_10291 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10290]
theorem aligned10290_10291 :
    AlignedValid 12 4 missing10290_10291 records10290_10291 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10290
    maskCheck10290 AlignedValid.nil

def missing10291_10292 : List (BitVec (edgeCount 12)) :=
  [missing10291]
abbrev records10291_10292 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10291]
theorem aligned10291_10292 :
    AlignedValid 12 4 missing10291_10292 records10291_10292 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10291
    maskCheck10291 AlignedValid.nil

def missing10290_10292 : List (BitVec (edgeCount 12)) :=
  missing10290_10291 ++ missing10291_10292
abbrev records10290_10292 : List Blob :=
  records10290_10291 ++ records10291_10292
theorem aligned10290_10292 :
    AlignedValid 12 4 missing10290_10292 records10290_10292 :=
  aligned10290_10291.append aligned10291_10292

def missing10288_10292 : List (BitVec (edgeCount 12)) :=
  missing10288_10290 ++ missing10290_10292
abbrev records10288_10292 : List Blob :=
  records10288_10290 ++ records10290_10292
theorem aligned10288_10292 :
    AlignedValid 12 4 missing10288_10292 records10288_10292 :=
  aligned10288_10290.append aligned10290_10292

def missing10292_10293 : List (BitVec (edgeCount 12)) :=
  [missing10292]
abbrev records10292_10293 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10292]
theorem aligned10292_10293 :
    AlignedValid 12 4 missing10292_10293 records10292_10293 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10292
    maskCheck10292 AlignedValid.nil

def missing10293_10294 : List (BitVec (edgeCount 12)) :=
  [missing10293]
abbrev records10293_10294 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10293]
theorem aligned10293_10294 :
    AlignedValid 12 4 missing10293_10294 records10293_10294 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10293
    maskCheck10293 AlignedValid.nil

def missing10292_10294 : List (BitVec (edgeCount 12)) :=
  missing10292_10293 ++ missing10293_10294
abbrev records10292_10294 : List Blob :=
  records10292_10293 ++ records10293_10294
theorem aligned10292_10294 :
    AlignedValid 12 4 missing10292_10294 records10292_10294 :=
  aligned10292_10293.append aligned10293_10294

def missing10294_10295 : List (BitVec (edgeCount 12)) :=
  [missing10294]
abbrev records10294_10295 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10294]
theorem aligned10294_10295 :
    AlignedValid 12 4 missing10294_10295 records10294_10295 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10294
    maskCheck10294 AlignedValid.nil

def missing10295_10296 : List (BitVec (edgeCount 12)) :=
  [missing10295]
abbrev records10295_10296 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10295]
theorem aligned10295_10296 :
    AlignedValid 12 4 missing10295_10296 records10295_10296 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10295
    maskCheck10295 AlignedValid.nil

def missing10294_10296 : List (BitVec (edgeCount 12)) :=
  missing10294_10295 ++ missing10295_10296
abbrev records10294_10296 : List Blob :=
  records10294_10295 ++ records10295_10296
theorem aligned10294_10296 :
    AlignedValid 12 4 missing10294_10296 records10294_10296 :=
  aligned10294_10295.append aligned10295_10296

def missing10292_10296 : List (BitVec (edgeCount 12)) :=
  missing10292_10294 ++ missing10294_10296
abbrev records10292_10296 : List Blob :=
  records10292_10294 ++ records10294_10296
theorem aligned10292_10296 :
    AlignedValid 12 4 missing10292_10296 records10292_10296 :=
  aligned10292_10294.append aligned10294_10296

def missing10288_10296 : List (BitVec (edgeCount 12)) :=
  missing10288_10292 ++ missing10292_10296
abbrev records10288_10296 : List Blob :=
  records10288_10292 ++ records10292_10296
theorem aligned10288_10296 :
    AlignedValid 12 4 missing10288_10296 records10288_10296 :=
  aligned10288_10292.append aligned10292_10296

def missing10296_10297 : List (BitVec (edgeCount 12)) :=
  [missing10296]
abbrev records10296_10297 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10296]
theorem aligned10296_10297 :
    AlignedValid 12 4 missing10296_10297 records10296_10297 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10296
    maskCheck10296 AlignedValid.nil

def missing10297_10298 : List (BitVec (edgeCount 12)) :=
  [missing10297]
abbrev records10297_10298 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10297]
theorem aligned10297_10298 :
    AlignedValid 12 4 missing10297_10298 records10297_10298 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10297
    maskCheck10297 AlignedValid.nil

def missing10296_10298 : List (BitVec (edgeCount 12)) :=
  missing10296_10297 ++ missing10297_10298
abbrev records10296_10298 : List Blob :=
  records10296_10297 ++ records10297_10298
theorem aligned10296_10298 :
    AlignedValid 12 4 missing10296_10298 records10296_10298 :=
  aligned10296_10297.append aligned10297_10298

def missing10298_10299 : List (BitVec (edgeCount 12)) :=
  [missing10298]
abbrev records10298_10299 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10298]
theorem aligned10298_10299 :
    AlignedValid 12 4 missing10298_10299 records10298_10299 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10298
    maskCheck10298 AlignedValid.nil

def missing10299_10300 : List (BitVec (edgeCount 12)) :=
  [missing10299]
abbrev records10299_10300 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10299]
theorem aligned10299_10300 :
    AlignedValid 12 4 missing10299_10300 records10299_10300 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10299
    maskCheck10299 AlignedValid.nil

def missing10298_10300 : List (BitVec (edgeCount 12)) :=
  missing10298_10299 ++ missing10299_10300
abbrev records10298_10300 : List Blob :=
  records10298_10299 ++ records10299_10300
theorem aligned10298_10300 :
    AlignedValid 12 4 missing10298_10300 records10298_10300 :=
  aligned10298_10299.append aligned10299_10300

def missing10296_10300 : List (BitVec (edgeCount 12)) :=
  missing10296_10298 ++ missing10298_10300
abbrev records10296_10300 : List Blob :=
  records10296_10298 ++ records10298_10300
theorem aligned10296_10300 :
    AlignedValid 12 4 missing10296_10300 records10296_10300 :=
  aligned10296_10298.append aligned10298_10300

def missing10300_10301 : List (BitVec (edgeCount 12)) :=
  [missing10300]
abbrev records10300_10301 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10300]
theorem aligned10300_10301 :
    AlignedValid 12 4 missing10300_10301 records10300_10301 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10300
    maskCheck10300 AlignedValid.nil

def missing10301_10302 : List (BitVec (edgeCount 12)) :=
  [missing10301]
abbrev records10301_10302 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10301]
theorem aligned10301_10302 :
    AlignedValid 12 4 missing10301_10302 records10301_10302 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10301
    maskCheck10301 AlignedValid.nil

def missing10300_10302 : List (BitVec (edgeCount 12)) :=
  missing10300_10301 ++ missing10301_10302
abbrev records10300_10302 : List Blob :=
  records10300_10301 ++ records10301_10302
theorem aligned10300_10302 :
    AlignedValid 12 4 missing10300_10302 records10300_10302 :=
  aligned10300_10301.append aligned10301_10302

def missing10302_10303 : List (BitVec (edgeCount 12)) :=
  [missing10302]
abbrev records10302_10303 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10302]
theorem aligned10302_10303 :
    AlignedValid 12 4 missing10302_10303 records10302_10303 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10302
    maskCheck10302 AlignedValid.nil

def missing10303_10304 : List (BitVec (edgeCount 12)) :=
  [missing10303]
abbrev records10303_10304 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10303]
theorem aligned10303_10304 :
    AlignedValid 12 4 missing10303_10304 records10303_10304 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10303
    maskCheck10303 AlignedValid.nil

def missing10302_10304 : List (BitVec (edgeCount 12)) :=
  missing10302_10303 ++ missing10303_10304
abbrev records10302_10304 : List Blob :=
  records10302_10303 ++ records10303_10304
theorem aligned10302_10304 :
    AlignedValid 12 4 missing10302_10304 records10302_10304 :=
  aligned10302_10303.append aligned10303_10304

def missing10300_10304 : List (BitVec (edgeCount 12)) :=
  missing10300_10302 ++ missing10302_10304
abbrev records10300_10304 : List Blob :=
  records10300_10302 ++ records10302_10304
theorem aligned10300_10304 :
    AlignedValid 12 4 missing10300_10304 records10300_10304 :=
  aligned10300_10302.append aligned10302_10304

def missing10296_10304 : List (BitVec (edgeCount 12)) :=
  missing10296_10300 ++ missing10300_10304
abbrev records10296_10304 : List Blob :=
  records10296_10300 ++ records10300_10304
theorem aligned10296_10304 :
    AlignedValid 12 4 missing10296_10304 records10296_10304 :=
  aligned10296_10300.append aligned10300_10304

def missing10288_10304 : List (BitVec (edgeCount 12)) :=
  missing10288_10296 ++ missing10296_10304
abbrev records10288_10304 : List Blob :=
  records10288_10296 ++ records10296_10304
theorem aligned10288_10304 :
    AlignedValid 12 4 missing10288_10304 records10288_10304 :=
  aligned10288_10296.append aligned10296_10304

def missing10272_10304 : List (BitVec (edgeCount 12)) :=
  missing10272_10288 ++ missing10288_10304
abbrev records10272_10304 : List Blob :=
  records10272_10288 ++ records10288_10304
theorem aligned10272_10304 :
    AlignedValid 12 4 missing10272_10304 records10272_10304 :=
  aligned10272_10288.append aligned10288_10304

def missing10240_10304 : List (BitVec (edgeCount 12)) :=
  missing10240_10272 ++ missing10272_10304
abbrev records10240_10304 : List Blob :=
  records10240_10272 ++ records10272_10304
theorem aligned10240_10304 :
    AlignedValid 12 4 missing10240_10304 records10240_10304 :=
  aligned10240_10272.append aligned10272_10304

def missing10304_10305 : List (BitVec (edgeCount 12)) :=
  [missing10304]
abbrev records10304_10305 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10304]
theorem aligned10304_10305 :
    AlignedValid 12 4 missing10304_10305 records10304_10305 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10304
    maskCheck10304 AlignedValid.nil

def missing10305_10306 : List (BitVec (edgeCount 12)) :=
  [missing10305]
abbrev records10305_10306 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10305]
theorem aligned10305_10306 :
    AlignedValid 12 4 missing10305_10306 records10305_10306 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10305
    maskCheck10305 AlignedValid.nil

def missing10304_10306 : List (BitVec (edgeCount 12)) :=
  missing10304_10305 ++ missing10305_10306
abbrev records10304_10306 : List Blob :=
  records10304_10305 ++ records10305_10306
theorem aligned10304_10306 :
    AlignedValid 12 4 missing10304_10306 records10304_10306 :=
  aligned10304_10305.append aligned10305_10306

def missing10306_10307 : List (BitVec (edgeCount 12)) :=
  [missing10306]
abbrev records10306_10307 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10306]
theorem aligned10306_10307 :
    AlignedValid 12 4 missing10306_10307 records10306_10307 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10306
    maskCheck10306 AlignedValid.nil

def missing10307_10308 : List (BitVec (edgeCount 12)) :=
  [missing10307]
abbrev records10307_10308 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10307]
theorem aligned10307_10308 :
    AlignedValid 12 4 missing10307_10308 records10307_10308 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10307
    maskCheck10307 AlignedValid.nil

def missing10306_10308 : List (BitVec (edgeCount 12)) :=
  missing10306_10307 ++ missing10307_10308
abbrev records10306_10308 : List Blob :=
  records10306_10307 ++ records10307_10308
theorem aligned10306_10308 :
    AlignedValid 12 4 missing10306_10308 records10306_10308 :=
  aligned10306_10307.append aligned10307_10308

def missing10304_10308 : List (BitVec (edgeCount 12)) :=
  missing10304_10306 ++ missing10306_10308
abbrev records10304_10308 : List Blob :=
  records10304_10306 ++ records10306_10308
theorem aligned10304_10308 :
    AlignedValid 12 4 missing10304_10308 records10304_10308 :=
  aligned10304_10306.append aligned10306_10308

def missing10308_10309 : List (BitVec (edgeCount 12)) :=
  [missing10308]
abbrev records10308_10309 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10308]
theorem aligned10308_10309 :
    AlignedValid 12 4 missing10308_10309 records10308_10309 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10308
    maskCheck10308 AlignedValid.nil

def missing10309_10310 : List (BitVec (edgeCount 12)) :=
  [missing10309]
abbrev records10309_10310 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10309]
theorem aligned10309_10310 :
    AlignedValid 12 4 missing10309_10310 records10309_10310 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10309
    maskCheck10309 AlignedValid.nil

def missing10308_10310 : List (BitVec (edgeCount 12)) :=
  missing10308_10309 ++ missing10309_10310
abbrev records10308_10310 : List Blob :=
  records10308_10309 ++ records10309_10310
theorem aligned10308_10310 :
    AlignedValid 12 4 missing10308_10310 records10308_10310 :=
  aligned10308_10309.append aligned10309_10310

def missing10310_10311 : List (BitVec (edgeCount 12)) :=
  [missing10310]
abbrev records10310_10311 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10310]
theorem aligned10310_10311 :
    AlignedValid 12 4 missing10310_10311 records10310_10311 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10310
    maskCheck10310 AlignedValid.nil

def missing10311_10312 : List (BitVec (edgeCount 12)) :=
  [missing10311]
abbrev records10311_10312 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10311]
theorem aligned10311_10312 :
    AlignedValid 12 4 missing10311_10312 records10311_10312 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10311
    maskCheck10311 AlignedValid.nil

def missing10310_10312 : List (BitVec (edgeCount 12)) :=
  missing10310_10311 ++ missing10311_10312
abbrev records10310_10312 : List Blob :=
  records10310_10311 ++ records10311_10312
theorem aligned10310_10312 :
    AlignedValid 12 4 missing10310_10312 records10310_10312 :=
  aligned10310_10311.append aligned10311_10312

def missing10308_10312 : List (BitVec (edgeCount 12)) :=
  missing10308_10310 ++ missing10310_10312
abbrev records10308_10312 : List Blob :=
  records10308_10310 ++ records10310_10312
theorem aligned10308_10312 :
    AlignedValid 12 4 missing10308_10312 records10308_10312 :=
  aligned10308_10310.append aligned10310_10312

def missing10304_10312 : List (BitVec (edgeCount 12)) :=
  missing10304_10308 ++ missing10308_10312
abbrev records10304_10312 : List Blob :=
  records10304_10308 ++ records10308_10312
theorem aligned10304_10312 :
    AlignedValid 12 4 missing10304_10312 records10304_10312 :=
  aligned10304_10308.append aligned10308_10312

def missing10312_10313 : List (BitVec (edgeCount 12)) :=
  [missing10312]
abbrev records10312_10313 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10312]
theorem aligned10312_10313 :
    AlignedValid 12 4 missing10312_10313 records10312_10313 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10312
    maskCheck10312 AlignedValid.nil

def missing10313_10314 : List (BitVec (edgeCount 12)) :=
  [missing10313]
abbrev records10313_10314 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10313]
theorem aligned10313_10314 :
    AlignedValid 12 4 missing10313_10314 records10313_10314 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10313
    maskCheck10313 AlignedValid.nil

def missing10312_10314 : List (BitVec (edgeCount 12)) :=
  missing10312_10313 ++ missing10313_10314
abbrev records10312_10314 : List Blob :=
  records10312_10313 ++ records10313_10314
theorem aligned10312_10314 :
    AlignedValid 12 4 missing10312_10314 records10312_10314 :=
  aligned10312_10313.append aligned10313_10314

def missing10314_10315 : List (BitVec (edgeCount 12)) :=
  [missing10314]
abbrev records10314_10315 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10314]
theorem aligned10314_10315 :
    AlignedValid 12 4 missing10314_10315 records10314_10315 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10314
    maskCheck10314 AlignedValid.nil

def missing10315_10316 : List (BitVec (edgeCount 12)) :=
  [missing10315]
abbrev records10315_10316 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10315]
theorem aligned10315_10316 :
    AlignedValid 12 4 missing10315_10316 records10315_10316 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10315
    maskCheck10315 AlignedValid.nil

def missing10314_10316 : List (BitVec (edgeCount 12)) :=
  missing10314_10315 ++ missing10315_10316
abbrev records10314_10316 : List Blob :=
  records10314_10315 ++ records10315_10316
theorem aligned10314_10316 :
    AlignedValid 12 4 missing10314_10316 records10314_10316 :=
  aligned10314_10315.append aligned10315_10316

def missing10312_10316 : List (BitVec (edgeCount 12)) :=
  missing10312_10314 ++ missing10314_10316
abbrev records10312_10316 : List Blob :=
  records10312_10314 ++ records10314_10316
theorem aligned10312_10316 :
    AlignedValid 12 4 missing10312_10316 records10312_10316 :=
  aligned10312_10314.append aligned10314_10316

def missing10316_10317 : List (BitVec (edgeCount 12)) :=
  [missing10316]
abbrev records10316_10317 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10316]
theorem aligned10316_10317 :
    AlignedValid 12 4 missing10316_10317 records10316_10317 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10316
    maskCheck10316 AlignedValid.nil

def missing10317_10318 : List (BitVec (edgeCount 12)) :=
  [missing10317]
abbrev records10317_10318 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10317]
theorem aligned10317_10318 :
    AlignedValid 12 4 missing10317_10318 records10317_10318 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10317
    maskCheck10317 AlignedValid.nil

def missing10316_10318 : List (BitVec (edgeCount 12)) :=
  missing10316_10317 ++ missing10317_10318
abbrev records10316_10318 : List Blob :=
  records10316_10317 ++ records10317_10318
theorem aligned10316_10318 :
    AlignedValid 12 4 missing10316_10318 records10316_10318 :=
  aligned10316_10317.append aligned10317_10318

def missing10318_10319 : List (BitVec (edgeCount 12)) :=
  [missing10318]
abbrev records10318_10319 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10318]
theorem aligned10318_10319 :
    AlignedValid 12 4 missing10318_10319 records10318_10319 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10318
    maskCheck10318 AlignedValid.nil

def missing10319_10320 : List (BitVec (edgeCount 12)) :=
  [missing10319]
abbrev records10319_10320 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10319]
theorem aligned10319_10320 :
    AlignedValid 12 4 missing10319_10320 records10319_10320 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10319
    maskCheck10319 AlignedValid.nil

def missing10318_10320 : List (BitVec (edgeCount 12)) :=
  missing10318_10319 ++ missing10319_10320
abbrev records10318_10320 : List Blob :=
  records10318_10319 ++ records10319_10320
theorem aligned10318_10320 :
    AlignedValid 12 4 missing10318_10320 records10318_10320 :=
  aligned10318_10319.append aligned10319_10320

def missing10316_10320 : List (BitVec (edgeCount 12)) :=
  missing10316_10318 ++ missing10318_10320
abbrev records10316_10320 : List Blob :=
  records10316_10318 ++ records10318_10320
theorem aligned10316_10320 :
    AlignedValid 12 4 missing10316_10320 records10316_10320 :=
  aligned10316_10318.append aligned10318_10320

def missing10312_10320 : List (BitVec (edgeCount 12)) :=
  missing10312_10316 ++ missing10316_10320
abbrev records10312_10320 : List Blob :=
  records10312_10316 ++ records10316_10320
theorem aligned10312_10320 :
    AlignedValid 12 4 missing10312_10320 records10312_10320 :=
  aligned10312_10316.append aligned10316_10320

def missing10304_10320 : List (BitVec (edgeCount 12)) :=
  missing10304_10312 ++ missing10312_10320
abbrev records10304_10320 : List Blob :=
  records10304_10312 ++ records10312_10320
theorem aligned10304_10320 :
    AlignedValid 12 4 missing10304_10320 records10304_10320 :=
  aligned10304_10312.append aligned10312_10320

def missing10320_10321 : List (BitVec (edgeCount 12)) :=
  [missing10320]
abbrev records10320_10321 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10320]
theorem aligned10320_10321 :
    AlignedValid 12 4 missing10320_10321 records10320_10321 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10320
    maskCheck10320 AlignedValid.nil

def missing10321_10322 : List (BitVec (edgeCount 12)) :=
  [missing10321]
abbrev records10321_10322 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10321]
theorem aligned10321_10322 :
    AlignedValid 12 4 missing10321_10322 records10321_10322 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10321
    maskCheck10321 AlignedValid.nil

def missing10320_10322 : List (BitVec (edgeCount 12)) :=
  missing10320_10321 ++ missing10321_10322
abbrev records10320_10322 : List Blob :=
  records10320_10321 ++ records10321_10322
theorem aligned10320_10322 :
    AlignedValid 12 4 missing10320_10322 records10320_10322 :=
  aligned10320_10321.append aligned10321_10322

def missing10322_10323 : List (BitVec (edgeCount 12)) :=
  [missing10322]
abbrev records10322_10323 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10322]
theorem aligned10322_10323 :
    AlignedValid 12 4 missing10322_10323 records10322_10323 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10322
    maskCheck10322 AlignedValid.nil

def missing10323_10324 : List (BitVec (edgeCount 12)) :=
  [missing10323]
abbrev records10323_10324 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10323]
theorem aligned10323_10324 :
    AlignedValid 12 4 missing10323_10324 records10323_10324 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10323
    maskCheck10323 AlignedValid.nil

def missing10322_10324 : List (BitVec (edgeCount 12)) :=
  missing10322_10323 ++ missing10323_10324
abbrev records10322_10324 : List Blob :=
  records10322_10323 ++ records10323_10324
theorem aligned10322_10324 :
    AlignedValid 12 4 missing10322_10324 records10322_10324 :=
  aligned10322_10323.append aligned10323_10324

def missing10320_10324 : List (BitVec (edgeCount 12)) :=
  missing10320_10322 ++ missing10322_10324
abbrev records10320_10324 : List Blob :=
  records10320_10322 ++ records10322_10324
theorem aligned10320_10324 :
    AlignedValid 12 4 missing10320_10324 records10320_10324 :=
  aligned10320_10322.append aligned10322_10324

def missing10324_10325 : List (BitVec (edgeCount 12)) :=
  [missing10324]
abbrev records10324_10325 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10324]
theorem aligned10324_10325 :
    AlignedValid 12 4 missing10324_10325 records10324_10325 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10324
    maskCheck10324 AlignedValid.nil

def missing10325_10326 : List (BitVec (edgeCount 12)) :=
  [missing10325]
abbrev records10325_10326 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10325]
theorem aligned10325_10326 :
    AlignedValid 12 4 missing10325_10326 records10325_10326 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10325
    maskCheck10325 AlignedValid.nil

def missing10324_10326 : List (BitVec (edgeCount 12)) :=
  missing10324_10325 ++ missing10325_10326
abbrev records10324_10326 : List Blob :=
  records10324_10325 ++ records10325_10326
theorem aligned10324_10326 :
    AlignedValid 12 4 missing10324_10326 records10324_10326 :=
  aligned10324_10325.append aligned10325_10326

def missing10326_10327 : List (BitVec (edgeCount 12)) :=
  [missing10326]
abbrev records10326_10327 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10326]
theorem aligned10326_10327 :
    AlignedValid 12 4 missing10326_10327 records10326_10327 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10326
    maskCheck10326 AlignedValid.nil

def missing10327_10328 : List (BitVec (edgeCount 12)) :=
  [missing10327]
abbrev records10327_10328 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10327]
theorem aligned10327_10328 :
    AlignedValid 12 4 missing10327_10328 records10327_10328 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10327
    maskCheck10327 AlignedValid.nil

def missing10326_10328 : List (BitVec (edgeCount 12)) :=
  missing10326_10327 ++ missing10327_10328
abbrev records10326_10328 : List Blob :=
  records10326_10327 ++ records10327_10328
theorem aligned10326_10328 :
    AlignedValid 12 4 missing10326_10328 records10326_10328 :=
  aligned10326_10327.append aligned10327_10328

def missing10324_10328 : List (BitVec (edgeCount 12)) :=
  missing10324_10326 ++ missing10326_10328
abbrev records10324_10328 : List Blob :=
  records10324_10326 ++ records10326_10328
theorem aligned10324_10328 :
    AlignedValid 12 4 missing10324_10328 records10324_10328 :=
  aligned10324_10326.append aligned10326_10328

def missing10320_10328 : List (BitVec (edgeCount 12)) :=
  missing10320_10324 ++ missing10324_10328
abbrev records10320_10328 : List Blob :=
  records10320_10324 ++ records10324_10328
theorem aligned10320_10328 :
    AlignedValid 12 4 missing10320_10328 records10320_10328 :=
  aligned10320_10324.append aligned10324_10328

def missing10328_10329 : List (BitVec (edgeCount 12)) :=
  [missing10328]
abbrev records10328_10329 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10328]
theorem aligned10328_10329 :
    AlignedValid 12 4 missing10328_10329 records10328_10329 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10328
    maskCheck10328 AlignedValid.nil

def missing10329_10330 : List (BitVec (edgeCount 12)) :=
  [missing10329]
abbrev records10329_10330 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10329]
theorem aligned10329_10330 :
    AlignedValid 12 4 missing10329_10330 records10329_10330 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10329
    maskCheck10329 AlignedValid.nil

def missing10328_10330 : List (BitVec (edgeCount 12)) :=
  missing10328_10329 ++ missing10329_10330
abbrev records10328_10330 : List Blob :=
  records10328_10329 ++ records10329_10330
theorem aligned10328_10330 :
    AlignedValid 12 4 missing10328_10330 records10328_10330 :=
  aligned10328_10329.append aligned10329_10330

def missing10330_10331 : List (BitVec (edgeCount 12)) :=
  [missing10330]
abbrev records10330_10331 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10330]
theorem aligned10330_10331 :
    AlignedValid 12 4 missing10330_10331 records10330_10331 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10330
    maskCheck10330 AlignedValid.nil

def missing10331_10332 : List (BitVec (edgeCount 12)) :=
  [missing10331]
abbrev records10331_10332 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10331]
theorem aligned10331_10332 :
    AlignedValid 12 4 missing10331_10332 records10331_10332 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10331
    maskCheck10331 AlignedValid.nil

def missing10330_10332 : List (BitVec (edgeCount 12)) :=
  missing10330_10331 ++ missing10331_10332
abbrev records10330_10332 : List Blob :=
  records10330_10331 ++ records10331_10332
theorem aligned10330_10332 :
    AlignedValid 12 4 missing10330_10332 records10330_10332 :=
  aligned10330_10331.append aligned10331_10332

def missing10328_10332 : List (BitVec (edgeCount 12)) :=
  missing10328_10330 ++ missing10330_10332
abbrev records10328_10332 : List Blob :=
  records10328_10330 ++ records10330_10332
theorem aligned10328_10332 :
    AlignedValid 12 4 missing10328_10332 records10328_10332 :=
  aligned10328_10330.append aligned10330_10332

def missing10332_10333 : List (BitVec (edgeCount 12)) :=
  [missing10332]
abbrev records10332_10333 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10332]
theorem aligned10332_10333 :
    AlignedValid 12 4 missing10332_10333 records10332_10333 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10332
    maskCheck10332 AlignedValid.nil

def missing10333_10334 : List (BitVec (edgeCount 12)) :=
  [missing10333]
abbrev records10333_10334 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10333]
theorem aligned10333_10334 :
    AlignedValid 12 4 missing10333_10334 records10333_10334 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10333
    maskCheck10333 AlignedValid.nil

def missing10332_10334 : List (BitVec (edgeCount 12)) :=
  missing10332_10333 ++ missing10333_10334
abbrev records10332_10334 : List Blob :=
  records10332_10333 ++ records10333_10334
theorem aligned10332_10334 :
    AlignedValid 12 4 missing10332_10334 records10332_10334 :=
  aligned10332_10333.append aligned10333_10334

def missing10334_10335 : List (BitVec (edgeCount 12)) :=
  [missing10334]
abbrev records10334_10335 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10334]
theorem aligned10334_10335 :
    AlignedValid 12 4 missing10334_10335 records10334_10335 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10334
    maskCheck10334 AlignedValid.nil

def missing10335_10336 : List (BitVec (edgeCount 12)) :=
  [missing10335]
abbrev records10335_10336 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10335]
theorem aligned10335_10336 :
    AlignedValid 12 4 missing10335_10336 records10335_10336 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10335
    maskCheck10335 AlignedValid.nil

def missing10334_10336 : List (BitVec (edgeCount 12)) :=
  missing10334_10335 ++ missing10335_10336
abbrev records10334_10336 : List Blob :=
  records10334_10335 ++ records10335_10336
theorem aligned10334_10336 :
    AlignedValid 12 4 missing10334_10336 records10334_10336 :=
  aligned10334_10335.append aligned10335_10336

def missing10332_10336 : List (BitVec (edgeCount 12)) :=
  missing10332_10334 ++ missing10334_10336
abbrev records10332_10336 : List Blob :=
  records10332_10334 ++ records10334_10336
theorem aligned10332_10336 :
    AlignedValid 12 4 missing10332_10336 records10332_10336 :=
  aligned10332_10334.append aligned10334_10336

def missing10328_10336 : List (BitVec (edgeCount 12)) :=
  missing10328_10332 ++ missing10332_10336
abbrev records10328_10336 : List Blob :=
  records10328_10332 ++ records10332_10336
theorem aligned10328_10336 :
    AlignedValid 12 4 missing10328_10336 records10328_10336 :=
  aligned10328_10332.append aligned10332_10336

def missing10320_10336 : List (BitVec (edgeCount 12)) :=
  missing10320_10328 ++ missing10328_10336
abbrev records10320_10336 : List Blob :=
  records10320_10328 ++ records10328_10336
theorem aligned10320_10336 :
    AlignedValid 12 4 missing10320_10336 records10320_10336 :=
  aligned10320_10328.append aligned10328_10336

def missing10304_10336 : List (BitVec (edgeCount 12)) :=
  missing10304_10320 ++ missing10320_10336
abbrev records10304_10336 : List Blob :=
  records10304_10320 ++ records10320_10336
theorem aligned10304_10336 :
    AlignedValid 12 4 missing10304_10336 records10304_10336 :=
  aligned10304_10320.append aligned10320_10336

def missing10336_10337 : List (BitVec (edgeCount 12)) :=
  [missing10336]
abbrev records10336_10337 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10336]
theorem aligned10336_10337 :
    AlignedValid 12 4 missing10336_10337 records10336_10337 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10336
    maskCheck10336 AlignedValid.nil

def missing10337_10338 : List (BitVec (edgeCount 12)) :=
  [missing10337]
abbrev records10337_10338 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10337]
theorem aligned10337_10338 :
    AlignedValid 12 4 missing10337_10338 records10337_10338 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10337
    maskCheck10337 AlignedValid.nil

def missing10336_10338 : List (BitVec (edgeCount 12)) :=
  missing10336_10337 ++ missing10337_10338
abbrev records10336_10338 : List Blob :=
  records10336_10337 ++ records10337_10338
theorem aligned10336_10338 :
    AlignedValid 12 4 missing10336_10338 records10336_10338 :=
  aligned10336_10337.append aligned10337_10338

def missing10338_10339 : List (BitVec (edgeCount 12)) :=
  [missing10338]
abbrev records10338_10339 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10338]
theorem aligned10338_10339 :
    AlignedValid 12 4 missing10338_10339 records10338_10339 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10338
    maskCheck10338 AlignedValid.nil

def missing10339_10340 : List (BitVec (edgeCount 12)) :=
  [missing10339]
abbrev records10339_10340 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10339]
theorem aligned10339_10340 :
    AlignedValid 12 4 missing10339_10340 records10339_10340 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10339
    maskCheck10339 AlignedValid.nil

def missing10338_10340 : List (BitVec (edgeCount 12)) :=
  missing10338_10339 ++ missing10339_10340
abbrev records10338_10340 : List Blob :=
  records10338_10339 ++ records10339_10340
theorem aligned10338_10340 :
    AlignedValid 12 4 missing10338_10340 records10338_10340 :=
  aligned10338_10339.append aligned10339_10340

def missing10336_10340 : List (BitVec (edgeCount 12)) :=
  missing10336_10338 ++ missing10338_10340
abbrev records10336_10340 : List Blob :=
  records10336_10338 ++ records10338_10340
theorem aligned10336_10340 :
    AlignedValid 12 4 missing10336_10340 records10336_10340 :=
  aligned10336_10338.append aligned10338_10340

def missing10340_10341 : List (BitVec (edgeCount 12)) :=
  [missing10340]
abbrev records10340_10341 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10340]
theorem aligned10340_10341 :
    AlignedValid 12 4 missing10340_10341 records10340_10341 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10340
    maskCheck10340 AlignedValid.nil

def missing10341_10342 : List (BitVec (edgeCount 12)) :=
  [missing10341]
abbrev records10341_10342 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10341]
theorem aligned10341_10342 :
    AlignedValid 12 4 missing10341_10342 records10341_10342 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10341
    maskCheck10341 AlignedValid.nil

def missing10340_10342 : List (BitVec (edgeCount 12)) :=
  missing10340_10341 ++ missing10341_10342
abbrev records10340_10342 : List Blob :=
  records10340_10341 ++ records10341_10342
theorem aligned10340_10342 :
    AlignedValid 12 4 missing10340_10342 records10340_10342 :=
  aligned10340_10341.append aligned10341_10342

def missing10342_10343 : List (BitVec (edgeCount 12)) :=
  [missing10342]
abbrev records10342_10343 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10342]
theorem aligned10342_10343 :
    AlignedValid 12 4 missing10342_10343 records10342_10343 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10342
    maskCheck10342 AlignedValid.nil

def missing10343_10344 : List (BitVec (edgeCount 12)) :=
  [missing10343]
abbrev records10343_10344 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10343]
theorem aligned10343_10344 :
    AlignedValid 12 4 missing10343_10344 records10343_10344 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10343
    maskCheck10343 AlignedValid.nil

def missing10342_10344 : List (BitVec (edgeCount 12)) :=
  missing10342_10343 ++ missing10343_10344
abbrev records10342_10344 : List Blob :=
  records10342_10343 ++ records10343_10344
theorem aligned10342_10344 :
    AlignedValid 12 4 missing10342_10344 records10342_10344 :=
  aligned10342_10343.append aligned10343_10344

def missing10340_10344 : List (BitVec (edgeCount 12)) :=
  missing10340_10342 ++ missing10342_10344
abbrev records10340_10344 : List Blob :=
  records10340_10342 ++ records10342_10344
theorem aligned10340_10344 :
    AlignedValid 12 4 missing10340_10344 records10340_10344 :=
  aligned10340_10342.append aligned10342_10344

def missing10336_10344 : List (BitVec (edgeCount 12)) :=
  missing10336_10340 ++ missing10340_10344
abbrev records10336_10344 : List Blob :=
  records10336_10340 ++ records10340_10344
theorem aligned10336_10344 :
    AlignedValid 12 4 missing10336_10344 records10336_10344 :=
  aligned10336_10340.append aligned10340_10344

def missing10344_10345 : List (BitVec (edgeCount 12)) :=
  [missing10344]
abbrev records10344_10345 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10344]
theorem aligned10344_10345 :
    AlignedValid 12 4 missing10344_10345 records10344_10345 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10344
    maskCheck10344 AlignedValid.nil

def missing10345_10346 : List (BitVec (edgeCount 12)) :=
  [missing10345]
abbrev records10345_10346 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10345]
theorem aligned10345_10346 :
    AlignedValid 12 4 missing10345_10346 records10345_10346 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10345
    maskCheck10345 AlignedValid.nil

def missing10344_10346 : List (BitVec (edgeCount 12)) :=
  missing10344_10345 ++ missing10345_10346
abbrev records10344_10346 : List Blob :=
  records10344_10345 ++ records10345_10346
theorem aligned10344_10346 :
    AlignedValid 12 4 missing10344_10346 records10344_10346 :=
  aligned10344_10345.append aligned10345_10346

def missing10346_10347 : List (BitVec (edgeCount 12)) :=
  [missing10346]
abbrev records10346_10347 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10346]
theorem aligned10346_10347 :
    AlignedValid 12 4 missing10346_10347 records10346_10347 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10346
    maskCheck10346 AlignedValid.nil

def missing10347_10348 : List (BitVec (edgeCount 12)) :=
  [missing10347]
abbrev records10347_10348 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10347]
theorem aligned10347_10348 :
    AlignedValid 12 4 missing10347_10348 records10347_10348 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10347
    maskCheck10347 AlignedValid.nil

def missing10346_10348 : List (BitVec (edgeCount 12)) :=
  missing10346_10347 ++ missing10347_10348
abbrev records10346_10348 : List Blob :=
  records10346_10347 ++ records10347_10348
theorem aligned10346_10348 :
    AlignedValid 12 4 missing10346_10348 records10346_10348 :=
  aligned10346_10347.append aligned10347_10348

def missing10344_10348 : List (BitVec (edgeCount 12)) :=
  missing10344_10346 ++ missing10346_10348
abbrev records10344_10348 : List Blob :=
  records10344_10346 ++ records10346_10348
theorem aligned10344_10348 :
    AlignedValid 12 4 missing10344_10348 records10344_10348 :=
  aligned10344_10346.append aligned10346_10348

def missing10348_10349 : List (BitVec (edgeCount 12)) :=
  [missing10348]
abbrev records10348_10349 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10348]
theorem aligned10348_10349 :
    AlignedValid 12 4 missing10348_10349 records10348_10349 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10348
    maskCheck10348 AlignedValid.nil

def missing10349_10350 : List (BitVec (edgeCount 12)) :=
  [missing10349]
abbrev records10349_10350 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10349]
theorem aligned10349_10350 :
    AlignedValid 12 4 missing10349_10350 records10349_10350 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10349
    maskCheck10349 AlignedValid.nil

def missing10348_10350 : List (BitVec (edgeCount 12)) :=
  missing10348_10349 ++ missing10349_10350
abbrev records10348_10350 : List Blob :=
  records10348_10349 ++ records10349_10350
theorem aligned10348_10350 :
    AlignedValid 12 4 missing10348_10350 records10348_10350 :=
  aligned10348_10349.append aligned10349_10350

def missing10350_10351 : List (BitVec (edgeCount 12)) :=
  [missing10350]
abbrev records10350_10351 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10350]
theorem aligned10350_10351 :
    AlignedValid 12 4 missing10350_10351 records10350_10351 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10350
    maskCheck10350 AlignedValid.nil

def missing10351_10352 : List (BitVec (edgeCount 12)) :=
  [missing10351]
abbrev records10351_10352 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10351]
theorem aligned10351_10352 :
    AlignedValid 12 4 missing10351_10352 records10351_10352 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10351
    maskCheck10351 AlignedValid.nil

def missing10350_10352 : List (BitVec (edgeCount 12)) :=
  missing10350_10351 ++ missing10351_10352
abbrev records10350_10352 : List Blob :=
  records10350_10351 ++ records10351_10352
theorem aligned10350_10352 :
    AlignedValid 12 4 missing10350_10352 records10350_10352 :=
  aligned10350_10351.append aligned10351_10352

def missing10348_10352 : List (BitVec (edgeCount 12)) :=
  missing10348_10350 ++ missing10350_10352
abbrev records10348_10352 : List Blob :=
  records10348_10350 ++ records10350_10352
theorem aligned10348_10352 :
    AlignedValid 12 4 missing10348_10352 records10348_10352 :=
  aligned10348_10350.append aligned10350_10352

def missing10344_10352 : List (BitVec (edgeCount 12)) :=
  missing10344_10348 ++ missing10348_10352
abbrev records10344_10352 : List Blob :=
  records10344_10348 ++ records10348_10352
theorem aligned10344_10352 :
    AlignedValid 12 4 missing10344_10352 records10344_10352 :=
  aligned10344_10348.append aligned10348_10352

def missing10336_10352 : List (BitVec (edgeCount 12)) :=
  missing10336_10344 ++ missing10344_10352
abbrev records10336_10352 : List Blob :=
  records10336_10344 ++ records10344_10352
theorem aligned10336_10352 :
    AlignedValid 12 4 missing10336_10352 records10336_10352 :=
  aligned10336_10344.append aligned10344_10352

def missing10352_10353 : List (BitVec (edgeCount 12)) :=
  [missing10352]
abbrev records10352_10353 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10352]
theorem aligned10352_10353 :
    AlignedValid 12 4 missing10352_10353 records10352_10353 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10352
    maskCheck10352 AlignedValid.nil

def missing10353_10354 : List (BitVec (edgeCount 12)) :=
  [missing10353]
abbrev records10353_10354 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10353]
theorem aligned10353_10354 :
    AlignedValid 12 4 missing10353_10354 records10353_10354 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10353
    maskCheck10353 AlignedValid.nil

def missing10352_10354 : List (BitVec (edgeCount 12)) :=
  missing10352_10353 ++ missing10353_10354
abbrev records10352_10354 : List Blob :=
  records10352_10353 ++ records10353_10354
theorem aligned10352_10354 :
    AlignedValid 12 4 missing10352_10354 records10352_10354 :=
  aligned10352_10353.append aligned10353_10354

def missing10354_10355 : List (BitVec (edgeCount 12)) :=
  [missing10354]
abbrev records10354_10355 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10354]
theorem aligned10354_10355 :
    AlignedValid 12 4 missing10354_10355 records10354_10355 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10354
    maskCheck10354 AlignedValid.nil

def missing10355_10356 : List (BitVec (edgeCount 12)) :=
  [missing10355]
abbrev records10355_10356 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10355]
theorem aligned10355_10356 :
    AlignedValid 12 4 missing10355_10356 records10355_10356 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10355
    maskCheck10355 AlignedValid.nil

def missing10354_10356 : List (BitVec (edgeCount 12)) :=
  missing10354_10355 ++ missing10355_10356
abbrev records10354_10356 : List Blob :=
  records10354_10355 ++ records10355_10356
theorem aligned10354_10356 :
    AlignedValid 12 4 missing10354_10356 records10354_10356 :=
  aligned10354_10355.append aligned10355_10356

def missing10352_10356 : List (BitVec (edgeCount 12)) :=
  missing10352_10354 ++ missing10354_10356
abbrev records10352_10356 : List Blob :=
  records10352_10354 ++ records10354_10356
theorem aligned10352_10356 :
    AlignedValid 12 4 missing10352_10356 records10352_10356 :=
  aligned10352_10354.append aligned10354_10356

def missing10356_10357 : List (BitVec (edgeCount 12)) :=
  [missing10356]
abbrev records10356_10357 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10356]
theorem aligned10356_10357 :
    AlignedValid 12 4 missing10356_10357 records10356_10357 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10356
    maskCheck10356 AlignedValid.nil

def missing10357_10358 : List (BitVec (edgeCount 12)) :=
  [missing10357]
abbrev records10357_10358 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10357]
theorem aligned10357_10358 :
    AlignedValid 12 4 missing10357_10358 records10357_10358 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10357
    maskCheck10357 AlignedValid.nil

def missing10356_10358 : List (BitVec (edgeCount 12)) :=
  missing10356_10357 ++ missing10357_10358
abbrev records10356_10358 : List Blob :=
  records10356_10357 ++ records10357_10358
theorem aligned10356_10358 :
    AlignedValid 12 4 missing10356_10358 records10356_10358 :=
  aligned10356_10357.append aligned10357_10358

def missing10358_10359 : List (BitVec (edgeCount 12)) :=
  [missing10358]
abbrev records10358_10359 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10358]
theorem aligned10358_10359 :
    AlignedValid 12 4 missing10358_10359 records10358_10359 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10358
    maskCheck10358 AlignedValid.nil

def missing10359_10360 : List (BitVec (edgeCount 12)) :=
  [missing10359]
abbrev records10359_10360 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10359]
theorem aligned10359_10360 :
    AlignedValid 12 4 missing10359_10360 records10359_10360 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10359
    maskCheck10359 AlignedValid.nil

def missing10358_10360 : List (BitVec (edgeCount 12)) :=
  missing10358_10359 ++ missing10359_10360
abbrev records10358_10360 : List Blob :=
  records10358_10359 ++ records10359_10360
theorem aligned10358_10360 :
    AlignedValid 12 4 missing10358_10360 records10358_10360 :=
  aligned10358_10359.append aligned10359_10360

def missing10356_10360 : List (BitVec (edgeCount 12)) :=
  missing10356_10358 ++ missing10358_10360
abbrev records10356_10360 : List Blob :=
  records10356_10358 ++ records10358_10360
theorem aligned10356_10360 :
    AlignedValid 12 4 missing10356_10360 records10356_10360 :=
  aligned10356_10358.append aligned10358_10360

def missing10352_10360 : List (BitVec (edgeCount 12)) :=
  missing10352_10356 ++ missing10356_10360
abbrev records10352_10360 : List Blob :=
  records10352_10356 ++ records10356_10360
theorem aligned10352_10360 :
    AlignedValid 12 4 missing10352_10360 records10352_10360 :=
  aligned10352_10356.append aligned10356_10360

def missing10360_10361 : List (BitVec (edgeCount 12)) :=
  [missing10360]
abbrev records10360_10361 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10360]
theorem aligned10360_10361 :
    AlignedValid 12 4 missing10360_10361 records10360_10361 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10360
    maskCheck10360 AlignedValid.nil

def missing10361_10362 : List (BitVec (edgeCount 12)) :=
  [missing10361]
abbrev records10361_10362 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10361]
theorem aligned10361_10362 :
    AlignedValid 12 4 missing10361_10362 records10361_10362 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10361
    maskCheck10361 AlignedValid.nil

def missing10360_10362 : List (BitVec (edgeCount 12)) :=
  missing10360_10361 ++ missing10361_10362
abbrev records10360_10362 : List Blob :=
  records10360_10361 ++ records10361_10362
theorem aligned10360_10362 :
    AlignedValid 12 4 missing10360_10362 records10360_10362 :=
  aligned10360_10361.append aligned10361_10362

def missing10362_10363 : List (BitVec (edgeCount 12)) :=
  [missing10362]
abbrev records10362_10363 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10362]
theorem aligned10362_10363 :
    AlignedValid 12 4 missing10362_10363 records10362_10363 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10362
    maskCheck10362 AlignedValid.nil

def missing10363_10364 : List (BitVec (edgeCount 12)) :=
  [missing10363]
abbrev records10363_10364 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10363]
theorem aligned10363_10364 :
    AlignedValid 12 4 missing10363_10364 records10363_10364 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10363
    maskCheck10363 AlignedValid.nil

def missing10362_10364 : List (BitVec (edgeCount 12)) :=
  missing10362_10363 ++ missing10363_10364
abbrev records10362_10364 : List Blob :=
  records10362_10363 ++ records10363_10364
theorem aligned10362_10364 :
    AlignedValid 12 4 missing10362_10364 records10362_10364 :=
  aligned10362_10363.append aligned10363_10364

def missing10360_10364 : List (BitVec (edgeCount 12)) :=
  missing10360_10362 ++ missing10362_10364
abbrev records10360_10364 : List Blob :=
  records10360_10362 ++ records10362_10364
theorem aligned10360_10364 :
    AlignedValid 12 4 missing10360_10364 records10360_10364 :=
  aligned10360_10362.append aligned10362_10364

def missing10364_10365 : List (BitVec (edgeCount 12)) :=
  [missing10364]
abbrev records10364_10365 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10364]
theorem aligned10364_10365 :
    AlignedValid 12 4 missing10364_10365 records10364_10365 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10364
    maskCheck10364 AlignedValid.nil

def missing10365_10366 : List (BitVec (edgeCount 12)) :=
  [missing10365]
abbrev records10365_10366 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10365]
theorem aligned10365_10366 :
    AlignedValid 12 4 missing10365_10366 records10365_10366 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10365
    maskCheck10365 AlignedValid.nil

def missing10364_10366 : List (BitVec (edgeCount 12)) :=
  missing10364_10365 ++ missing10365_10366
abbrev records10364_10366 : List Blob :=
  records10364_10365 ++ records10365_10366
theorem aligned10364_10366 :
    AlignedValid 12 4 missing10364_10366 records10364_10366 :=
  aligned10364_10365.append aligned10365_10366

def missing10366_10367 : List (BitVec (edgeCount 12)) :=
  [missing10366]
abbrev records10366_10367 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10366]
theorem aligned10366_10367 :
    AlignedValid 12 4 missing10366_10367 records10366_10367 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10366
    maskCheck10366 AlignedValid.nil

def missing10367_10368 : List (BitVec (edgeCount 12)) :=
  [missing10367]
abbrev records10367_10368 : List Blob :=
  [StrongPackedBucketN12A4Shard080.record10367]
theorem aligned10367_10368 :
    AlignedValid 12 4 missing10367_10368 records10367_10368 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard080.check10367
    maskCheck10367 AlignedValid.nil

def missing10366_10368 : List (BitVec (edgeCount 12)) :=
  missing10366_10367 ++ missing10367_10368
abbrev records10366_10368 : List Blob :=
  records10366_10367 ++ records10367_10368
theorem aligned10366_10368 :
    AlignedValid 12 4 missing10366_10368 records10366_10368 :=
  aligned10366_10367.append aligned10367_10368

def missing10364_10368 : List (BitVec (edgeCount 12)) :=
  missing10364_10366 ++ missing10366_10368
abbrev records10364_10368 : List Blob :=
  records10364_10366 ++ records10366_10368
theorem aligned10364_10368 :
    AlignedValid 12 4 missing10364_10368 records10364_10368 :=
  aligned10364_10366.append aligned10366_10368

def missing10360_10368 : List (BitVec (edgeCount 12)) :=
  missing10360_10364 ++ missing10364_10368
abbrev records10360_10368 : List Blob :=
  records10360_10364 ++ records10364_10368
theorem aligned10360_10368 :
    AlignedValid 12 4 missing10360_10368 records10360_10368 :=
  aligned10360_10364.append aligned10364_10368

def missing10352_10368 : List (BitVec (edgeCount 12)) :=
  missing10352_10360 ++ missing10360_10368
abbrev records10352_10368 : List Blob :=
  records10352_10360 ++ records10360_10368
theorem aligned10352_10368 :
    AlignedValid 12 4 missing10352_10368 records10352_10368 :=
  aligned10352_10360.append aligned10360_10368

def missing10336_10368 : List (BitVec (edgeCount 12)) :=
  missing10336_10352 ++ missing10352_10368
abbrev records10336_10368 : List Blob :=
  records10336_10352 ++ records10352_10368
theorem aligned10336_10368 :
    AlignedValid 12 4 missing10336_10368 records10336_10368 :=
  aligned10336_10352.append aligned10352_10368

def missing10304_10368 : List (BitVec (edgeCount 12)) :=
  missing10304_10336 ++ missing10336_10368
abbrev records10304_10368 : List Blob :=
  records10304_10336 ++ records10336_10368
theorem aligned10304_10368 :
    AlignedValid 12 4 missing10304_10368 records10304_10368 :=
  aligned10304_10336.append aligned10336_10368

def missing10240_10368 : List (BitVec (edgeCount 12)) :=
  missing10240_10304 ++ missing10304_10368
abbrev records10240_10368 : List Blob :=
  records10240_10304 ++ records10304_10368
theorem aligned10240_10368 :
    AlignedValid 12 4 missing10240_10368 records10240_10368 :=
  aligned10240_10304.append aligned10304_10368

abbrev missing : List (BitVec (edgeCount 12)) := missing10240_10368
abbrev records : List Blob := records10240_10368
theorem aligned : AlignedValid 12 4 missing records := aligned10240_10368

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard080
