/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A3Shard010

/-! Decode-only alignment checks for n=12, a=3, records 1280--1407. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard010

open PackedBucketCertificate

def missing1280 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1144019996175761408
theorem maskCheck1280 :
    checkMaskFor missing1280 StrongPackedBucketN12A3Shard010.record1280 = true := by
  decide

def missing1281 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2224883906744680448
theorem maskCheck1281 :
    checkMaskFor missing1281 StrongPackedBucketN12A3Shard010.record1281 = true := by
  decide

def missing1282 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4494698118939410432
theorem maskCheck1282 :
    checkMaskFor missing1282 StrongPackedBucketN12A3Shard010.record1282 = true := by
  decide

def missing1283 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9790931280727113728
theorem maskCheck1283 :
    checkMaskFor missing1283 StrongPackedBucketN12A3Shard010.record1283 = true := by
  decide

def missing1284 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10295334438992609280
theorem maskCheck1284 :
    checkMaskFor missing1284 StrongPackedBucketN12A3Shard010.record1284 = true := by
  decide

def missing1285 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27949444978284953600
theorem maskCheck1285 :
    checkMaskFor missing1285 StrongPackedBucketN12A3Shard010.record1285 = true := by
  decide

def missing1286 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64698817937628200960
theorem maskCheck1286 :
    checkMaskFor missing1286 StrongPackedBucketN12A3Shard010.record1286 = true := by
  decide

def missing1287 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2270025524854128640
theorem maskCheck1287 :
    checkMaskFor missing1287 StrongPackedBucketN12A3Shard010.record1287 = true := by
  decide

def missing1288 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4431753345991966720
theorem maskCheck1288 :
    checkMaskFor missing1288 StrongPackedBucketN12A3Shard010.record1288 = true := by
  decide

def missing1289 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4503810940029894656
theorem maskCheck1289 :
    checkMaskFor missing1289 StrongPackedBucketN12A3Shard010.record1289 = true := by
  decide

def missing1290 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4539839737048858624
theorem maskCheck1290 :
    checkMaskFor missing1290 StrongPackedBucketN12A3Shard010.record1290 = true := by
  decide

def missing1291 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8971381770381426688
theorem maskCheck1291 :
    checkMaskFor missing1291 StrongPackedBucketN12A3Shard010.record1291 = true := by
  decide

def missing1292 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9007410567400390656
theorem maskCheck1292 :
    checkMaskFor missing1292 StrongPackedBucketN12A3Shard010.record1292 = true := by
  decide

def missing1293 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9079468161438318592
theorem maskCheck1293 :
    checkMaskFor missing1293 StrongPackedBucketN12A3Shard010.record1293 = true := by
  decide

def missing1294 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10340476057102057472
theorem maskCheck1294 :
    checkMaskFor missing1294 StrongPackedBucketN12A3Shard010.record1294 = true := by
  decide

def missing1295 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11349282373633048576
theorem maskCheck1295 :
    checkMaskFor missing1295 StrongPackedBucketN12A3Shard010.record1295 = true := by
  decide

def missing1296 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11421339967670976512
theorem maskCheck1296 :
    checkMaskFor missing1296 StrongPackedBucketN12A3Shard010.record1296 = true := by
  decide

def missing1297 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11457368764689940480
theorem maskCheck1297 :
    checkMaskFor missing1297 StrongPackedBucketN12A3Shard010.record1297 = true := by
  decide

def missing1298 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13583067788808814592
theorem maskCheck1298 :
    checkMaskFor missing1298 StrongPackedBucketN12A3Shard010.record1298 = true := by
  decide

def missing1299 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13619096585827778560
theorem maskCheck1299 :
    checkMaskFor missing1299 StrongPackedBucketN12A3Shard010.record1299 = true := by
  decide

def missing1300 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13691154179865706496
theorem maskCheck1300 :
    checkMaskFor missing1300 StrongPackedBucketN12A3Shard010.record1300 = true := by
  decide

def missing1301 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19563848093956833280
theorem maskCheck1301 :
    checkMaskFor missing1301 StrongPackedBucketN12A3Shard010.record1301 = true := by
  decide

def missing1302 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20572654410487824384
theorem maskCheck1302 :
    checkMaskFor missing1302 StrongPackedBucketN12A3Shard010.record1302 = true := by
  decide

def missing1303 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20644712004525752320
theorem maskCheck1303 :
    checkMaskFor missing1303 StrongPackedBucketN12A3Shard010.record1303 = true := by
  decide

def missing1304 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20680740801544716288
theorem maskCheck1304 :
    checkMaskFor missing1304 StrongPackedBucketN12A3Shard010.record1304 = true := by
  decide

def missing1305 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22806439825663590400
theorem maskCheck1305 :
    checkMaskFor missing1305 StrongPackedBucketN12A3Shard010.record1305 = true := by
  decide

def missing1306 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22842468622682554368
theorem maskCheck1306 :
    checkMaskFor missing1306 StrongPackedBucketN12A3Shard010.record1306 = true := by
  decide

def missing1307 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28210759378508185600
theorem maskCheck1307 :
    checkMaskFor missing1307 StrongPackedBucketN12A3Shard010.record1307 = true := by
  decide

def missing1308 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28643104942735753216
theorem maskCheck1308 :
    checkMaskFor missing1308 StrongPackedBucketN12A3Shard010.record1308 = true := by
  decide

def missing1309 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28715162536773681152
theorem maskCheck1309 :
    checkMaskFor missing1309 StrongPackedBucketN12A3Shard010.record1309 = true := by
  decide

def missing1310 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28751191333792645120
theorem maskCheck1310 :
    checkMaskFor missing1310 StrongPackedBucketN12A3Shard010.record1310 = true := by
  decide

def missing1311 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29723968853304672256
theorem maskCheck1311 :
    checkMaskFor missing1311 StrongPackedBucketN12A3Shard010.record1311 = true := by
  decide

def missing1312 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38010592167666384896
theorem maskCheck1312 :
    checkMaskFor missing1312 StrongPackedBucketN12A3Shard010.record1312 = true := by
  decide

def missing1313 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39019398484197376000
theorem maskCheck1313 :
    checkMaskFor missing1313 StrongPackedBucketN12A3Shard010.record1313 = true := by
  decide

def missing1314 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39091456078235303936
theorem maskCheck1314 :
    checkMaskFor missing1314 StrongPackedBucketN12A3Shard010.record1314 = true := by
  decide

def missing1315 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41253183899373142016
theorem maskCheck1315 :
    checkMaskFor missing1315 StrongPackedBucketN12A3Shard010.record1315 = true := by
  decide

def missing1316 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46657503452217737216
theorem maskCheck1316 :
    checkMaskFor missing1316 StrongPackedBucketN12A3Shard010.record1316 = true := by
  decide

def missing1317 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47089849016445304832
theorem maskCheck1317 :
    checkMaskFor missing1317 StrongPackedBucketN12A3Shard010.record1317 = true := by
  decide

def missing1318 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47161906610483232768
theorem maskCheck1318 :
    checkMaskFor missing1318 StrongPackedBucketN12A3Shard010.record1318 = true := by
  decide

def missing1319 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55880875489072513024
theorem maskCheck1319 :
    checkMaskFor missing1319 StrongPackedBucketN12A3Shard010.record1319 = true := by
  decide

def missing1320 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56313221053300080640
theorem maskCheck1320 :
    checkMaskFor missing1320 StrongPackedBucketN12A3Shard010.record1320 = true := by
  decide

def missing1321 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64816017149775577088
theorem maskCheck1321 :
    checkMaskFor missing1321 StrongPackedBucketN12A3Shard010.record1321 = true := by
  decide

def missing1322 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2270236631086661632
theorem maskCheck1322 :
    checkMaskFor missing1322 StrongPackedBucketN12A3Shard010.record1322 = true := by
  decide

def missing1323 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4287849264148643840
theorem maskCheck1323 :
    checkMaskFor missing1323 StrongPackedBucketN12A3Shard010.record1323 = true := by
  decide

def missing1324 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4504022046262427648
theorem maskCheck1324 :
    checkMaskFor missing1324 StrongPackedBucketN12A3Shard010.record1324 = true := by
  decide

def missing1325 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4540050843281391616
theorem maskCheck1325 :
    checkMaskFor missing1325 StrongPackedBucketN12A3Shard010.record1325 = true := by
  decide

def missing1326 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8755420094500175872
theorem maskCheck1326 :
    checkMaskFor missing1326 StrongPackedBucketN12A3Shard010.record1326 = true := by
  decide

def missing1327 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8827477688538103808
theorem maskCheck1327 :
    checkMaskFor missing1327 StrongPackedBucketN12A3Shard010.record1327 = true := by
  decide

def missing1328 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8863506485557067776
theorem maskCheck1328 :
    checkMaskFor missing1328 StrongPackedBucketN12A3Shard010.record1328 = true := by
  decide

def missing1329 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9079679267670851584
theorem maskCheck1329 :
    checkMaskFor missing1329 StrongPackedBucketN12A3Shard010.record1329 = true := by
  decide

def missing1330 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10340687163334590464
theorem maskCheck1330 :
    checkMaskFor missing1330 StrongPackedBucketN12A3Shard010.record1330 = true := by
  decide

def missing1331 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11205378291789725696
theorem maskCheck1331 :
    checkMaskFor missing1331 StrongPackedBucketN12A3Shard010.record1331 = true := by
  decide

def missing1332 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11421551073903509504
theorem maskCheck1332 :
    checkMaskFor missing1332 StrongPackedBucketN12A3Shard010.record1332 = true := by
  decide

def missing1333 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11457579870922473472
theorem maskCheck1333 :
    checkMaskFor missing1333 StrongPackedBucketN12A3Shard010.record1333 = true := by
  decide

def missing1334 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13367106112927563776
theorem maskCheck1334 :
    checkMaskFor missing1334 StrongPackedBucketN12A3Shard010.record1334 = true := by
  decide

def missing1335 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13439163706965491712
theorem maskCheck1335 :
    checkMaskFor missing1335 StrongPackedBucketN12A3Shard010.record1335 = true := by
  decide

def missing1336 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13475192503984455680
theorem maskCheck1336 :
    checkMaskFor missing1336 StrongPackedBucketN12A3Shard010.record1336 = true := by
  decide

def missing1337 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17906734537317023744
theorem maskCheck1337 :
    checkMaskFor missing1337 StrongPackedBucketN12A3Shard010.record1337 = true := by
  decide

def missing1338 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17942763334335987712
theorem maskCheck1338 :
    checkMaskFor missing1338 StrongPackedBucketN12A3Shard010.record1338 = true := by
  decide

def missing1339 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19564059200189366272
theorem maskCheck1339 :
    checkMaskFor missing1339 StrongPackedBucketN12A3Shard010.record1339 = true := by
  decide

def missing1340 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20428750328644501504
theorem maskCheck1340 :
    checkMaskFor missing1340 StrongPackedBucketN12A3Shard010.record1340 = true := by
  decide

def missing1341 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20644923110758285312
theorem maskCheck1341 :
    checkMaskFor missing1341 StrongPackedBucketN12A3Shard010.record1341 = true := by
  decide

def missing1342 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22590478149782339584
theorem maskCheck1342 :
    checkMaskFor missing1342 StrongPackedBucketN12A3Shard010.record1342 = true := by
  decide

def missing1343 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22662535743820267520
theorem maskCheck1343 :
    checkMaskFor missing1343 StrongPackedBucketN12A3Shard010.record1343 = true := by
  decide

def missing1344 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27130106574171799552
theorem maskCheck1344 :
    checkMaskFor missing1344 StrongPackedBucketN12A3Shard010.record1344 = true := by
  decide

def missing1345 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28210970484740718592
theorem maskCheck1345 :
    checkMaskFor missing1345 StrongPackedBucketN12A3Shard010.record1345 = true := by
  decide

def missing1346 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28499200860892430336
theorem maskCheck1346 :
    checkMaskFor missing1346 StrongPackedBucketN12A3Shard010.record1346 = true := by
  decide

def missing1347 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29508007177423421440
theorem maskCheck1347 :
    checkMaskFor missing1347 StrongPackedBucketN12A3Shard010.record1347 = true := by
  decide

def missing1348 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38010803273898917888
theorem maskCheck1348 :
    checkMaskFor missing1348 StrongPackedBucketN12A3Shard010.record1348 = true := by
  decide

def missing1349 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38875494402354053120
theorem maskCheck1349 :
    checkMaskFor missing1349 StrongPackedBucketN12A3Shard010.record1349 = true := by
  decide

def missing1350 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39091667184467836928
theorem maskCheck1350 :
    checkMaskFor missing1350 StrongPackedBucketN12A3Shard010.record1350 = true := by
  decide

def missing1351 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39127695981486800896
theorem maskCheck1351 :
    checkMaskFor missing1351 StrongPackedBucketN12A3Shard010.record1351 = true := by
  decide

def missing1352 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41037222223491891200
theorem maskCheck1352 :
    checkMaskFor missing1352 StrongPackedBucketN12A3Shard010.record1352 = true := by
  decide

def missing1353 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41109279817529819136
theorem maskCheck1353 :
    checkMaskFor missing1353 StrongPackedBucketN12A3Shard010.record1353 = true := by
  decide

def missing1354 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41145308614548783104
theorem maskCheck1354 :
    checkMaskFor missing1354 StrongPackedBucketN12A3Shard010.record1354 = true := by
  decide

def missing1355 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41361481396662566912
theorem maskCheck1355 :
    checkMaskFor missing1355 StrongPackedBucketN12A3Shard010.record1355 = true := by
  decide

def missing1356 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45576850647881351168
theorem maskCheck1356 :
    checkMaskFor missing1356 StrongPackedBucketN12A3Shard010.record1356 = true := by
  decide

def missing1357 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45612879444900315136
theorem maskCheck1357 :
    checkMaskFor missing1357 StrongPackedBucketN12A3Shard010.record1357 = true := by
  decide

def missing1358 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45684937038938243072
theorem maskCheck1358 :
    checkMaskFor missing1358 StrongPackedBucketN12A3Shard010.record1358 = true := by
  decide

def missing1359 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46657714558450270208
theorem maskCheck1359 :
    checkMaskFor missing1359 StrongPackedBucketN12A3Shard010.record1359 = true := by
  decide

def missing1360 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46945944934601981952
theorem maskCheck1360 :
    checkMaskFor missing1360 StrongPackedBucketN12A3Shard010.record1360 = true := by
  decide

def missing1361 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47162117716715765760
theorem maskCheck1361 :
    checkMaskFor missing1361 StrongPackedBucketN12A3Shard010.record1361 = true := by
  decide

def missing1362 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47198146513734729728
theorem maskCheck1362 :
    checkMaskFor missing1362 StrongPackedBucketN12A3Shard010.record1362 = true := by
  decide

def missing1363 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47954751251132973056
theorem maskCheck1363 :
    checkMaskFor missing1363 StrongPackedBucketN12A3Shard010.record1363 = true := by
  decide

def missing1364 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48026808845170900992
theorem maskCheck1364 :
    checkMaskFor missing1364 StrongPackedBucketN12A3Shard010.record1364 = true := by
  decide

def missing1365 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48062837642189864960
theorem maskCheck1365 :
    checkMaskFor missing1365 StrongPackedBucketN12A3Shard010.record1365 = true := by
  decide

def missing1366 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50188536666308739072
theorem maskCheck1366 :
    checkMaskFor missing1366 StrongPackedBucketN12A3Shard010.record1366 = true := by
  decide

def missing1367 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50224565463327703040
theorem maskCheck1367 :
    checkMaskFor missing1367 StrongPackedBucketN12A3Shard010.record1367 = true := by
  decide

def missing1368 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55881086595305046016
theorem maskCheck1368 :
    checkMaskFor missing1368 StrongPackedBucketN12A3Shard010.record1368 = true := by
  decide

def missing1369 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56169316971456757760
theorem maskCheck1369 :
    checkMaskFor missing1369 StrongPackedBucketN12A3Shard010.record1369 = true := by
  decide

def missing1370 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56385489753570541568
theorem maskCheck1370 :
    checkMaskFor missing1370 StrongPackedBucketN12A3Shard010.record1370 = true := by
  decide

def missing1371 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57178123287987748864
theorem maskCheck1371 :
    checkMaskFor missing1371 StrongPackedBucketN12A3Shard010.record1371 = true := by
  decide

def missing1372 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57250180882025676800
theorem maskCheck1372 :
    checkMaskFor missing1372 StrongPackedBucketN12A3Shard010.record1372 = true := by
  decide

def missing1373 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59411908703163514880
theorem maskCheck1373 :
    checkMaskFor missing1373 StrongPackedBucketN12A3Shard010.record1373 = true := by
  decide

def missing1374 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64816228256008110080
theorem maskCheck1374 :
    checkMaskFor missing1374 StrongPackedBucketN12A3Shard010.record1374 = true := by
  decide

def missing1375 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65248573820235677696
theorem maskCheck1375 :
    checkMaskFor missing1375 StrongPackedBucketN12A3Shard010.record1375 = true := by
  decide

def missing1376 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2278891986620514304
theorem maskCheck1376 :
    checkMaskFor missing1376 StrongPackedBucketN12A3Shard010.record1376 = true := by
  decide

def missing1377 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4512677401796280320
theorem maskCheck1377 :
    checkMaskFor missing1377 StrongPackedBucketN12A3Shard010.record1377 = true := by
  decide

def missing1378 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9088334623204704256
theorem maskCheck1378 :
    checkMaskFor missing1378 StrongPackedBucketN12A3Shard010.record1378 = true := by
  decide

def missing1379 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10349342518868443136
theorem maskCheck1379 :
    checkMaskFor missing1379 StrongPackedBucketN12A3Shard010.record1379 = true := by
  decide

def missing1380 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11430206429437362176
theorem maskCheck1380 :
    checkMaskFor missing1380 StrongPackedBucketN12A3Shard010.record1380 = true := by
  decide

def missing1381 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19572714555723218944
theorem maskCheck1381 :
    checkMaskFor missing1381 StrongPackedBucketN12A3Shard010.record1381 = true := by
  decide

def missing1382 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28219625840274571264
theorem maskCheck1382 :
    checkMaskFor missing1382 StrongPackedBucketN12A3Shard010.record1382 = true := by
  decide

def missing1383 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64824883611541962752
theorem maskCheck1383 :
    checkMaskFor missing1383 StrongPackedBucketN12A3Shard010.record1383 = true := by
  decide

def missing1384 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117139204619370496
theorem maskCheck1384 :
    checkMaskFor missing1384 StrongPackedBucketN12A3Shard010.record1384 = true := by
  decide

def missing1385 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2125945521150361600
theorem maskCheck1385 :
    checkMaskFor missing1385 StrongPackedBucketN12A3Shard010.record1385 = true := by
  decide

def missing1386 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2198003115188289536
theorem maskCheck1386 :
    checkMaskFor missing1386 StrongPackedBucketN12A3Shard010.record1386 = true := by
  decide

def missing1387 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2234031912207253504
theorem maskCheck1387 :
    checkMaskFor missing1387 StrongPackedBucketN12A3Shard010.record1387 = true := by
  decide

def missing1388 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4359730936326127616
theorem maskCheck1388 :
    checkMaskFor missing1388 StrongPackedBucketN12A3Shard010.record1388 = true := by
  decide

def missing1389 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4395759733345091584
theorem maskCheck1389 :
    checkMaskFor missing1389 StrongPackedBucketN12A3Shard010.record1389 = true := by
  decide

def missing1390 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4467817327383019520
theorem maskCheck1390 :
    checkMaskFor missing1390 StrongPackedBucketN12A3Shard010.record1390 = true := by
  decide

def missing1391 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8935388157734551552
theorem maskCheck1391 :
    checkMaskFor missing1391 StrongPackedBucketN12A3Shard010.record1391 = true := by
  decide

def missing1392 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9764050489170722816
theorem maskCheck1392 :
    checkMaskFor missing1392 StrongPackedBucketN12A3Shard010.record1392 = true := by
  decide

def missing1393 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10196396053398290432
theorem maskCheck1393 :
    checkMaskFor missing1393 StrongPackedBucketN12A3Shard010.record1393 = true := by
  decide

def missing1394 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10268453647436218368
theorem maskCheck1394 :
    checkMaskFor missing1394 StrongPackedBucketN12A3Shard010.record1394 = true := by
  decide

def missing1395 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10304482444455182336
theorem maskCheck1395 :
    checkMaskFor missing1395 StrongPackedBucketN12A3Shard010.record1395 = true := by
  decide

def missing1396 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11277259963967209472
theorem maskCheck1396 :
    checkMaskFor missing1396 StrongPackedBucketN12A3Shard010.record1396 = true := by
  decide

def missing1397 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11313288760986173440
theorem maskCheck1397 :
    checkMaskFor missing1397 StrongPackedBucketN12A3Shard010.record1397 = true := by
  decide

def missing1398 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11385346355024101376
theorem maskCheck1398 :
    checkMaskFor missing1398 StrongPackedBucketN12A3Shard010.record1398 = true := by
  decide

def missing1399 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18987422526025498624
theorem maskCheck1399 :
    checkMaskFor missing1399 StrongPackedBucketN12A3Shard010.record1399 = true := by
  decide

def missing1400 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19419768090253066240
theorem maskCheck1400 :
    checkMaskFor missing1400 StrongPackedBucketN12A3Shard010.record1400 = true := by
  decide

def missing1401 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19491825684290994176
theorem maskCheck1401 :
    checkMaskFor missing1401 StrongPackedBucketN12A3Shard010.record1401 = true := by
  decide

def missing1402 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19527854481309958144
theorem maskCheck1402 :
    checkMaskFor missing1402 StrongPackedBucketN12A3Shard010.record1402 = true := by
  decide

def missing1403 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20500632000821985280
theorem maskCheck1403 :
    checkMaskFor missing1403 StrongPackedBucketN12A3Shard010.record1403 = true := by
  decide

def missing1404 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20536660797840949248
theorem maskCheck1404 :
    checkMaskFor missing1404 StrongPackedBucketN12A3Shard010.record1404 = true := by
  decide

def missing1405 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27922564186728562688
theorem maskCheck1405 :
    checkMaskFor missing1405 StrongPackedBucketN12A3Shard010.record1405 = true := by
  decide

def missing1406 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28066679374804418560
theorem maskCheck1406 :
    checkMaskFor missing1406 StrongPackedBucketN12A3Shard010.record1406 = true := by
  decide

def missing1407 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28138736968842346496
theorem maskCheck1407 :
    checkMaskFor missing1407 StrongPackedBucketN12A3Shard010.record1407 = true := by
  decide

def missing1280_1281 : List (BitVec (edgeCount 12)) :=
  [missing1280]
abbrev records1280_1281 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1280]
theorem aligned1280_1281 :
    AlignedValid 12 3 missing1280_1281 records1280_1281 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1280
    maskCheck1280 AlignedValid.nil

def missing1281_1282 : List (BitVec (edgeCount 12)) :=
  [missing1281]
abbrev records1281_1282 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1281]
theorem aligned1281_1282 :
    AlignedValid 12 3 missing1281_1282 records1281_1282 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1281
    maskCheck1281 AlignedValid.nil

def missing1280_1282 : List (BitVec (edgeCount 12)) :=
  missing1280_1281 ++ missing1281_1282
abbrev records1280_1282 : List Blob :=
  records1280_1281 ++ records1281_1282
theorem aligned1280_1282 :
    AlignedValid 12 3 missing1280_1282 records1280_1282 :=
  aligned1280_1281.append aligned1281_1282

def missing1282_1283 : List (BitVec (edgeCount 12)) :=
  [missing1282]
abbrev records1282_1283 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1282]
theorem aligned1282_1283 :
    AlignedValid 12 3 missing1282_1283 records1282_1283 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1282
    maskCheck1282 AlignedValid.nil

def missing1283_1284 : List (BitVec (edgeCount 12)) :=
  [missing1283]
abbrev records1283_1284 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1283]
theorem aligned1283_1284 :
    AlignedValid 12 3 missing1283_1284 records1283_1284 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1283
    maskCheck1283 AlignedValid.nil

def missing1282_1284 : List (BitVec (edgeCount 12)) :=
  missing1282_1283 ++ missing1283_1284
abbrev records1282_1284 : List Blob :=
  records1282_1283 ++ records1283_1284
theorem aligned1282_1284 :
    AlignedValid 12 3 missing1282_1284 records1282_1284 :=
  aligned1282_1283.append aligned1283_1284

def missing1280_1284 : List (BitVec (edgeCount 12)) :=
  missing1280_1282 ++ missing1282_1284
abbrev records1280_1284 : List Blob :=
  records1280_1282 ++ records1282_1284
theorem aligned1280_1284 :
    AlignedValid 12 3 missing1280_1284 records1280_1284 :=
  aligned1280_1282.append aligned1282_1284

def missing1284_1285 : List (BitVec (edgeCount 12)) :=
  [missing1284]
abbrev records1284_1285 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1284]
theorem aligned1284_1285 :
    AlignedValid 12 3 missing1284_1285 records1284_1285 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1284
    maskCheck1284 AlignedValid.nil

def missing1285_1286 : List (BitVec (edgeCount 12)) :=
  [missing1285]
abbrev records1285_1286 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1285]
theorem aligned1285_1286 :
    AlignedValid 12 3 missing1285_1286 records1285_1286 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1285
    maskCheck1285 AlignedValid.nil

def missing1284_1286 : List (BitVec (edgeCount 12)) :=
  missing1284_1285 ++ missing1285_1286
abbrev records1284_1286 : List Blob :=
  records1284_1285 ++ records1285_1286
theorem aligned1284_1286 :
    AlignedValid 12 3 missing1284_1286 records1284_1286 :=
  aligned1284_1285.append aligned1285_1286

def missing1286_1287 : List (BitVec (edgeCount 12)) :=
  [missing1286]
abbrev records1286_1287 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1286]
theorem aligned1286_1287 :
    AlignedValid 12 3 missing1286_1287 records1286_1287 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1286
    maskCheck1286 AlignedValid.nil

def missing1287_1288 : List (BitVec (edgeCount 12)) :=
  [missing1287]
abbrev records1287_1288 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1287]
theorem aligned1287_1288 :
    AlignedValid 12 3 missing1287_1288 records1287_1288 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1287
    maskCheck1287 AlignedValid.nil

def missing1286_1288 : List (BitVec (edgeCount 12)) :=
  missing1286_1287 ++ missing1287_1288
abbrev records1286_1288 : List Blob :=
  records1286_1287 ++ records1287_1288
theorem aligned1286_1288 :
    AlignedValid 12 3 missing1286_1288 records1286_1288 :=
  aligned1286_1287.append aligned1287_1288

def missing1284_1288 : List (BitVec (edgeCount 12)) :=
  missing1284_1286 ++ missing1286_1288
abbrev records1284_1288 : List Blob :=
  records1284_1286 ++ records1286_1288
theorem aligned1284_1288 :
    AlignedValid 12 3 missing1284_1288 records1284_1288 :=
  aligned1284_1286.append aligned1286_1288

def missing1280_1288 : List (BitVec (edgeCount 12)) :=
  missing1280_1284 ++ missing1284_1288
abbrev records1280_1288 : List Blob :=
  records1280_1284 ++ records1284_1288
theorem aligned1280_1288 :
    AlignedValid 12 3 missing1280_1288 records1280_1288 :=
  aligned1280_1284.append aligned1284_1288

def missing1288_1289 : List (BitVec (edgeCount 12)) :=
  [missing1288]
abbrev records1288_1289 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1288]
theorem aligned1288_1289 :
    AlignedValid 12 3 missing1288_1289 records1288_1289 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1288
    maskCheck1288 AlignedValid.nil

def missing1289_1290 : List (BitVec (edgeCount 12)) :=
  [missing1289]
abbrev records1289_1290 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1289]
theorem aligned1289_1290 :
    AlignedValid 12 3 missing1289_1290 records1289_1290 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1289
    maskCheck1289 AlignedValid.nil

def missing1288_1290 : List (BitVec (edgeCount 12)) :=
  missing1288_1289 ++ missing1289_1290
abbrev records1288_1290 : List Blob :=
  records1288_1289 ++ records1289_1290
theorem aligned1288_1290 :
    AlignedValid 12 3 missing1288_1290 records1288_1290 :=
  aligned1288_1289.append aligned1289_1290

def missing1290_1291 : List (BitVec (edgeCount 12)) :=
  [missing1290]
abbrev records1290_1291 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1290]
theorem aligned1290_1291 :
    AlignedValid 12 3 missing1290_1291 records1290_1291 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1290
    maskCheck1290 AlignedValid.nil

def missing1291_1292 : List (BitVec (edgeCount 12)) :=
  [missing1291]
abbrev records1291_1292 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1291]
theorem aligned1291_1292 :
    AlignedValid 12 3 missing1291_1292 records1291_1292 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1291
    maskCheck1291 AlignedValid.nil

def missing1290_1292 : List (BitVec (edgeCount 12)) :=
  missing1290_1291 ++ missing1291_1292
abbrev records1290_1292 : List Blob :=
  records1290_1291 ++ records1291_1292
theorem aligned1290_1292 :
    AlignedValid 12 3 missing1290_1292 records1290_1292 :=
  aligned1290_1291.append aligned1291_1292

def missing1288_1292 : List (BitVec (edgeCount 12)) :=
  missing1288_1290 ++ missing1290_1292
abbrev records1288_1292 : List Blob :=
  records1288_1290 ++ records1290_1292
theorem aligned1288_1292 :
    AlignedValid 12 3 missing1288_1292 records1288_1292 :=
  aligned1288_1290.append aligned1290_1292

def missing1292_1293 : List (BitVec (edgeCount 12)) :=
  [missing1292]
abbrev records1292_1293 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1292]
theorem aligned1292_1293 :
    AlignedValid 12 3 missing1292_1293 records1292_1293 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1292
    maskCheck1292 AlignedValid.nil

def missing1293_1294 : List (BitVec (edgeCount 12)) :=
  [missing1293]
abbrev records1293_1294 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1293]
theorem aligned1293_1294 :
    AlignedValid 12 3 missing1293_1294 records1293_1294 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1293
    maskCheck1293 AlignedValid.nil

def missing1292_1294 : List (BitVec (edgeCount 12)) :=
  missing1292_1293 ++ missing1293_1294
abbrev records1292_1294 : List Blob :=
  records1292_1293 ++ records1293_1294
theorem aligned1292_1294 :
    AlignedValid 12 3 missing1292_1294 records1292_1294 :=
  aligned1292_1293.append aligned1293_1294

def missing1294_1295 : List (BitVec (edgeCount 12)) :=
  [missing1294]
abbrev records1294_1295 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1294]
theorem aligned1294_1295 :
    AlignedValid 12 3 missing1294_1295 records1294_1295 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1294
    maskCheck1294 AlignedValid.nil

def missing1295_1296 : List (BitVec (edgeCount 12)) :=
  [missing1295]
abbrev records1295_1296 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1295]
theorem aligned1295_1296 :
    AlignedValid 12 3 missing1295_1296 records1295_1296 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1295
    maskCheck1295 AlignedValid.nil

def missing1294_1296 : List (BitVec (edgeCount 12)) :=
  missing1294_1295 ++ missing1295_1296
abbrev records1294_1296 : List Blob :=
  records1294_1295 ++ records1295_1296
theorem aligned1294_1296 :
    AlignedValid 12 3 missing1294_1296 records1294_1296 :=
  aligned1294_1295.append aligned1295_1296

def missing1292_1296 : List (BitVec (edgeCount 12)) :=
  missing1292_1294 ++ missing1294_1296
abbrev records1292_1296 : List Blob :=
  records1292_1294 ++ records1294_1296
theorem aligned1292_1296 :
    AlignedValid 12 3 missing1292_1296 records1292_1296 :=
  aligned1292_1294.append aligned1294_1296

def missing1288_1296 : List (BitVec (edgeCount 12)) :=
  missing1288_1292 ++ missing1292_1296
abbrev records1288_1296 : List Blob :=
  records1288_1292 ++ records1292_1296
theorem aligned1288_1296 :
    AlignedValid 12 3 missing1288_1296 records1288_1296 :=
  aligned1288_1292.append aligned1292_1296

def missing1280_1296 : List (BitVec (edgeCount 12)) :=
  missing1280_1288 ++ missing1288_1296
abbrev records1280_1296 : List Blob :=
  records1280_1288 ++ records1288_1296
theorem aligned1280_1296 :
    AlignedValid 12 3 missing1280_1296 records1280_1296 :=
  aligned1280_1288.append aligned1288_1296

def missing1296_1297 : List (BitVec (edgeCount 12)) :=
  [missing1296]
abbrev records1296_1297 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1296]
theorem aligned1296_1297 :
    AlignedValid 12 3 missing1296_1297 records1296_1297 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1296
    maskCheck1296 AlignedValid.nil

def missing1297_1298 : List (BitVec (edgeCount 12)) :=
  [missing1297]
abbrev records1297_1298 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1297]
theorem aligned1297_1298 :
    AlignedValid 12 3 missing1297_1298 records1297_1298 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1297
    maskCheck1297 AlignedValid.nil

def missing1296_1298 : List (BitVec (edgeCount 12)) :=
  missing1296_1297 ++ missing1297_1298
abbrev records1296_1298 : List Blob :=
  records1296_1297 ++ records1297_1298
theorem aligned1296_1298 :
    AlignedValid 12 3 missing1296_1298 records1296_1298 :=
  aligned1296_1297.append aligned1297_1298

def missing1298_1299 : List (BitVec (edgeCount 12)) :=
  [missing1298]
abbrev records1298_1299 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1298]
theorem aligned1298_1299 :
    AlignedValid 12 3 missing1298_1299 records1298_1299 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1298
    maskCheck1298 AlignedValid.nil

def missing1299_1300 : List (BitVec (edgeCount 12)) :=
  [missing1299]
abbrev records1299_1300 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1299]
theorem aligned1299_1300 :
    AlignedValid 12 3 missing1299_1300 records1299_1300 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1299
    maskCheck1299 AlignedValid.nil

def missing1298_1300 : List (BitVec (edgeCount 12)) :=
  missing1298_1299 ++ missing1299_1300
abbrev records1298_1300 : List Blob :=
  records1298_1299 ++ records1299_1300
theorem aligned1298_1300 :
    AlignedValid 12 3 missing1298_1300 records1298_1300 :=
  aligned1298_1299.append aligned1299_1300

def missing1296_1300 : List (BitVec (edgeCount 12)) :=
  missing1296_1298 ++ missing1298_1300
abbrev records1296_1300 : List Blob :=
  records1296_1298 ++ records1298_1300
theorem aligned1296_1300 :
    AlignedValid 12 3 missing1296_1300 records1296_1300 :=
  aligned1296_1298.append aligned1298_1300

def missing1300_1301 : List (BitVec (edgeCount 12)) :=
  [missing1300]
abbrev records1300_1301 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1300]
theorem aligned1300_1301 :
    AlignedValid 12 3 missing1300_1301 records1300_1301 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1300
    maskCheck1300 AlignedValid.nil

def missing1301_1302 : List (BitVec (edgeCount 12)) :=
  [missing1301]
abbrev records1301_1302 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1301]
theorem aligned1301_1302 :
    AlignedValid 12 3 missing1301_1302 records1301_1302 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1301
    maskCheck1301 AlignedValid.nil

def missing1300_1302 : List (BitVec (edgeCount 12)) :=
  missing1300_1301 ++ missing1301_1302
abbrev records1300_1302 : List Blob :=
  records1300_1301 ++ records1301_1302
theorem aligned1300_1302 :
    AlignedValid 12 3 missing1300_1302 records1300_1302 :=
  aligned1300_1301.append aligned1301_1302

def missing1302_1303 : List (BitVec (edgeCount 12)) :=
  [missing1302]
abbrev records1302_1303 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1302]
theorem aligned1302_1303 :
    AlignedValid 12 3 missing1302_1303 records1302_1303 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1302
    maskCheck1302 AlignedValid.nil

def missing1303_1304 : List (BitVec (edgeCount 12)) :=
  [missing1303]
abbrev records1303_1304 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1303]
theorem aligned1303_1304 :
    AlignedValid 12 3 missing1303_1304 records1303_1304 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1303
    maskCheck1303 AlignedValid.nil

def missing1302_1304 : List (BitVec (edgeCount 12)) :=
  missing1302_1303 ++ missing1303_1304
abbrev records1302_1304 : List Blob :=
  records1302_1303 ++ records1303_1304
theorem aligned1302_1304 :
    AlignedValid 12 3 missing1302_1304 records1302_1304 :=
  aligned1302_1303.append aligned1303_1304

def missing1300_1304 : List (BitVec (edgeCount 12)) :=
  missing1300_1302 ++ missing1302_1304
abbrev records1300_1304 : List Blob :=
  records1300_1302 ++ records1302_1304
theorem aligned1300_1304 :
    AlignedValid 12 3 missing1300_1304 records1300_1304 :=
  aligned1300_1302.append aligned1302_1304

def missing1296_1304 : List (BitVec (edgeCount 12)) :=
  missing1296_1300 ++ missing1300_1304
abbrev records1296_1304 : List Blob :=
  records1296_1300 ++ records1300_1304
theorem aligned1296_1304 :
    AlignedValid 12 3 missing1296_1304 records1296_1304 :=
  aligned1296_1300.append aligned1300_1304

def missing1304_1305 : List (BitVec (edgeCount 12)) :=
  [missing1304]
abbrev records1304_1305 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1304]
theorem aligned1304_1305 :
    AlignedValid 12 3 missing1304_1305 records1304_1305 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1304
    maskCheck1304 AlignedValid.nil

def missing1305_1306 : List (BitVec (edgeCount 12)) :=
  [missing1305]
abbrev records1305_1306 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1305]
theorem aligned1305_1306 :
    AlignedValid 12 3 missing1305_1306 records1305_1306 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1305
    maskCheck1305 AlignedValid.nil

def missing1304_1306 : List (BitVec (edgeCount 12)) :=
  missing1304_1305 ++ missing1305_1306
abbrev records1304_1306 : List Blob :=
  records1304_1305 ++ records1305_1306
theorem aligned1304_1306 :
    AlignedValid 12 3 missing1304_1306 records1304_1306 :=
  aligned1304_1305.append aligned1305_1306

def missing1306_1307 : List (BitVec (edgeCount 12)) :=
  [missing1306]
abbrev records1306_1307 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1306]
theorem aligned1306_1307 :
    AlignedValid 12 3 missing1306_1307 records1306_1307 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1306
    maskCheck1306 AlignedValid.nil

def missing1307_1308 : List (BitVec (edgeCount 12)) :=
  [missing1307]
abbrev records1307_1308 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1307]
theorem aligned1307_1308 :
    AlignedValid 12 3 missing1307_1308 records1307_1308 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1307
    maskCheck1307 AlignedValid.nil

def missing1306_1308 : List (BitVec (edgeCount 12)) :=
  missing1306_1307 ++ missing1307_1308
abbrev records1306_1308 : List Blob :=
  records1306_1307 ++ records1307_1308
theorem aligned1306_1308 :
    AlignedValid 12 3 missing1306_1308 records1306_1308 :=
  aligned1306_1307.append aligned1307_1308

def missing1304_1308 : List (BitVec (edgeCount 12)) :=
  missing1304_1306 ++ missing1306_1308
abbrev records1304_1308 : List Blob :=
  records1304_1306 ++ records1306_1308
theorem aligned1304_1308 :
    AlignedValid 12 3 missing1304_1308 records1304_1308 :=
  aligned1304_1306.append aligned1306_1308

def missing1308_1309 : List (BitVec (edgeCount 12)) :=
  [missing1308]
abbrev records1308_1309 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1308]
theorem aligned1308_1309 :
    AlignedValid 12 3 missing1308_1309 records1308_1309 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1308
    maskCheck1308 AlignedValid.nil

def missing1309_1310 : List (BitVec (edgeCount 12)) :=
  [missing1309]
abbrev records1309_1310 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1309]
theorem aligned1309_1310 :
    AlignedValid 12 3 missing1309_1310 records1309_1310 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1309
    maskCheck1309 AlignedValid.nil

def missing1308_1310 : List (BitVec (edgeCount 12)) :=
  missing1308_1309 ++ missing1309_1310
abbrev records1308_1310 : List Blob :=
  records1308_1309 ++ records1309_1310
theorem aligned1308_1310 :
    AlignedValid 12 3 missing1308_1310 records1308_1310 :=
  aligned1308_1309.append aligned1309_1310

def missing1310_1311 : List (BitVec (edgeCount 12)) :=
  [missing1310]
abbrev records1310_1311 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1310]
theorem aligned1310_1311 :
    AlignedValid 12 3 missing1310_1311 records1310_1311 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1310
    maskCheck1310 AlignedValid.nil

def missing1311_1312 : List (BitVec (edgeCount 12)) :=
  [missing1311]
abbrev records1311_1312 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1311]
theorem aligned1311_1312 :
    AlignedValid 12 3 missing1311_1312 records1311_1312 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1311
    maskCheck1311 AlignedValid.nil

def missing1310_1312 : List (BitVec (edgeCount 12)) :=
  missing1310_1311 ++ missing1311_1312
abbrev records1310_1312 : List Blob :=
  records1310_1311 ++ records1311_1312
theorem aligned1310_1312 :
    AlignedValid 12 3 missing1310_1312 records1310_1312 :=
  aligned1310_1311.append aligned1311_1312

def missing1308_1312 : List (BitVec (edgeCount 12)) :=
  missing1308_1310 ++ missing1310_1312
abbrev records1308_1312 : List Blob :=
  records1308_1310 ++ records1310_1312
theorem aligned1308_1312 :
    AlignedValid 12 3 missing1308_1312 records1308_1312 :=
  aligned1308_1310.append aligned1310_1312

def missing1304_1312 : List (BitVec (edgeCount 12)) :=
  missing1304_1308 ++ missing1308_1312
abbrev records1304_1312 : List Blob :=
  records1304_1308 ++ records1308_1312
theorem aligned1304_1312 :
    AlignedValid 12 3 missing1304_1312 records1304_1312 :=
  aligned1304_1308.append aligned1308_1312

def missing1296_1312 : List (BitVec (edgeCount 12)) :=
  missing1296_1304 ++ missing1304_1312
abbrev records1296_1312 : List Blob :=
  records1296_1304 ++ records1304_1312
theorem aligned1296_1312 :
    AlignedValid 12 3 missing1296_1312 records1296_1312 :=
  aligned1296_1304.append aligned1304_1312

def missing1280_1312 : List (BitVec (edgeCount 12)) :=
  missing1280_1296 ++ missing1296_1312
abbrev records1280_1312 : List Blob :=
  records1280_1296 ++ records1296_1312
theorem aligned1280_1312 :
    AlignedValid 12 3 missing1280_1312 records1280_1312 :=
  aligned1280_1296.append aligned1296_1312

def missing1312_1313 : List (BitVec (edgeCount 12)) :=
  [missing1312]
abbrev records1312_1313 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1312]
theorem aligned1312_1313 :
    AlignedValid 12 3 missing1312_1313 records1312_1313 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1312
    maskCheck1312 AlignedValid.nil

def missing1313_1314 : List (BitVec (edgeCount 12)) :=
  [missing1313]
abbrev records1313_1314 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1313]
theorem aligned1313_1314 :
    AlignedValid 12 3 missing1313_1314 records1313_1314 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1313
    maskCheck1313 AlignedValid.nil

def missing1312_1314 : List (BitVec (edgeCount 12)) :=
  missing1312_1313 ++ missing1313_1314
abbrev records1312_1314 : List Blob :=
  records1312_1313 ++ records1313_1314
theorem aligned1312_1314 :
    AlignedValid 12 3 missing1312_1314 records1312_1314 :=
  aligned1312_1313.append aligned1313_1314

def missing1314_1315 : List (BitVec (edgeCount 12)) :=
  [missing1314]
abbrev records1314_1315 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1314]
theorem aligned1314_1315 :
    AlignedValid 12 3 missing1314_1315 records1314_1315 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1314
    maskCheck1314 AlignedValid.nil

def missing1315_1316 : List (BitVec (edgeCount 12)) :=
  [missing1315]
abbrev records1315_1316 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1315]
theorem aligned1315_1316 :
    AlignedValid 12 3 missing1315_1316 records1315_1316 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1315
    maskCheck1315 AlignedValid.nil

def missing1314_1316 : List (BitVec (edgeCount 12)) :=
  missing1314_1315 ++ missing1315_1316
abbrev records1314_1316 : List Blob :=
  records1314_1315 ++ records1315_1316
theorem aligned1314_1316 :
    AlignedValid 12 3 missing1314_1316 records1314_1316 :=
  aligned1314_1315.append aligned1315_1316

def missing1312_1316 : List (BitVec (edgeCount 12)) :=
  missing1312_1314 ++ missing1314_1316
abbrev records1312_1316 : List Blob :=
  records1312_1314 ++ records1314_1316
theorem aligned1312_1316 :
    AlignedValid 12 3 missing1312_1316 records1312_1316 :=
  aligned1312_1314.append aligned1314_1316

def missing1316_1317 : List (BitVec (edgeCount 12)) :=
  [missing1316]
abbrev records1316_1317 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1316]
theorem aligned1316_1317 :
    AlignedValid 12 3 missing1316_1317 records1316_1317 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1316
    maskCheck1316 AlignedValid.nil

def missing1317_1318 : List (BitVec (edgeCount 12)) :=
  [missing1317]
abbrev records1317_1318 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1317]
theorem aligned1317_1318 :
    AlignedValid 12 3 missing1317_1318 records1317_1318 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1317
    maskCheck1317 AlignedValid.nil

def missing1316_1318 : List (BitVec (edgeCount 12)) :=
  missing1316_1317 ++ missing1317_1318
abbrev records1316_1318 : List Blob :=
  records1316_1317 ++ records1317_1318
theorem aligned1316_1318 :
    AlignedValid 12 3 missing1316_1318 records1316_1318 :=
  aligned1316_1317.append aligned1317_1318

def missing1318_1319 : List (BitVec (edgeCount 12)) :=
  [missing1318]
abbrev records1318_1319 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1318]
theorem aligned1318_1319 :
    AlignedValid 12 3 missing1318_1319 records1318_1319 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1318
    maskCheck1318 AlignedValid.nil

def missing1319_1320 : List (BitVec (edgeCount 12)) :=
  [missing1319]
abbrev records1319_1320 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1319]
theorem aligned1319_1320 :
    AlignedValid 12 3 missing1319_1320 records1319_1320 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1319
    maskCheck1319 AlignedValid.nil

def missing1318_1320 : List (BitVec (edgeCount 12)) :=
  missing1318_1319 ++ missing1319_1320
abbrev records1318_1320 : List Blob :=
  records1318_1319 ++ records1319_1320
theorem aligned1318_1320 :
    AlignedValid 12 3 missing1318_1320 records1318_1320 :=
  aligned1318_1319.append aligned1319_1320

def missing1316_1320 : List (BitVec (edgeCount 12)) :=
  missing1316_1318 ++ missing1318_1320
abbrev records1316_1320 : List Blob :=
  records1316_1318 ++ records1318_1320
theorem aligned1316_1320 :
    AlignedValid 12 3 missing1316_1320 records1316_1320 :=
  aligned1316_1318.append aligned1318_1320

def missing1312_1320 : List (BitVec (edgeCount 12)) :=
  missing1312_1316 ++ missing1316_1320
abbrev records1312_1320 : List Blob :=
  records1312_1316 ++ records1316_1320
theorem aligned1312_1320 :
    AlignedValid 12 3 missing1312_1320 records1312_1320 :=
  aligned1312_1316.append aligned1316_1320

def missing1320_1321 : List (BitVec (edgeCount 12)) :=
  [missing1320]
abbrev records1320_1321 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1320]
theorem aligned1320_1321 :
    AlignedValid 12 3 missing1320_1321 records1320_1321 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1320
    maskCheck1320 AlignedValid.nil

def missing1321_1322 : List (BitVec (edgeCount 12)) :=
  [missing1321]
abbrev records1321_1322 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1321]
theorem aligned1321_1322 :
    AlignedValid 12 3 missing1321_1322 records1321_1322 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1321
    maskCheck1321 AlignedValid.nil

def missing1320_1322 : List (BitVec (edgeCount 12)) :=
  missing1320_1321 ++ missing1321_1322
abbrev records1320_1322 : List Blob :=
  records1320_1321 ++ records1321_1322
theorem aligned1320_1322 :
    AlignedValid 12 3 missing1320_1322 records1320_1322 :=
  aligned1320_1321.append aligned1321_1322

def missing1322_1323 : List (BitVec (edgeCount 12)) :=
  [missing1322]
abbrev records1322_1323 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1322]
theorem aligned1322_1323 :
    AlignedValid 12 3 missing1322_1323 records1322_1323 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1322
    maskCheck1322 AlignedValid.nil

def missing1323_1324 : List (BitVec (edgeCount 12)) :=
  [missing1323]
abbrev records1323_1324 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1323]
theorem aligned1323_1324 :
    AlignedValid 12 3 missing1323_1324 records1323_1324 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1323
    maskCheck1323 AlignedValid.nil

def missing1322_1324 : List (BitVec (edgeCount 12)) :=
  missing1322_1323 ++ missing1323_1324
abbrev records1322_1324 : List Blob :=
  records1322_1323 ++ records1323_1324
theorem aligned1322_1324 :
    AlignedValid 12 3 missing1322_1324 records1322_1324 :=
  aligned1322_1323.append aligned1323_1324

def missing1320_1324 : List (BitVec (edgeCount 12)) :=
  missing1320_1322 ++ missing1322_1324
abbrev records1320_1324 : List Blob :=
  records1320_1322 ++ records1322_1324
theorem aligned1320_1324 :
    AlignedValid 12 3 missing1320_1324 records1320_1324 :=
  aligned1320_1322.append aligned1322_1324

def missing1324_1325 : List (BitVec (edgeCount 12)) :=
  [missing1324]
abbrev records1324_1325 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1324]
theorem aligned1324_1325 :
    AlignedValid 12 3 missing1324_1325 records1324_1325 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1324
    maskCheck1324 AlignedValid.nil

def missing1325_1326 : List (BitVec (edgeCount 12)) :=
  [missing1325]
abbrev records1325_1326 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1325]
theorem aligned1325_1326 :
    AlignedValid 12 3 missing1325_1326 records1325_1326 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1325
    maskCheck1325 AlignedValid.nil

def missing1324_1326 : List (BitVec (edgeCount 12)) :=
  missing1324_1325 ++ missing1325_1326
abbrev records1324_1326 : List Blob :=
  records1324_1325 ++ records1325_1326
theorem aligned1324_1326 :
    AlignedValid 12 3 missing1324_1326 records1324_1326 :=
  aligned1324_1325.append aligned1325_1326

def missing1326_1327 : List (BitVec (edgeCount 12)) :=
  [missing1326]
abbrev records1326_1327 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1326]
theorem aligned1326_1327 :
    AlignedValid 12 3 missing1326_1327 records1326_1327 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1326
    maskCheck1326 AlignedValid.nil

def missing1327_1328 : List (BitVec (edgeCount 12)) :=
  [missing1327]
abbrev records1327_1328 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1327]
theorem aligned1327_1328 :
    AlignedValid 12 3 missing1327_1328 records1327_1328 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1327
    maskCheck1327 AlignedValid.nil

def missing1326_1328 : List (BitVec (edgeCount 12)) :=
  missing1326_1327 ++ missing1327_1328
abbrev records1326_1328 : List Blob :=
  records1326_1327 ++ records1327_1328
theorem aligned1326_1328 :
    AlignedValid 12 3 missing1326_1328 records1326_1328 :=
  aligned1326_1327.append aligned1327_1328

def missing1324_1328 : List (BitVec (edgeCount 12)) :=
  missing1324_1326 ++ missing1326_1328
abbrev records1324_1328 : List Blob :=
  records1324_1326 ++ records1326_1328
theorem aligned1324_1328 :
    AlignedValid 12 3 missing1324_1328 records1324_1328 :=
  aligned1324_1326.append aligned1326_1328

def missing1320_1328 : List (BitVec (edgeCount 12)) :=
  missing1320_1324 ++ missing1324_1328
abbrev records1320_1328 : List Blob :=
  records1320_1324 ++ records1324_1328
theorem aligned1320_1328 :
    AlignedValid 12 3 missing1320_1328 records1320_1328 :=
  aligned1320_1324.append aligned1324_1328

def missing1312_1328 : List (BitVec (edgeCount 12)) :=
  missing1312_1320 ++ missing1320_1328
abbrev records1312_1328 : List Blob :=
  records1312_1320 ++ records1320_1328
theorem aligned1312_1328 :
    AlignedValid 12 3 missing1312_1328 records1312_1328 :=
  aligned1312_1320.append aligned1320_1328

def missing1328_1329 : List (BitVec (edgeCount 12)) :=
  [missing1328]
abbrev records1328_1329 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1328]
theorem aligned1328_1329 :
    AlignedValid 12 3 missing1328_1329 records1328_1329 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1328
    maskCheck1328 AlignedValid.nil

def missing1329_1330 : List (BitVec (edgeCount 12)) :=
  [missing1329]
abbrev records1329_1330 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1329]
theorem aligned1329_1330 :
    AlignedValid 12 3 missing1329_1330 records1329_1330 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1329
    maskCheck1329 AlignedValid.nil

def missing1328_1330 : List (BitVec (edgeCount 12)) :=
  missing1328_1329 ++ missing1329_1330
abbrev records1328_1330 : List Blob :=
  records1328_1329 ++ records1329_1330
theorem aligned1328_1330 :
    AlignedValid 12 3 missing1328_1330 records1328_1330 :=
  aligned1328_1329.append aligned1329_1330

def missing1330_1331 : List (BitVec (edgeCount 12)) :=
  [missing1330]
abbrev records1330_1331 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1330]
theorem aligned1330_1331 :
    AlignedValid 12 3 missing1330_1331 records1330_1331 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1330
    maskCheck1330 AlignedValid.nil

def missing1331_1332 : List (BitVec (edgeCount 12)) :=
  [missing1331]
abbrev records1331_1332 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1331]
theorem aligned1331_1332 :
    AlignedValid 12 3 missing1331_1332 records1331_1332 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1331
    maskCheck1331 AlignedValid.nil

def missing1330_1332 : List (BitVec (edgeCount 12)) :=
  missing1330_1331 ++ missing1331_1332
abbrev records1330_1332 : List Blob :=
  records1330_1331 ++ records1331_1332
theorem aligned1330_1332 :
    AlignedValid 12 3 missing1330_1332 records1330_1332 :=
  aligned1330_1331.append aligned1331_1332

def missing1328_1332 : List (BitVec (edgeCount 12)) :=
  missing1328_1330 ++ missing1330_1332
abbrev records1328_1332 : List Blob :=
  records1328_1330 ++ records1330_1332
theorem aligned1328_1332 :
    AlignedValid 12 3 missing1328_1332 records1328_1332 :=
  aligned1328_1330.append aligned1330_1332

def missing1332_1333 : List (BitVec (edgeCount 12)) :=
  [missing1332]
abbrev records1332_1333 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1332]
theorem aligned1332_1333 :
    AlignedValid 12 3 missing1332_1333 records1332_1333 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1332
    maskCheck1332 AlignedValid.nil

def missing1333_1334 : List (BitVec (edgeCount 12)) :=
  [missing1333]
abbrev records1333_1334 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1333]
theorem aligned1333_1334 :
    AlignedValid 12 3 missing1333_1334 records1333_1334 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1333
    maskCheck1333 AlignedValid.nil

def missing1332_1334 : List (BitVec (edgeCount 12)) :=
  missing1332_1333 ++ missing1333_1334
abbrev records1332_1334 : List Blob :=
  records1332_1333 ++ records1333_1334
theorem aligned1332_1334 :
    AlignedValid 12 3 missing1332_1334 records1332_1334 :=
  aligned1332_1333.append aligned1333_1334

def missing1334_1335 : List (BitVec (edgeCount 12)) :=
  [missing1334]
abbrev records1334_1335 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1334]
theorem aligned1334_1335 :
    AlignedValid 12 3 missing1334_1335 records1334_1335 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1334
    maskCheck1334 AlignedValid.nil

def missing1335_1336 : List (BitVec (edgeCount 12)) :=
  [missing1335]
abbrev records1335_1336 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1335]
theorem aligned1335_1336 :
    AlignedValid 12 3 missing1335_1336 records1335_1336 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1335
    maskCheck1335 AlignedValid.nil

def missing1334_1336 : List (BitVec (edgeCount 12)) :=
  missing1334_1335 ++ missing1335_1336
abbrev records1334_1336 : List Blob :=
  records1334_1335 ++ records1335_1336
theorem aligned1334_1336 :
    AlignedValid 12 3 missing1334_1336 records1334_1336 :=
  aligned1334_1335.append aligned1335_1336

def missing1332_1336 : List (BitVec (edgeCount 12)) :=
  missing1332_1334 ++ missing1334_1336
abbrev records1332_1336 : List Blob :=
  records1332_1334 ++ records1334_1336
theorem aligned1332_1336 :
    AlignedValid 12 3 missing1332_1336 records1332_1336 :=
  aligned1332_1334.append aligned1334_1336

def missing1328_1336 : List (BitVec (edgeCount 12)) :=
  missing1328_1332 ++ missing1332_1336
abbrev records1328_1336 : List Blob :=
  records1328_1332 ++ records1332_1336
theorem aligned1328_1336 :
    AlignedValid 12 3 missing1328_1336 records1328_1336 :=
  aligned1328_1332.append aligned1332_1336

def missing1336_1337 : List (BitVec (edgeCount 12)) :=
  [missing1336]
abbrev records1336_1337 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1336]
theorem aligned1336_1337 :
    AlignedValid 12 3 missing1336_1337 records1336_1337 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1336
    maskCheck1336 AlignedValid.nil

def missing1337_1338 : List (BitVec (edgeCount 12)) :=
  [missing1337]
abbrev records1337_1338 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1337]
theorem aligned1337_1338 :
    AlignedValid 12 3 missing1337_1338 records1337_1338 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1337
    maskCheck1337 AlignedValid.nil

def missing1336_1338 : List (BitVec (edgeCount 12)) :=
  missing1336_1337 ++ missing1337_1338
abbrev records1336_1338 : List Blob :=
  records1336_1337 ++ records1337_1338
theorem aligned1336_1338 :
    AlignedValid 12 3 missing1336_1338 records1336_1338 :=
  aligned1336_1337.append aligned1337_1338

def missing1338_1339 : List (BitVec (edgeCount 12)) :=
  [missing1338]
abbrev records1338_1339 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1338]
theorem aligned1338_1339 :
    AlignedValid 12 3 missing1338_1339 records1338_1339 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1338
    maskCheck1338 AlignedValid.nil

def missing1339_1340 : List (BitVec (edgeCount 12)) :=
  [missing1339]
abbrev records1339_1340 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1339]
theorem aligned1339_1340 :
    AlignedValid 12 3 missing1339_1340 records1339_1340 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1339
    maskCheck1339 AlignedValid.nil

def missing1338_1340 : List (BitVec (edgeCount 12)) :=
  missing1338_1339 ++ missing1339_1340
abbrev records1338_1340 : List Blob :=
  records1338_1339 ++ records1339_1340
theorem aligned1338_1340 :
    AlignedValid 12 3 missing1338_1340 records1338_1340 :=
  aligned1338_1339.append aligned1339_1340

def missing1336_1340 : List (BitVec (edgeCount 12)) :=
  missing1336_1338 ++ missing1338_1340
abbrev records1336_1340 : List Blob :=
  records1336_1338 ++ records1338_1340
theorem aligned1336_1340 :
    AlignedValid 12 3 missing1336_1340 records1336_1340 :=
  aligned1336_1338.append aligned1338_1340

def missing1340_1341 : List (BitVec (edgeCount 12)) :=
  [missing1340]
abbrev records1340_1341 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1340]
theorem aligned1340_1341 :
    AlignedValid 12 3 missing1340_1341 records1340_1341 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1340
    maskCheck1340 AlignedValid.nil

def missing1341_1342 : List (BitVec (edgeCount 12)) :=
  [missing1341]
abbrev records1341_1342 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1341]
theorem aligned1341_1342 :
    AlignedValid 12 3 missing1341_1342 records1341_1342 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1341
    maskCheck1341 AlignedValid.nil

def missing1340_1342 : List (BitVec (edgeCount 12)) :=
  missing1340_1341 ++ missing1341_1342
abbrev records1340_1342 : List Blob :=
  records1340_1341 ++ records1341_1342
theorem aligned1340_1342 :
    AlignedValid 12 3 missing1340_1342 records1340_1342 :=
  aligned1340_1341.append aligned1341_1342

def missing1342_1343 : List (BitVec (edgeCount 12)) :=
  [missing1342]
abbrev records1342_1343 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1342]
theorem aligned1342_1343 :
    AlignedValid 12 3 missing1342_1343 records1342_1343 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1342
    maskCheck1342 AlignedValid.nil

def missing1343_1344 : List (BitVec (edgeCount 12)) :=
  [missing1343]
abbrev records1343_1344 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1343]
theorem aligned1343_1344 :
    AlignedValid 12 3 missing1343_1344 records1343_1344 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1343
    maskCheck1343 AlignedValid.nil

def missing1342_1344 : List (BitVec (edgeCount 12)) :=
  missing1342_1343 ++ missing1343_1344
abbrev records1342_1344 : List Blob :=
  records1342_1343 ++ records1343_1344
theorem aligned1342_1344 :
    AlignedValid 12 3 missing1342_1344 records1342_1344 :=
  aligned1342_1343.append aligned1343_1344

def missing1340_1344 : List (BitVec (edgeCount 12)) :=
  missing1340_1342 ++ missing1342_1344
abbrev records1340_1344 : List Blob :=
  records1340_1342 ++ records1342_1344
theorem aligned1340_1344 :
    AlignedValid 12 3 missing1340_1344 records1340_1344 :=
  aligned1340_1342.append aligned1342_1344

def missing1336_1344 : List (BitVec (edgeCount 12)) :=
  missing1336_1340 ++ missing1340_1344
abbrev records1336_1344 : List Blob :=
  records1336_1340 ++ records1340_1344
theorem aligned1336_1344 :
    AlignedValid 12 3 missing1336_1344 records1336_1344 :=
  aligned1336_1340.append aligned1340_1344

def missing1328_1344 : List (BitVec (edgeCount 12)) :=
  missing1328_1336 ++ missing1336_1344
abbrev records1328_1344 : List Blob :=
  records1328_1336 ++ records1336_1344
theorem aligned1328_1344 :
    AlignedValid 12 3 missing1328_1344 records1328_1344 :=
  aligned1328_1336.append aligned1336_1344

def missing1312_1344 : List (BitVec (edgeCount 12)) :=
  missing1312_1328 ++ missing1328_1344
abbrev records1312_1344 : List Blob :=
  records1312_1328 ++ records1328_1344
theorem aligned1312_1344 :
    AlignedValid 12 3 missing1312_1344 records1312_1344 :=
  aligned1312_1328.append aligned1328_1344

def missing1280_1344 : List (BitVec (edgeCount 12)) :=
  missing1280_1312 ++ missing1312_1344
abbrev records1280_1344 : List Blob :=
  records1280_1312 ++ records1312_1344
theorem aligned1280_1344 :
    AlignedValid 12 3 missing1280_1344 records1280_1344 :=
  aligned1280_1312.append aligned1312_1344

def missing1344_1345 : List (BitVec (edgeCount 12)) :=
  [missing1344]
abbrev records1344_1345 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1344]
theorem aligned1344_1345 :
    AlignedValid 12 3 missing1344_1345 records1344_1345 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1344
    maskCheck1344 AlignedValid.nil

def missing1345_1346 : List (BitVec (edgeCount 12)) :=
  [missing1345]
abbrev records1345_1346 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1345]
theorem aligned1345_1346 :
    AlignedValid 12 3 missing1345_1346 records1345_1346 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1345
    maskCheck1345 AlignedValid.nil

def missing1344_1346 : List (BitVec (edgeCount 12)) :=
  missing1344_1345 ++ missing1345_1346
abbrev records1344_1346 : List Blob :=
  records1344_1345 ++ records1345_1346
theorem aligned1344_1346 :
    AlignedValid 12 3 missing1344_1346 records1344_1346 :=
  aligned1344_1345.append aligned1345_1346

def missing1346_1347 : List (BitVec (edgeCount 12)) :=
  [missing1346]
abbrev records1346_1347 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1346]
theorem aligned1346_1347 :
    AlignedValid 12 3 missing1346_1347 records1346_1347 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1346
    maskCheck1346 AlignedValid.nil

def missing1347_1348 : List (BitVec (edgeCount 12)) :=
  [missing1347]
abbrev records1347_1348 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1347]
theorem aligned1347_1348 :
    AlignedValid 12 3 missing1347_1348 records1347_1348 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1347
    maskCheck1347 AlignedValid.nil

def missing1346_1348 : List (BitVec (edgeCount 12)) :=
  missing1346_1347 ++ missing1347_1348
abbrev records1346_1348 : List Blob :=
  records1346_1347 ++ records1347_1348
theorem aligned1346_1348 :
    AlignedValid 12 3 missing1346_1348 records1346_1348 :=
  aligned1346_1347.append aligned1347_1348

def missing1344_1348 : List (BitVec (edgeCount 12)) :=
  missing1344_1346 ++ missing1346_1348
abbrev records1344_1348 : List Blob :=
  records1344_1346 ++ records1346_1348
theorem aligned1344_1348 :
    AlignedValid 12 3 missing1344_1348 records1344_1348 :=
  aligned1344_1346.append aligned1346_1348

def missing1348_1349 : List (BitVec (edgeCount 12)) :=
  [missing1348]
abbrev records1348_1349 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1348]
theorem aligned1348_1349 :
    AlignedValid 12 3 missing1348_1349 records1348_1349 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1348
    maskCheck1348 AlignedValid.nil

def missing1349_1350 : List (BitVec (edgeCount 12)) :=
  [missing1349]
abbrev records1349_1350 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1349]
theorem aligned1349_1350 :
    AlignedValid 12 3 missing1349_1350 records1349_1350 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1349
    maskCheck1349 AlignedValid.nil

def missing1348_1350 : List (BitVec (edgeCount 12)) :=
  missing1348_1349 ++ missing1349_1350
abbrev records1348_1350 : List Blob :=
  records1348_1349 ++ records1349_1350
theorem aligned1348_1350 :
    AlignedValid 12 3 missing1348_1350 records1348_1350 :=
  aligned1348_1349.append aligned1349_1350

def missing1350_1351 : List (BitVec (edgeCount 12)) :=
  [missing1350]
abbrev records1350_1351 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1350]
theorem aligned1350_1351 :
    AlignedValid 12 3 missing1350_1351 records1350_1351 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1350
    maskCheck1350 AlignedValid.nil

def missing1351_1352 : List (BitVec (edgeCount 12)) :=
  [missing1351]
abbrev records1351_1352 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1351]
theorem aligned1351_1352 :
    AlignedValid 12 3 missing1351_1352 records1351_1352 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1351
    maskCheck1351 AlignedValid.nil

def missing1350_1352 : List (BitVec (edgeCount 12)) :=
  missing1350_1351 ++ missing1351_1352
abbrev records1350_1352 : List Blob :=
  records1350_1351 ++ records1351_1352
theorem aligned1350_1352 :
    AlignedValid 12 3 missing1350_1352 records1350_1352 :=
  aligned1350_1351.append aligned1351_1352

def missing1348_1352 : List (BitVec (edgeCount 12)) :=
  missing1348_1350 ++ missing1350_1352
abbrev records1348_1352 : List Blob :=
  records1348_1350 ++ records1350_1352
theorem aligned1348_1352 :
    AlignedValid 12 3 missing1348_1352 records1348_1352 :=
  aligned1348_1350.append aligned1350_1352

def missing1344_1352 : List (BitVec (edgeCount 12)) :=
  missing1344_1348 ++ missing1348_1352
abbrev records1344_1352 : List Blob :=
  records1344_1348 ++ records1348_1352
theorem aligned1344_1352 :
    AlignedValid 12 3 missing1344_1352 records1344_1352 :=
  aligned1344_1348.append aligned1348_1352

def missing1352_1353 : List (BitVec (edgeCount 12)) :=
  [missing1352]
abbrev records1352_1353 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1352]
theorem aligned1352_1353 :
    AlignedValid 12 3 missing1352_1353 records1352_1353 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1352
    maskCheck1352 AlignedValid.nil

def missing1353_1354 : List (BitVec (edgeCount 12)) :=
  [missing1353]
abbrev records1353_1354 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1353]
theorem aligned1353_1354 :
    AlignedValid 12 3 missing1353_1354 records1353_1354 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1353
    maskCheck1353 AlignedValid.nil

def missing1352_1354 : List (BitVec (edgeCount 12)) :=
  missing1352_1353 ++ missing1353_1354
abbrev records1352_1354 : List Blob :=
  records1352_1353 ++ records1353_1354
theorem aligned1352_1354 :
    AlignedValid 12 3 missing1352_1354 records1352_1354 :=
  aligned1352_1353.append aligned1353_1354

def missing1354_1355 : List (BitVec (edgeCount 12)) :=
  [missing1354]
abbrev records1354_1355 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1354]
theorem aligned1354_1355 :
    AlignedValid 12 3 missing1354_1355 records1354_1355 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1354
    maskCheck1354 AlignedValid.nil

def missing1355_1356 : List (BitVec (edgeCount 12)) :=
  [missing1355]
abbrev records1355_1356 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1355]
theorem aligned1355_1356 :
    AlignedValid 12 3 missing1355_1356 records1355_1356 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1355
    maskCheck1355 AlignedValid.nil

def missing1354_1356 : List (BitVec (edgeCount 12)) :=
  missing1354_1355 ++ missing1355_1356
abbrev records1354_1356 : List Blob :=
  records1354_1355 ++ records1355_1356
theorem aligned1354_1356 :
    AlignedValid 12 3 missing1354_1356 records1354_1356 :=
  aligned1354_1355.append aligned1355_1356

def missing1352_1356 : List (BitVec (edgeCount 12)) :=
  missing1352_1354 ++ missing1354_1356
abbrev records1352_1356 : List Blob :=
  records1352_1354 ++ records1354_1356
theorem aligned1352_1356 :
    AlignedValid 12 3 missing1352_1356 records1352_1356 :=
  aligned1352_1354.append aligned1354_1356

def missing1356_1357 : List (BitVec (edgeCount 12)) :=
  [missing1356]
abbrev records1356_1357 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1356]
theorem aligned1356_1357 :
    AlignedValid 12 3 missing1356_1357 records1356_1357 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1356
    maskCheck1356 AlignedValid.nil

def missing1357_1358 : List (BitVec (edgeCount 12)) :=
  [missing1357]
abbrev records1357_1358 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1357]
theorem aligned1357_1358 :
    AlignedValid 12 3 missing1357_1358 records1357_1358 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1357
    maskCheck1357 AlignedValid.nil

def missing1356_1358 : List (BitVec (edgeCount 12)) :=
  missing1356_1357 ++ missing1357_1358
abbrev records1356_1358 : List Blob :=
  records1356_1357 ++ records1357_1358
theorem aligned1356_1358 :
    AlignedValid 12 3 missing1356_1358 records1356_1358 :=
  aligned1356_1357.append aligned1357_1358

def missing1358_1359 : List (BitVec (edgeCount 12)) :=
  [missing1358]
abbrev records1358_1359 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1358]
theorem aligned1358_1359 :
    AlignedValid 12 3 missing1358_1359 records1358_1359 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1358
    maskCheck1358 AlignedValid.nil

def missing1359_1360 : List (BitVec (edgeCount 12)) :=
  [missing1359]
abbrev records1359_1360 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1359]
theorem aligned1359_1360 :
    AlignedValid 12 3 missing1359_1360 records1359_1360 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1359
    maskCheck1359 AlignedValid.nil

def missing1358_1360 : List (BitVec (edgeCount 12)) :=
  missing1358_1359 ++ missing1359_1360
abbrev records1358_1360 : List Blob :=
  records1358_1359 ++ records1359_1360
theorem aligned1358_1360 :
    AlignedValid 12 3 missing1358_1360 records1358_1360 :=
  aligned1358_1359.append aligned1359_1360

def missing1356_1360 : List (BitVec (edgeCount 12)) :=
  missing1356_1358 ++ missing1358_1360
abbrev records1356_1360 : List Blob :=
  records1356_1358 ++ records1358_1360
theorem aligned1356_1360 :
    AlignedValid 12 3 missing1356_1360 records1356_1360 :=
  aligned1356_1358.append aligned1358_1360

def missing1352_1360 : List (BitVec (edgeCount 12)) :=
  missing1352_1356 ++ missing1356_1360
abbrev records1352_1360 : List Blob :=
  records1352_1356 ++ records1356_1360
theorem aligned1352_1360 :
    AlignedValid 12 3 missing1352_1360 records1352_1360 :=
  aligned1352_1356.append aligned1356_1360

def missing1344_1360 : List (BitVec (edgeCount 12)) :=
  missing1344_1352 ++ missing1352_1360
abbrev records1344_1360 : List Blob :=
  records1344_1352 ++ records1352_1360
theorem aligned1344_1360 :
    AlignedValid 12 3 missing1344_1360 records1344_1360 :=
  aligned1344_1352.append aligned1352_1360

def missing1360_1361 : List (BitVec (edgeCount 12)) :=
  [missing1360]
abbrev records1360_1361 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1360]
theorem aligned1360_1361 :
    AlignedValid 12 3 missing1360_1361 records1360_1361 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1360
    maskCheck1360 AlignedValid.nil

def missing1361_1362 : List (BitVec (edgeCount 12)) :=
  [missing1361]
abbrev records1361_1362 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1361]
theorem aligned1361_1362 :
    AlignedValid 12 3 missing1361_1362 records1361_1362 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1361
    maskCheck1361 AlignedValid.nil

def missing1360_1362 : List (BitVec (edgeCount 12)) :=
  missing1360_1361 ++ missing1361_1362
abbrev records1360_1362 : List Blob :=
  records1360_1361 ++ records1361_1362
theorem aligned1360_1362 :
    AlignedValid 12 3 missing1360_1362 records1360_1362 :=
  aligned1360_1361.append aligned1361_1362

def missing1362_1363 : List (BitVec (edgeCount 12)) :=
  [missing1362]
abbrev records1362_1363 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1362]
theorem aligned1362_1363 :
    AlignedValid 12 3 missing1362_1363 records1362_1363 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1362
    maskCheck1362 AlignedValid.nil

def missing1363_1364 : List (BitVec (edgeCount 12)) :=
  [missing1363]
abbrev records1363_1364 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1363]
theorem aligned1363_1364 :
    AlignedValid 12 3 missing1363_1364 records1363_1364 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1363
    maskCheck1363 AlignedValid.nil

def missing1362_1364 : List (BitVec (edgeCount 12)) :=
  missing1362_1363 ++ missing1363_1364
abbrev records1362_1364 : List Blob :=
  records1362_1363 ++ records1363_1364
theorem aligned1362_1364 :
    AlignedValid 12 3 missing1362_1364 records1362_1364 :=
  aligned1362_1363.append aligned1363_1364

def missing1360_1364 : List (BitVec (edgeCount 12)) :=
  missing1360_1362 ++ missing1362_1364
abbrev records1360_1364 : List Blob :=
  records1360_1362 ++ records1362_1364
theorem aligned1360_1364 :
    AlignedValid 12 3 missing1360_1364 records1360_1364 :=
  aligned1360_1362.append aligned1362_1364

def missing1364_1365 : List (BitVec (edgeCount 12)) :=
  [missing1364]
abbrev records1364_1365 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1364]
theorem aligned1364_1365 :
    AlignedValid 12 3 missing1364_1365 records1364_1365 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1364
    maskCheck1364 AlignedValid.nil

def missing1365_1366 : List (BitVec (edgeCount 12)) :=
  [missing1365]
abbrev records1365_1366 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1365]
theorem aligned1365_1366 :
    AlignedValid 12 3 missing1365_1366 records1365_1366 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1365
    maskCheck1365 AlignedValid.nil

def missing1364_1366 : List (BitVec (edgeCount 12)) :=
  missing1364_1365 ++ missing1365_1366
abbrev records1364_1366 : List Blob :=
  records1364_1365 ++ records1365_1366
theorem aligned1364_1366 :
    AlignedValid 12 3 missing1364_1366 records1364_1366 :=
  aligned1364_1365.append aligned1365_1366

def missing1366_1367 : List (BitVec (edgeCount 12)) :=
  [missing1366]
abbrev records1366_1367 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1366]
theorem aligned1366_1367 :
    AlignedValid 12 3 missing1366_1367 records1366_1367 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1366
    maskCheck1366 AlignedValid.nil

def missing1367_1368 : List (BitVec (edgeCount 12)) :=
  [missing1367]
abbrev records1367_1368 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1367]
theorem aligned1367_1368 :
    AlignedValid 12 3 missing1367_1368 records1367_1368 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1367
    maskCheck1367 AlignedValid.nil

def missing1366_1368 : List (BitVec (edgeCount 12)) :=
  missing1366_1367 ++ missing1367_1368
abbrev records1366_1368 : List Blob :=
  records1366_1367 ++ records1367_1368
theorem aligned1366_1368 :
    AlignedValid 12 3 missing1366_1368 records1366_1368 :=
  aligned1366_1367.append aligned1367_1368

def missing1364_1368 : List (BitVec (edgeCount 12)) :=
  missing1364_1366 ++ missing1366_1368
abbrev records1364_1368 : List Blob :=
  records1364_1366 ++ records1366_1368
theorem aligned1364_1368 :
    AlignedValid 12 3 missing1364_1368 records1364_1368 :=
  aligned1364_1366.append aligned1366_1368

def missing1360_1368 : List (BitVec (edgeCount 12)) :=
  missing1360_1364 ++ missing1364_1368
abbrev records1360_1368 : List Blob :=
  records1360_1364 ++ records1364_1368
theorem aligned1360_1368 :
    AlignedValid 12 3 missing1360_1368 records1360_1368 :=
  aligned1360_1364.append aligned1364_1368

def missing1368_1369 : List (BitVec (edgeCount 12)) :=
  [missing1368]
abbrev records1368_1369 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1368]
theorem aligned1368_1369 :
    AlignedValid 12 3 missing1368_1369 records1368_1369 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1368
    maskCheck1368 AlignedValid.nil

def missing1369_1370 : List (BitVec (edgeCount 12)) :=
  [missing1369]
abbrev records1369_1370 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1369]
theorem aligned1369_1370 :
    AlignedValid 12 3 missing1369_1370 records1369_1370 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1369
    maskCheck1369 AlignedValid.nil

def missing1368_1370 : List (BitVec (edgeCount 12)) :=
  missing1368_1369 ++ missing1369_1370
abbrev records1368_1370 : List Blob :=
  records1368_1369 ++ records1369_1370
theorem aligned1368_1370 :
    AlignedValid 12 3 missing1368_1370 records1368_1370 :=
  aligned1368_1369.append aligned1369_1370

def missing1370_1371 : List (BitVec (edgeCount 12)) :=
  [missing1370]
abbrev records1370_1371 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1370]
theorem aligned1370_1371 :
    AlignedValid 12 3 missing1370_1371 records1370_1371 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1370
    maskCheck1370 AlignedValid.nil

def missing1371_1372 : List (BitVec (edgeCount 12)) :=
  [missing1371]
abbrev records1371_1372 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1371]
theorem aligned1371_1372 :
    AlignedValid 12 3 missing1371_1372 records1371_1372 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1371
    maskCheck1371 AlignedValid.nil

def missing1370_1372 : List (BitVec (edgeCount 12)) :=
  missing1370_1371 ++ missing1371_1372
abbrev records1370_1372 : List Blob :=
  records1370_1371 ++ records1371_1372
theorem aligned1370_1372 :
    AlignedValid 12 3 missing1370_1372 records1370_1372 :=
  aligned1370_1371.append aligned1371_1372

def missing1368_1372 : List (BitVec (edgeCount 12)) :=
  missing1368_1370 ++ missing1370_1372
abbrev records1368_1372 : List Blob :=
  records1368_1370 ++ records1370_1372
theorem aligned1368_1372 :
    AlignedValid 12 3 missing1368_1372 records1368_1372 :=
  aligned1368_1370.append aligned1370_1372

def missing1372_1373 : List (BitVec (edgeCount 12)) :=
  [missing1372]
abbrev records1372_1373 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1372]
theorem aligned1372_1373 :
    AlignedValid 12 3 missing1372_1373 records1372_1373 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1372
    maskCheck1372 AlignedValid.nil

def missing1373_1374 : List (BitVec (edgeCount 12)) :=
  [missing1373]
abbrev records1373_1374 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1373]
theorem aligned1373_1374 :
    AlignedValid 12 3 missing1373_1374 records1373_1374 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1373
    maskCheck1373 AlignedValid.nil

def missing1372_1374 : List (BitVec (edgeCount 12)) :=
  missing1372_1373 ++ missing1373_1374
abbrev records1372_1374 : List Blob :=
  records1372_1373 ++ records1373_1374
theorem aligned1372_1374 :
    AlignedValid 12 3 missing1372_1374 records1372_1374 :=
  aligned1372_1373.append aligned1373_1374

def missing1374_1375 : List (BitVec (edgeCount 12)) :=
  [missing1374]
abbrev records1374_1375 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1374]
theorem aligned1374_1375 :
    AlignedValid 12 3 missing1374_1375 records1374_1375 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1374
    maskCheck1374 AlignedValid.nil

def missing1375_1376 : List (BitVec (edgeCount 12)) :=
  [missing1375]
abbrev records1375_1376 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1375]
theorem aligned1375_1376 :
    AlignedValid 12 3 missing1375_1376 records1375_1376 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1375
    maskCheck1375 AlignedValid.nil

def missing1374_1376 : List (BitVec (edgeCount 12)) :=
  missing1374_1375 ++ missing1375_1376
abbrev records1374_1376 : List Blob :=
  records1374_1375 ++ records1375_1376
theorem aligned1374_1376 :
    AlignedValid 12 3 missing1374_1376 records1374_1376 :=
  aligned1374_1375.append aligned1375_1376

def missing1372_1376 : List (BitVec (edgeCount 12)) :=
  missing1372_1374 ++ missing1374_1376
abbrev records1372_1376 : List Blob :=
  records1372_1374 ++ records1374_1376
theorem aligned1372_1376 :
    AlignedValid 12 3 missing1372_1376 records1372_1376 :=
  aligned1372_1374.append aligned1374_1376

def missing1368_1376 : List (BitVec (edgeCount 12)) :=
  missing1368_1372 ++ missing1372_1376
abbrev records1368_1376 : List Blob :=
  records1368_1372 ++ records1372_1376
theorem aligned1368_1376 :
    AlignedValid 12 3 missing1368_1376 records1368_1376 :=
  aligned1368_1372.append aligned1372_1376

def missing1360_1376 : List (BitVec (edgeCount 12)) :=
  missing1360_1368 ++ missing1368_1376
abbrev records1360_1376 : List Blob :=
  records1360_1368 ++ records1368_1376
theorem aligned1360_1376 :
    AlignedValid 12 3 missing1360_1376 records1360_1376 :=
  aligned1360_1368.append aligned1368_1376

def missing1344_1376 : List (BitVec (edgeCount 12)) :=
  missing1344_1360 ++ missing1360_1376
abbrev records1344_1376 : List Blob :=
  records1344_1360 ++ records1360_1376
theorem aligned1344_1376 :
    AlignedValid 12 3 missing1344_1376 records1344_1376 :=
  aligned1344_1360.append aligned1360_1376

def missing1376_1377 : List (BitVec (edgeCount 12)) :=
  [missing1376]
abbrev records1376_1377 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1376]
theorem aligned1376_1377 :
    AlignedValid 12 3 missing1376_1377 records1376_1377 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1376
    maskCheck1376 AlignedValid.nil

def missing1377_1378 : List (BitVec (edgeCount 12)) :=
  [missing1377]
abbrev records1377_1378 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1377]
theorem aligned1377_1378 :
    AlignedValid 12 3 missing1377_1378 records1377_1378 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1377
    maskCheck1377 AlignedValid.nil

def missing1376_1378 : List (BitVec (edgeCount 12)) :=
  missing1376_1377 ++ missing1377_1378
abbrev records1376_1378 : List Blob :=
  records1376_1377 ++ records1377_1378
theorem aligned1376_1378 :
    AlignedValid 12 3 missing1376_1378 records1376_1378 :=
  aligned1376_1377.append aligned1377_1378

def missing1378_1379 : List (BitVec (edgeCount 12)) :=
  [missing1378]
abbrev records1378_1379 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1378]
theorem aligned1378_1379 :
    AlignedValid 12 3 missing1378_1379 records1378_1379 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1378
    maskCheck1378 AlignedValid.nil

def missing1379_1380 : List (BitVec (edgeCount 12)) :=
  [missing1379]
abbrev records1379_1380 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1379]
theorem aligned1379_1380 :
    AlignedValid 12 3 missing1379_1380 records1379_1380 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1379
    maskCheck1379 AlignedValid.nil

def missing1378_1380 : List (BitVec (edgeCount 12)) :=
  missing1378_1379 ++ missing1379_1380
abbrev records1378_1380 : List Blob :=
  records1378_1379 ++ records1379_1380
theorem aligned1378_1380 :
    AlignedValid 12 3 missing1378_1380 records1378_1380 :=
  aligned1378_1379.append aligned1379_1380

def missing1376_1380 : List (BitVec (edgeCount 12)) :=
  missing1376_1378 ++ missing1378_1380
abbrev records1376_1380 : List Blob :=
  records1376_1378 ++ records1378_1380
theorem aligned1376_1380 :
    AlignedValid 12 3 missing1376_1380 records1376_1380 :=
  aligned1376_1378.append aligned1378_1380

def missing1380_1381 : List (BitVec (edgeCount 12)) :=
  [missing1380]
abbrev records1380_1381 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1380]
theorem aligned1380_1381 :
    AlignedValid 12 3 missing1380_1381 records1380_1381 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1380
    maskCheck1380 AlignedValid.nil

def missing1381_1382 : List (BitVec (edgeCount 12)) :=
  [missing1381]
abbrev records1381_1382 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1381]
theorem aligned1381_1382 :
    AlignedValid 12 3 missing1381_1382 records1381_1382 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1381
    maskCheck1381 AlignedValid.nil

def missing1380_1382 : List (BitVec (edgeCount 12)) :=
  missing1380_1381 ++ missing1381_1382
abbrev records1380_1382 : List Blob :=
  records1380_1381 ++ records1381_1382
theorem aligned1380_1382 :
    AlignedValid 12 3 missing1380_1382 records1380_1382 :=
  aligned1380_1381.append aligned1381_1382

def missing1382_1383 : List (BitVec (edgeCount 12)) :=
  [missing1382]
abbrev records1382_1383 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1382]
theorem aligned1382_1383 :
    AlignedValid 12 3 missing1382_1383 records1382_1383 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1382
    maskCheck1382 AlignedValid.nil

def missing1383_1384 : List (BitVec (edgeCount 12)) :=
  [missing1383]
abbrev records1383_1384 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1383]
theorem aligned1383_1384 :
    AlignedValid 12 3 missing1383_1384 records1383_1384 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1383
    maskCheck1383 AlignedValid.nil

def missing1382_1384 : List (BitVec (edgeCount 12)) :=
  missing1382_1383 ++ missing1383_1384
abbrev records1382_1384 : List Blob :=
  records1382_1383 ++ records1383_1384
theorem aligned1382_1384 :
    AlignedValid 12 3 missing1382_1384 records1382_1384 :=
  aligned1382_1383.append aligned1383_1384

def missing1380_1384 : List (BitVec (edgeCount 12)) :=
  missing1380_1382 ++ missing1382_1384
abbrev records1380_1384 : List Blob :=
  records1380_1382 ++ records1382_1384
theorem aligned1380_1384 :
    AlignedValid 12 3 missing1380_1384 records1380_1384 :=
  aligned1380_1382.append aligned1382_1384

def missing1376_1384 : List (BitVec (edgeCount 12)) :=
  missing1376_1380 ++ missing1380_1384
abbrev records1376_1384 : List Blob :=
  records1376_1380 ++ records1380_1384
theorem aligned1376_1384 :
    AlignedValid 12 3 missing1376_1384 records1376_1384 :=
  aligned1376_1380.append aligned1380_1384

def missing1384_1385 : List (BitVec (edgeCount 12)) :=
  [missing1384]
abbrev records1384_1385 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1384]
theorem aligned1384_1385 :
    AlignedValid 12 3 missing1384_1385 records1384_1385 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1384
    maskCheck1384 AlignedValid.nil

def missing1385_1386 : List (BitVec (edgeCount 12)) :=
  [missing1385]
abbrev records1385_1386 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1385]
theorem aligned1385_1386 :
    AlignedValid 12 3 missing1385_1386 records1385_1386 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1385
    maskCheck1385 AlignedValid.nil

def missing1384_1386 : List (BitVec (edgeCount 12)) :=
  missing1384_1385 ++ missing1385_1386
abbrev records1384_1386 : List Blob :=
  records1384_1385 ++ records1385_1386
theorem aligned1384_1386 :
    AlignedValid 12 3 missing1384_1386 records1384_1386 :=
  aligned1384_1385.append aligned1385_1386

def missing1386_1387 : List (BitVec (edgeCount 12)) :=
  [missing1386]
abbrev records1386_1387 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1386]
theorem aligned1386_1387 :
    AlignedValid 12 3 missing1386_1387 records1386_1387 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1386
    maskCheck1386 AlignedValid.nil

def missing1387_1388 : List (BitVec (edgeCount 12)) :=
  [missing1387]
abbrev records1387_1388 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1387]
theorem aligned1387_1388 :
    AlignedValid 12 3 missing1387_1388 records1387_1388 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1387
    maskCheck1387 AlignedValid.nil

def missing1386_1388 : List (BitVec (edgeCount 12)) :=
  missing1386_1387 ++ missing1387_1388
abbrev records1386_1388 : List Blob :=
  records1386_1387 ++ records1387_1388
theorem aligned1386_1388 :
    AlignedValid 12 3 missing1386_1388 records1386_1388 :=
  aligned1386_1387.append aligned1387_1388

def missing1384_1388 : List (BitVec (edgeCount 12)) :=
  missing1384_1386 ++ missing1386_1388
abbrev records1384_1388 : List Blob :=
  records1384_1386 ++ records1386_1388
theorem aligned1384_1388 :
    AlignedValid 12 3 missing1384_1388 records1384_1388 :=
  aligned1384_1386.append aligned1386_1388

def missing1388_1389 : List (BitVec (edgeCount 12)) :=
  [missing1388]
abbrev records1388_1389 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1388]
theorem aligned1388_1389 :
    AlignedValid 12 3 missing1388_1389 records1388_1389 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1388
    maskCheck1388 AlignedValid.nil

def missing1389_1390 : List (BitVec (edgeCount 12)) :=
  [missing1389]
abbrev records1389_1390 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1389]
theorem aligned1389_1390 :
    AlignedValid 12 3 missing1389_1390 records1389_1390 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1389
    maskCheck1389 AlignedValid.nil

def missing1388_1390 : List (BitVec (edgeCount 12)) :=
  missing1388_1389 ++ missing1389_1390
abbrev records1388_1390 : List Blob :=
  records1388_1389 ++ records1389_1390
theorem aligned1388_1390 :
    AlignedValid 12 3 missing1388_1390 records1388_1390 :=
  aligned1388_1389.append aligned1389_1390

def missing1390_1391 : List (BitVec (edgeCount 12)) :=
  [missing1390]
abbrev records1390_1391 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1390]
theorem aligned1390_1391 :
    AlignedValid 12 3 missing1390_1391 records1390_1391 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1390
    maskCheck1390 AlignedValid.nil

def missing1391_1392 : List (BitVec (edgeCount 12)) :=
  [missing1391]
abbrev records1391_1392 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1391]
theorem aligned1391_1392 :
    AlignedValid 12 3 missing1391_1392 records1391_1392 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1391
    maskCheck1391 AlignedValid.nil

def missing1390_1392 : List (BitVec (edgeCount 12)) :=
  missing1390_1391 ++ missing1391_1392
abbrev records1390_1392 : List Blob :=
  records1390_1391 ++ records1391_1392
theorem aligned1390_1392 :
    AlignedValid 12 3 missing1390_1392 records1390_1392 :=
  aligned1390_1391.append aligned1391_1392

def missing1388_1392 : List (BitVec (edgeCount 12)) :=
  missing1388_1390 ++ missing1390_1392
abbrev records1388_1392 : List Blob :=
  records1388_1390 ++ records1390_1392
theorem aligned1388_1392 :
    AlignedValid 12 3 missing1388_1392 records1388_1392 :=
  aligned1388_1390.append aligned1390_1392

def missing1384_1392 : List (BitVec (edgeCount 12)) :=
  missing1384_1388 ++ missing1388_1392
abbrev records1384_1392 : List Blob :=
  records1384_1388 ++ records1388_1392
theorem aligned1384_1392 :
    AlignedValid 12 3 missing1384_1392 records1384_1392 :=
  aligned1384_1388.append aligned1388_1392

def missing1376_1392 : List (BitVec (edgeCount 12)) :=
  missing1376_1384 ++ missing1384_1392
abbrev records1376_1392 : List Blob :=
  records1376_1384 ++ records1384_1392
theorem aligned1376_1392 :
    AlignedValid 12 3 missing1376_1392 records1376_1392 :=
  aligned1376_1384.append aligned1384_1392

def missing1392_1393 : List (BitVec (edgeCount 12)) :=
  [missing1392]
abbrev records1392_1393 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1392]
theorem aligned1392_1393 :
    AlignedValid 12 3 missing1392_1393 records1392_1393 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1392
    maskCheck1392 AlignedValid.nil

def missing1393_1394 : List (BitVec (edgeCount 12)) :=
  [missing1393]
abbrev records1393_1394 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1393]
theorem aligned1393_1394 :
    AlignedValid 12 3 missing1393_1394 records1393_1394 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1393
    maskCheck1393 AlignedValid.nil

def missing1392_1394 : List (BitVec (edgeCount 12)) :=
  missing1392_1393 ++ missing1393_1394
abbrev records1392_1394 : List Blob :=
  records1392_1393 ++ records1393_1394
theorem aligned1392_1394 :
    AlignedValid 12 3 missing1392_1394 records1392_1394 :=
  aligned1392_1393.append aligned1393_1394

def missing1394_1395 : List (BitVec (edgeCount 12)) :=
  [missing1394]
abbrev records1394_1395 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1394]
theorem aligned1394_1395 :
    AlignedValid 12 3 missing1394_1395 records1394_1395 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1394
    maskCheck1394 AlignedValid.nil

def missing1395_1396 : List (BitVec (edgeCount 12)) :=
  [missing1395]
abbrev records1395_1396 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1395]
theorem aligned1395_1396 :
    AlignedValid 12 3 missing1395_1396 records1395_1396 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1395
    maskCheck1395 AlignedValid.nil

def missing1394_1396 : List (BitVec (edgeCount 12)) :=
  missing1394_1395 ++ missing1395_1396
abbrev records1394_1396 : List Blob :=
  records1394_1395 ++ records1395_1396
theorem aligned1394_1396 :
    AlignedValid 12 3 missing1394_1396 records1394_1396 :=
  aligned1394_1395.append aligned1395_1396

def missing1392_1396 : List (BitVec (edgeCount 12)) :=
  missing1392_1394 ++ missing1394_1396
abbrev records1392_1396 : List Blob :=
  records1392_1394 ++ records1394_1396
theorem aligned1392_1396 :
    AlignedValid 12 3 missing1392_1396 records1392_1396 :=
  aligned1392_1394.append aligned1394_1396

def missing1396_1397 : List (BitVec (edgeCount 12)) :=
  [missing1396]
abbrev records1396_1397 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1396]
theorem aligned1396_1397 :
    AlignedValid 12 3 missing1396_1397 records1396_1397 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1396
    maskCheck1396 AlignedValid.nil

def missing1397_1398 : List (BitVec (edgeCount 12)) :=
  [missing1397]
abbrev records1397_1398 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1397]
theorem aligned1397_1398 :
    AlignedValid 12 3 missing1397_1398 records1397_1398 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1397
    maskCheck1397 AlignedValid.nil

def missing1396_1398 : List (BitVec (edgeCount 12)) :=
  missing1396_1397 ++ missing1397_1398
abbrev records1396_1398 : List Blob :=
  records1396_1397 ++ records1397_1398
theorem aligned1396_1398 :
    AlignedValid 12 3 missing1396_1398 records1396_1398 :=
  aligned1396_1397.append aligned1397_1398

def missing1398_1399 : List (BitVec (edgeCount 12)) :=
  [missing1398]
abbrev records1398_1399 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1398]
theorem aligned1398_1399 :
    AlignedValid 12 3 missing1398_1399 records1398_1399 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1398
    maskCheck1398 AlignedValid.nil

def missing1399_1400 : List (BitVec (edgeCount 12)) :=
  [missing1399]
abbrev records1399_1400 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1399]
theorem aligned1399_1400 :
    AlignedValid 12 3 missing1399_1400 records1399_1400 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1399
    maskCheck1399 AlignedValid.nil

def missing1398_1400 : List (BitVec (edgeCount 12)) :=
  missing1398_1399 ++ missing1399_1400
abbrev records1398_1400 : List Blob :=
  records1398_1399 ++ records1399_1400
theorem aligned1398_1400 :
    AlignedValid 12 3 missing1398_1400 records1398_1400 :=
  aligned1398_1399.append aligned1399_1400

def missing1396_1400 : List (BitVec (edgeCount 12)) :=
  missing1396_1398 ++ missing1398_1400
abbrev records1396_1400 : List Blob :=
  records1396_1398 ++ records1398_1400
theorem aligned1396_1400 :
    AlignedValid 12 3 missing1396_1400 records1396_1400 :=
  aligned1396_1398.append aligned1398_1400

def missing1392_1400 : List (BitVec (edgeCount 12)) :=
  missing1392_1396 ++ missing1396_1400
abbrev records1392_1400 : List Blob :=
  records1392_1396 ++ records1396_1400
theorem aligned1392_1400 :
    AlignedValid 12 3 missing1392_1400 records1392_1400 :=
  aligned1392_1396.append aligned1396_1400

def missing1400_1401 : List (BitVec (edgeCount 12)) :=
  [missing1400]
abbrev records1400_1401 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1400]
theorem aligned1400_1401 :
    AlignedValid 12 3 missing1400_1401 records1400_1401 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1400
    maskCheck1400 AlignedValid.nil

def missing1401_1402 : List (BitVec (edgeCount 12)) :=
  [missing1401]
abbrev records1401_1402 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1401]
theorem aligned1401_1402 :
    AlignedValid 12 3 missing1401_1402 records1401_1402 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1401
    maskCheck1401 AlignedValid.nil

def missing1400_1402 : List (BitVec (edgeCount 12)) :=
  missing1400_1401 ++ missing1401_1402
abbrev records1400_1402 : List Blob :=
  records1400_1401 ++ records1401_1402
theorem aligned1400_1402 :
    AlignedValid 12 3 missing1400_1402 records1400_1402 :=
  aligned1400_1401.append aligned1401_1402

def missing1402_1403 : List (BitVec (edgeCount 12)) :=
  [missing1402]
abbrev records1402_1403 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1402]
theorem aligned1402_1403 :
    AlignedValid 12 3 missing1402_1403 records1402_1403 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1402
    maskCheck1402 AlignedValid.nil

def missing1403_1404 : List (BitVec (edgeCount 12)) :=
  [missing1403]
abbrev records1403_1404 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1403]
theorem aligned1403_1404 :
    AlignedValid 12 3 missing1403_1404 records1403_1404 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1403
    maskCheck1403 AlignedValid.nil

def missing1402_1404 : List (BitVec (edgeCount 12)) :=
  missing1402_1403 ++ missing1403_1404
abbrev records1402_1404 : List Blob :=
  records1402_1403 ++ records1403_1404
theorem aligned1402_1404 :
    AlignedValid 12 3 missing1402_1404 records1402_1404 :=
  aligned1402_1403.append aligned1403_1404

def missing1400_1404 : List (BitVec (edgeCount 12)) :=
  missing1400_1402 ++ missing1402_1404
abbrev records1400_1404 : List Blob :=
  records1400_1402 ++ records1402_1404
theorem aligned1400_1404 :
    AlignedValid 12 3 missing1400_1404 records1400_1404 :=
  aligned1400_1402.append aligned1402_1404

def missing1404_1405 : List (BitVec (edgeCount 12)) :=
  [missing1404]
abbrev records1404_1405 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1404]
theorem aligned1404_1405 :
    AlignedValid 12 3 missing1404_1405 records1404_1405 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1404
    maskCheck1404 AlignedValid.nil

def missing1405_1406 : List (BitVec (edgeCount 12)) :=
  [missing1405]
abbrev records1405_1406 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1405]
theorem aligned1405_1406 :
    AlignedValid 12 3 missing1405_1406 records1405_1406 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1405
    maskCheck1405 AlignedValid.nil

def missing1404_1406 : List (BitVec (edgeCount 12)) :=
  missing1404_1405 ++ missing1405_1406
abbrev records1404_1406 : List Blob :=
  records1404_1405 ++ records1405_1406
theorem aligned1404_1406 :
    AlignedValid 12 3 missing1404_1406 records1404_1406 :=
  aligned1404_1405.append aligned1405_1406

def missing1406_1407 : List (BitVec (edgeCount 12)) :=
  [missing1406]
abbrev records1406_1407 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1406]
theorem aligned1406_1407 :
    AlignedValid 12 3 missing1406_1407 records1406_1407 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1406
    maskCheck1406 AlignedValid.nil

def missing1407_1408 : List (BitVec (edgeCount 12)) :=
  [missing1407]
abbrev records1407_1408 : List Blob :=
  [StrongPackedBucketN12A3Shard010.record1407]
theorem aligned1407_1408 :
    AlignedValid 12 3 missing1407_1408 records1407_1408 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A3Shard010.check1407
    maskCheck1407 AlignedValid.nil

def missing1406_1408 : List (BitVec (edgeCount 12)) :=
  missing1406_1407 ++ missing1407_1408
abbrev records1406_1408 : List Blob :=
  records1406_1407 ++ records1407_1408
theorem aligned1406_1408 :
    AlignedValid 12 3 missing1406_1408 records1406_1408 :=
  aligned1406_1407.append aligned1407_1408

def missing1404_1408 : List (BitVec (edgeCount 12)) :=
  missing1404_1406 ++ missing1406_1408
abbrev records1404_1408 : List Blob :=
  records1404_1406 ++ records1406_1408
theorem aligned1404_1408 :
    AlignedValid 12 3 missing1404_1408 records1404_1408 :=
  aligned1404_1406.append aligned1406_1408

def missing1400_1408 : List (BitVec (edgeCount 12)) :=
  missing1400_1404 ++ missing1404_1408
abbrev records1400_1408 : List Blob :=
  records1400_1404 ++ records1404_1408
theorem aligned1400_1408 :
    AlignedValid 12 3 missing1400_1408 records1400_1408 :=
  aligned1400_1404.append aligned1404_1408

def missing1392_1408 : List (BitVec (edgeCount 12)) :=
  missing1392_1400 ++ missing1400_1408
abbrev records1392_1408 : List Blob :=
  records1392_1400 ++ records1400_1408
theorem aligned1392_1408 :
    AlignedValid 12 3 missing1392_1408 records1392_1408 :=
  aligned1392_1400.append aligned1400_1408

def missing1376_1408 : List (BitVec (edgeCount 12)) :=
  missing1376_1392 ++ missing1392_1408
abbrev records1376_1408 : List Blob :=
  records1376_1392 ++ records1392_1408
theorem aligned1376_1408 :
    AlignedValid 12 3 missing1376_1408 records1376_1408 :=
  aligned1376_1392.append aligned1392_1408

def missing1344_1408 : List (BitVec (edgeCount 12)) :=
  missing1344_1376 ++ missing1376_1408
abbrev records1344_1408 : List Blob :=
  records1344_1376 ++ records1376_1408
theorem aligned1344_1408 :
    AlignedValid 12 3 missing1344_1408 records1344_1408 :=
  aligned1344_1376.append aligned1376_1408

def missing1280_1408 : List (BitVec (edgeCount 12)) :=
  missing1280_1344 ++ missing1344_1408
abbrev records1280_1408 : List Blob :=
  records1280_1344 ++ records1344_1408
theorem aligned1280_1408 :
    AlignedValid 12 3 missing1280_1408 records1280_1408 :=
  aligned1280_1344.append aligned1344_1408

abbrev missing : List (BitVec (edgeCount 12)) := missing1280_1408
abbrev records : List Blob := records1280_1408
theorem aligned : AlignedValid 12 3 missing records := aligned1280_1408

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A3AlignedShard010
