/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A1Shard001

/-! Decode-only alignment checks for n=12, a=1, records 128--255. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A1AlignedShard001

open PackedBucketCertificate

def missing128 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4071781897443737600
theorem maskCheck128 :
    checkMaskFor missing128 StrongPackedBucketN12A1Shard001.record128 = true := by
  decide

def missing129 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699473487143108608
theorem maskCheck129 :
    checkMaskFor missing129 StrongPackedBucketN12A1Shard001.record129 = true := by
  decide

def missing130 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18951675066275856384
theorem maskCheck130 :
    checkMaskFor missing130 StrongPackedBucketN12A1Shard001.record130 = true := by
  decide

def missing131 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19131819051370676224
theorem maskCheck131 :
    checkMaskFor missing131 StrongPackedBucketN12A1Shard001.record131 = true := by
  decide

def missing132 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19239905442427568128
theorem maskCheck132 :
    checkMaskFor missing132 StrongPackedBucketN12A1Shard001.record132 = true := by
  decide

def missing133 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20212682961939595264
theorem maskCheck133 :
    checkMaskFor missing133 StrongPackedBucketN12A1Shard001.record133 = true := by
  decide

def missing134 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20248711758958559232
theorem maskCheck134 :
    checkMaskFor missing134 StrongPackedBucketN12A1Shard001.record134 = true := by
  decide

def missing135 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22482497174134325248
theorem maskCheck135 :
    checkMaskFor missing135 StrongPackedBucketN12A1Shard001.record135 = true := by
  decide

def missing136 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 541487555166601216
theorem maskCheck136 :
    checkMaskFor missing136 StrongPackedBucketN12A1Shard001.record136 = true := by
  decide

def missing137 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081919510451060736
theorem maskCheck137 :
    checkMaskFor missing137 StrongPackedBucketN12A1Shard001.record137 = true := by
  decide

def missing138 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1406178683621736448
theorem maskCheck138 :
    checkMaskFor missing138 StrongPackedBucketN12A1Shard001.record138 = true := by
  decide

def missing139 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1658380262754484224
theorem maskCheck139 :
    checkMaskFor missing139 StrongPackedBucketN12A1Shard001.record139 = true := by
  decide

def missing140 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3567906504759574528
theorem maskCheck140 :
    checkMaskFor missing140 StrongPackedBucketN12A1Shard001.record140 = true := by
  decide

def missing141 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3675992895816466432
theorem maskCheck141 :
    checkMaskFor missing141 StrongPackedBucketN12A1Shard001.record141 = true := by
  decide

def missing142 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8107534929149034496
theorem maskCheck142 :
    checkMaskFor missing142 StrongPackedBucketN12A1Shard001.record142 = true := by
  decide

def missing143 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8143563726167998464
theorem maskCheck143 :
    checkMaskFor missing143 StrongPackedBucketN12A1Shard001.record143 = true := by
  decide

def missing144 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17294878168984846336
theorem maskCheck144 :
    checkMaskFor missing144 StrongPackedBucketN12A1Shard001.record144 = true := by
  decide

def missing145 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18700001252724441088
theorem maskCheck145 :
    checkMaskFor missing145 StrongPackedBucketN12A1Shard001.record145 = true := by
  decide

def missing146 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19708807569255432192
theorem maskCheck146 :
    checkMaskFor missing146 StrongPackedBucketN12A1Shard001.record146 = true := by
  decide

def missing147 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 21942592984431198208
theorem maskCheck147 :
    checkMaskFor missing147 StrongPackedBucketN12A1Shard001.record147 = true := by
  decide

def missing148 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18717206410675879936
theorem maskCheck148 :
    checkMaskFor missing148 StrongPackedBucketN12A1Shard001.record148 = true := by
  decide

def missing149 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18861321598751735808
theorem maskCheck149 :
    checkMaskFor missing149 StrongPackedBucketN12A1Shard001.record149 = true := by
  decide

def missing150 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19365724757017231360
theorem maskCheck150 :
    checkMaskFor missing150 StrongPackedBucketN12A1Shard001.record150 = true := by
  decide

def missing151 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1116998466862579712
theorem maskCheck151 :
    checkMaskFor missing151 StrongPackedBucketN12A1Shard001.record151 = true := by
  decide

def missing152 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2197862377431498752
theorem maskCheck152 :
    checkMaskFor missing152 StrongPackedBucketN12A1Shard001.record152 = true := by
  decide

def missing153 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4467676589626228736
theorem maskCheck153 :
    checkMaskFor missing153 StrongPackedBucketN12A1Shard001.record153 = true := by
  decide

def missing154 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18987281788268707840
theorem maskCheck154 :
    checkMaskFor missing154 StrongPackedBucketN12A1Shard001.record154 = true := by
  decide

def missing155 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19491684946534203392
theorem maskCheck155 :
    checkMaskFor missing155 StrongPackedBucketN12A1Shard001.record155 = true := by
  decide

def missing156 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55592539559536099328
theorem maskCheck156 :
    checkMaskFor missing156 StrongPackedBucketN12A1Shard001.record156 = true := by
  decide

def missing157 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117068835606757376
theorem maskCheck157 :
    checkMaskFor missing157 StrongPackedBucketN12A1Shard001.record157 = true := by
  decide

def missing158 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2125875152137748480
theorem maskCheck158 :
    checkMaskFor missing158 StrongPackedBucketN12A1Shard001.record158 = true := by
  decide

def missing159 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2233961543194640384
theorem maskCheck159 :
    checkMaskFor missing159 StrongPackedBucketN12A1Shard001.record159 = true := by
  decide

def missing160 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4359660567313514496
theorem maskCheck160 :
    checkMaskFor missing160 StrongPackedBucketN12A1Shard001.record160 = true := by
  decide

def missing161 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4395689364332478464
theorem maskCheck161 :
    checkMaskFor missing161 StrongPackedBucketN12A1Shard001.record161 = true := by
  decide

def missing162 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8935317788721938432
theorem maskCheck162 :
    checkMaskFor missing162 StrongPackedBucketN12A1Shard001.record162 = true := by
  decide

def missing163 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18987352157012885504
theorem maskCheck163 :
    checkMaskFor missing163 StrongPackedBucketN12A1Shard001.record163 = true := by
  decide

def missing164 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19419697721240453120
theorem maskCheck164 :
    checkMaskFor missing164 StrongPackedBucketN12A1Shard001.record164 = true := by
  decide

def missing165 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19491755315278381056
theorem maskCheck165 :
    checkMaskFor missing165 StrongPackedBucketN12A1Shard001.record165 = true := by
  decide

def missing166 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19527784112297345024
theorem maskCheck166 :
    checkMaskFor missing166 StrongPackedBucketN12A1Shard001.record166 = true := by
  decide

def missing167 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20500561631809372160
theorem maskCheck167 :
    checkMaskFor missing167 StrongPackedBucketN12A1Shard001.record167 = true := by
  decide

def missing168 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20536590428828336128
theorem maskCheck168 :
    checkMaskFor missing168 StrongPackedBucketN12A1Shard001.record168 = true := by
  decide

def missing169 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20608648022866264064
theorem maskCheck169 :
    checkMaskFor missing169 StrongPackedBucketN12A1Shard001.record169 = true := by
  decide

def missing170 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22770375844004102144
theorem maskCheck170 :
    checkMaskFor missing170 StrongPackedBucketN12A1Shard001.record170 = true := by
  decide

def missing171 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55592609928280276992
theorem maskCheck171 :
    checkMaskFor missing171 StrongPackedBucketN12A1Shard001.record171 = true := by
  decide

def missing172 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55736725116356132864
theorem maskCheck172 :
    checkMaskFor missing172 StrongPackedBucketN12A1Shard001.record172 = true := by
  decide

def missing173 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55844811507413024768
theorem maskCheck173 :
    checkMaskFor missing173 StrongPackedBucketN12A1Shard001.record173 = true := by
  decide

def missing174 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56241128274621628416
theorem maskCheck174 :
    checkMaskFor missing174 StrongPackedBucketN12A1Shard001.record174 = true := by
  decide

def missing175 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56277157071640592384
theorem maskCheck175 :
    checkMaskFor missing175 StrongPackedBucketN12A1Shard001.record175 = true := by
  decide

def missing176 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57358020982209511424
theorem maskCheck176 :
    checkMaskFor missing176 StrongPackedBucketN12A1Shard001.record176 = true := by
  decide

def missing177 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1117315126211379200
theorem maskCheck177 :
    checkMaskFor missing177 StrongPackedBucketN12A1Shard001.record177 = true := by
  decide

def missing178 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1982006254666514432
theorem maskCheck178 :
    checkMaskFor missing178 StrongPackedBucketN12A1Shard001.record178 = true := by
  decide

def missing179 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4143734075804352512
theorem maskCheck179 :
    checkMaskFor missing179 StrongPackedBucketN12A1Shard001.record179 = true := by
  decide

def missing180 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4215791669842280448
theorem maskCheck180 :
    checkMaskFor missing180 StrongPackedBucketN12A1Shard001.record180 = true := by
  decide

def missing181 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8683362500193812480
theorem maskCheck181 :
    checkMaskFor missing181 StrongPackedBucketN12A1Shard001.record181 = true := by
  decide

def missing182 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17870705740029624320
theorem maskCheck182 :
    checkMaskFor missing182 StrongPackedBucketN12A1Shard001.record182 = true := by
  decide

def missing183 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18987598447617507328
theorem maskCheck183 :
    checkMaskFor missing183 StrongPackedBucketN12A1Shard001.record183 = true := by
  decide

def missing184 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19275828823769219072
theorem maskCheck184 :
    checkMaskFor missing184 StrongPackedBucketN12A1Shard001.record184 = true := by
  decide

def missing185 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19492001605883002880
theorem maskCheck185 :
    checkMaskFor missing185 StrongPackedBucketN12A1Shard001.record185 = true := by
  decide

def missing186 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20284635140300210176
theorem maskCheck186 :
    checkMaskFor missing186 StrongPackedBucketN12A1Shard001.record186 = true := by
  decide

def missing187 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20356692734338138112
theorem maskCheck187 :
    checkMaskFor missing187 StrongPackedBucketN12A1Shard001.record187 = true := by
  decide

def missing188 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20608894313470885888
theorem maskCheck188 :
    checkMaskFor missing188 StrongPackedBucketN12A1Shard001.record188 = true := by
  decide

def missing189 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22518420555475976192
theorem maskCheck189 :
    checkMaskFor missing189 StrongPackedBucketN12A1Shard001.record189 = true := by
  decide

def missing190 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22626506946532868096
theorem maskCheck190 :
    checkMaskFor missing190 StrongPackedBucketN12A1Shard001.record190 = true := by
  decide

def missing191 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27094077776884400128
theorem maskCheck191 :
    checkMaskFor missing191 StrongPackedBucketN12A1Shard001.record191 = true := by
  decide

def missing192 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55592856218884898816
theorem maskCheck192 :
    checkMaskFor missing192 StrongPackedBucketN12A1Shard001.record192 = true := by
  decide

def missing193 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56025201783112466432
theorem maskCheck193 :
    checkMaskFor missing193 StrongPackedBucketN12A1Shard001.record193 = true := by
  decide

def missing194 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56097259377150394368
theorem maskCheck194 :
    checkMaskFor missing194 StrongPackedBucketN12A1Shard001.record194 = true := by
  decide

def missing195 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57106065693681385472
theorem maskCheck195 :
    checkMaskFor missing195 StrongPackedBucketN12A1Shard001.record195 = true := by
  decide

def missing196 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59375879905876115456
theorem maskCheck196 :
    checkMaskFor missing196 StrongPackedBucketN12A1Shard001.record196 = true := by
  decide

def missing197 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 540678452047511552
theorem maskCheck197 :
    checkMaskFor missing197 StrongPackedBucketN12A1Shard001.record197 = true := by
  decide

def missing198 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 973024016275079168
theorem maskCheck198 :
    checkMaskFor missing198 StrongPackedBucketN12A1Shard001.record198 = true := by
  decide

def missing199 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1045081610313007104
theorem maskCheck199 :
    checkMaskFor missing199 StrongPackedBucketN12A1Shard001.record199 = true := by
  decide

def missing200 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2053887926843998208
theorem maskCheck200 :
    checkMaskFor missing200 StrongPackedBucketN12A1Shard001.record200 = true := by
  decide

def missing201 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2161974317900890112
theorem maskCheck201 :
    checkMaskFor missing201 StrongPackedBucketN12A1Shard001.record201 = true := by
  decide

def missing202 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4323702139038728192
theorem maskCheck202 :
    checkMaskFor missing202 StrongPackedBucketN12A1Shard001.record202 = true := by
  decide

def missing203 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699192149605351424
theorem maskCheck203 :
    checkMaskFor missing203 StrongPackedBucketN12A1Shard001.record203 = true := by
  decide

def missing204 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18843307337681207296
theorem maskCheck204 :
    checkMaskFor missing204 StrongPackedBucketN12A1Shard001.record204 = true := by
  decide

def missing205 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18915364931719135232
theorem maskCheck205 :
    checkMaskFor missing205 StrongPackedBucketN12A1Shard001.record205 = true := by
  decide

def missing206 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19347710495946702848
theorem maskCheck206 :
    checkMaskFor missing206 StrongPackedBucketN12A1Shard001.record206 = true := by
  decide

def missing207 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19455796887003594752
theorem maskCheck207 :
    checkMaskFor missing207 StrongPackedBucketN12A1Shard001.record207 = true := by
  decide

def missing208 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20464603203534585856
theorem maskCheck208 :
    checkMaskFor missing208 StrongPackedBucketN12A1Shard001.record208 = true := by
  decide

def missing209 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37145936223314903040
theorem maskCheck209 :
    checkMaskFor missing209 StrongPackedBucketN12A1Shard001.record209 = true := by
  decide

def missing210 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37290051411390758912
theorem maskCheck210 :
    checkMaskFor missing210 StrongPackedBucketN12A1Shard001.record210 = true := by
  decide

def missing211 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 540889558280044544
theorem maskCheck211 :
    checkMaskFor missing211 StrongPackedBucketN12A1Shard001.record211 = true := by
  decide

def missing212 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 829119934431756288
theorem maskCheck212 :
    checkMaskFor missing212 StrongPackedBucketN12A1Shard001.record212 = true := by
  decide

def missing213 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1045292716545540096
theorem maskCheck213 :
    checkMaskFor missing213 StrongPackedBucketN12A1Shard001.record213 = true := by
  decide

def missing214 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1081321513564504064
theorem maskCheck214 :
    checkMaskFor missing214 StrongPackedBucketN12A1Shard001.record214 = true := by
  decide

def missing215 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1837926250962747392
theorem maskCheck215 :
    checkMaskFor missing215 StrongPackedBucketN12A1Shard001.record215 = true := by
  decide

def missing216 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1909983845000675328
theorem maskCheck216 :
    checkMaskFor missing216 StrongPackedBucketN12A1Shard001.record216 = true := by
  decide

def missing217 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1946012642019639296
theorem maskCheck217 :
    checkMaskFor missing217 StrongPackedBucketN12A1Shard001.record217 = true := by
  decide

def missing218 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2162185424133423104
theorem maskCheck218 :
    checkMaskFor missing218 StrongPackedBucketN12A1Shard001.record218 = true := by
  decide

def missing219 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4071711666138513408
theorem maskCheck219 :
    checkMaskFor missing219 StrongPackedBucketN12A1Shard001.record219 = true := by
  decide

def missing220 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4107740463157477376
theorem maskCheck220 :
    checkMaskFor missing220 StrongPackedBucketN12A1Shard001.record220 = true := by
  decide

def missing221 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4179798057195405312
theorem maskCheck221 :
    checkMaskFor missing221 StrongPackedBucketN12A1Shard001.record221 = true := by
  decide

def missing222 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8647368887546937344
theorem maskCheck222 :
    checkMaskFor missing222 StrongPackedBucketN12A1Shard001.record222 = true := by
  decide

def missing223 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699403255837884416
theorem maskCheck223 :
    checkMaskFor missing223 StrongPackedBucketN12A1Shard001.record223 = true := by
  decide

def missing224 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18915576037951668224
theorem maskCheck224 :
    checkMaskFor missing224 StrongPackedBucketN12A1Shard001.record224 = true := by
  decide

def missing225 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18951604834970632192
theorem maskCheck225 :
    checkMaskFor missing225 StrongPackedBucketN12A1Shard001.record225 = true := by
  decide

def missing226 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19131748820065452032
theorem maskCheck226 :
    checkMaskFor missing226 StrongPackedBucketN12A1Shard001.record226 = true := by
  decide

def missing227 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19203806414103379968
theorem maskCheck227 :
    checkMaskFor missing227 StrongPackedBucketN12A1Shard001.record227 = true := by
  decide

def missing228 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19239835211122343936
theorem maskCheck228 :
    checkMaskFor missing228 StrongPackedBucketN12A1Shard001.record228 = true := by
  decide

def missing229 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19456007993236127744
theorem maskCheck229 :
    checkMaskFor missing229 StrongPackedBucketN12A1Shard001.record229 = true := by
  decide

def missing230 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20212612730634371072
theorem maskCheck230 :
    checkMaskFor missing230 StrongPackedBucketN12A1Shard001.record230 = true := by
  decide

def missing231 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20248641527653335040
theorem maskCheck231 :
    checkMaskFor missing231 StrongPackedBucketN12A1Shard001.record231 = true := by
  decide

def missing232 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20320699121691262976
theorem maskCheck232 :
    checkMaskFor missing232 StrongPackedBucketN12A1Shard001.record232 = true := by
  decide

def missing233 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22482426942829101056
theorem maskCheck233 :
    checkMaskFor missing233 StrongPackedBucketN12A1Shard001.record233 = true := by
  decide

def missing234 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37146147329547436032
theorem maskCheck234 :
    checkMaskFor missing234 StrongPackedBucketN12A1Shard001.record234 = true := by
  decide

def missing235 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37362320111661219840
theorem maskCheck235 :
    checkMaskFor missing235 StrongPackedBucketN12A1Shard001.record235 = true := by
  decide

def missing236 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37398348908680183808
theorem maskCheck236 :
    checkMaskFor missing236 StrongPackedBucketN12A1Shard001.record236 = true := by
  decide

def missing237 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37578492893775003648
theorem maskCheck237 :
    checkMaskFor missing237 StrongPackedBucketN12A1Shard001.record237 = true := by
  decide

def missing238 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37650550487812931584
theorem maskCheck238 :
    checkMaskFor missing238 StrongPackedBucketN12A1Shard001.record238 = true := by
  decide

def missing239 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37686579284831895552
theorem maskCheck239 :
    checkMaskFor missing239 StrongPackedBucketN12A1Shard001.record239 = true := by
  decide

def missing240 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38659356804343922688
theorem maskCheck240 :
    checkMaskFor missing240 StrongPackedBucketN12A1Shard001.record240 = true := by
  decide

def missing241 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38695385601362886656
theorem maskCheck241 :
    checkMaskFor missing241 StrongPackedBucketN12A1Shard001.record241 = true := by
  decide

def missing242 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55448776215181131776
theorem maskCheck242 :
    checkMaskFor missing242 StrongPackedBucketN12A1Shard001.record242 = true := by
  decide

def missing243 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 541417323861377024
theorem maskCheck243 :
    checkMaskFor missing243 StrongPackedBucketN12A1Shard001.record243 = true := by
  decide

def missing244 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1045820482126872576
theorem maskCheck244 :
    checkMaskFor missing244 StrongPackedBucketN12A1Shard001.record244 = true := by
  decide

def missing245 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1406108452316512256
theorem maskCheck245 :
    checkMaskFor missing245 StrongPackedBucketN12A1Shard001.record245 = true := by
  decide

def missing246 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1622281234430296064
theorem maskCheck246 :
    checkMaskFor missing246 StrongPackedBucketN12A1Shard001.record246 = true := by
  decide

def missing247 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2162713189714755584
theorem maskCheck247 :
    checkMaskFor missing247 StrongPackedBucketN12A1Shard001.record247 = true := by
  decide

def missing248 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3567836273454350336
theorem maskCheck248 :
    checkMaskFor missing248 StrongPackedBucketN12A1Shard001.record248 = true := by
  decide

def missing249 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3639893867492278272
theorem maskCheck249 :
    checkMaskFor missing249 StrongPackedBucketN12A1Shard001.record249 = true := by
  decide

def missing250 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3892095446625026048
theorem maskCheck250 :
    checkMaskFor missing250 StrongPackedBucketN12A1Shard001.record250 = true := by
  decide

def missing251 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8107464697843810304
theorem maskCheck251 :
    checkMaskFor missing251 StrongPackedBucketN12A1Shard001.record251 = true := by
  decide

def missing252 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8215551088900702208
theorem maskCheck252 :
    checkMaskFor missing252 StrongPackedBucketN12A1Shard001.record252 = true := by
  decide

def missing253 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17294807937679622144
theorem maskCheck253 :
    checkMaskFor missing253 StrongPackedBucketN12A1Shard001.record253 = true := by
  decide

def missing254 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18699931021419216896
theorem maskCheck254 :
    checkMaskFor missing254 StrongPackedBucketN12A1Shard001.record254 = true := by
  decide

def missing255 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18916103803533000704
theorem maskCheck255 :
    checkMaskFor missing255 StrongPackedBucketN12A1Shard001.record255 = true := by
  decide

def missing128_129 : List (BitVec (edgeCount 12)) :=
  [missing128]
abbrev records128_129 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record128]
theorem aligned128_129 :
    AlignedValid 12 1 missing128_129 records128_129 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check128
    maskCheck128 AlignedValid.nil

def missing129_130 : List (BitVec (edgeCount 12)) :=
  [missing129]
abbrev records129_130 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record129]
theorem aligned129_130 :
    AlignedValid 12 1 missing129_130 records129_130 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check129
    maskCheck129 AlignedValid.nil

def missing128_130 : List (BitVec (edgeCount 12)) :=
  missing128_129 ++ missing129_130
abbrev records128_130 : List Blob :=
  records128_129 ++ records129_130
theorem aligned128_130 :
    AlignedValid 12 1 missing128_130 records128_130 :=
  aligned128_129.append aligned129_130

def missing130_131 : List (BitVec (edgeCount 12)) :=
  [missing130]
abbrev records130_131 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record130]
theorem aligned130_131 :
    AlignedValid 12 1 missing130_131 records130_131 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check130
    maskCheck130 AlignedValid.nil

def missing131_132 : List (BitVec (edgeCount 12)) :=
  [missing131]
abbrev records131_132 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record131]
theorem aligned131_132 :
    AlignedValid 12 1 missing131_132 records131_132 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check131
    maskCheck131 AlignedValid.nil

def missing130_132 : List (BitVec (edgeCount 12)) :=
  missing130_131 ++ missing131_132
abbrev records130_132 : List Blob :=
  records130_131 ++ records131_132
theorem aligned130_132 :
    AlignedValid 12 1 missing130_132 records130_132 :=
  aligned130_131.append aligned131_132

def missing128_132 : List (BitVec (edgeCount 12)) :=
  missing128_130 ++ missing130_132
abbrev records128_132 : List Blob :=
  records128_130 ++ records130_132
theorem aligned128_132 :
    AlignedValid 12 1 missing128_132 records128_132 :=
  aligned128_130.append aligned130_132

def missing132_133 : List (BitVec (edgeCount 12)) :=
  [missing132]
abbrev records132_133 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record132]
theorem aligned132_133 :
    AlignedValid 12 1 missing132_133 records132_133 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check132
    maskCheck132 AlignedValid.nil

def missing133_134 : List (BitVec (edgeCount 12)) :=
  [missing133]
abbrev records133_134 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record133]
theorem aligned133_134 :
    AlignedValid 12 1 missing133_134 records133_134 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check133
    maskCheck133 AlignedValid.nil

def missing132_134 : List (BitVec (edgeCount 12)) :=
  missing132_133 ++ missing133_134
abbrev records132_134 : List Blob :=
  records132_133 ++ records133_134
theorem aligned132_134 :
    AlignedValid 12 1 missing132_134 records132_134 :=
  aligned132_133.append aligned133_134

def missing134_135 : List (BitVec (edgeCount 12)) :=
  [missing134]
abbrev records134_135 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record134]
theorem aligned134_135 :
    AlignedValid 12 1 missing134_135 records134_135 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check134
    maskCheck134 AlignedValid.nil

def missing135_136 : List (BitVec (edgeCount 12)) :=
  [missing135]
abbrev records135_136 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record135]
theorem aligned135_136 :
    AlignedValid 12 1 missing135_136 records135_136 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check135
    maskCheck135 AlignedValid.nil

def missing134_136 : List (BitVec (edgeCount 12)) :=
  missing134_135 ++ missing135_136
abbrev records134_136 : List Blob :=
  records134_135 ++ records135_136
theorem aligned134_136 :
    AlignedValid 12 1 missing134_136 records134_136 :=
  aligned134_135.append aligned135_136

def missing132_136 : List (BitVec (edgeCount 12)) :=
  missing132_134 ++ missing134_136
abbrev records132_136 : List Blob :=
  records132_134 ++ records134_136
theorem aligned132_136 :
    AlignedValid 12 1 missing132_136 records132_136 :=
  aligned132_134.append aligned134_136

def missing128_136 : List (BitVec (edgeCount 12)) :=
  missing128_132 ++ missing132_136
abbrev records128_136 : List Blob :=
  records128_132 ++ records132_136
theorem aligned128_136 :
    AlignedValid 12 1 missing128_136 records128_136 :=
  aligned128_132.append aligned132_136

def missing136_137 : List (BitVec (edgeCount 12)) :=
  [missing136]
abbrev records136_137 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record136]
theorem aligned136_137 :
    AlignedValid 12 1 missing136_137 records136_137 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check136
    maskCheck136 AlignedValid.nil

def missing137_138 : List (BitVec (edgeCount 12)) :=
  [missing137]
abbrev records137_138 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record137]
theorem aligned137_138 :
    AlignedValid 12 1 missing137_138 records137_138 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check137
    maskCheck137 AlignedValid.nil

def missing136_138 : List (BitVec (edgeCount 12)) :=
  missing136_137 ++ missing137_138
abbrev records136_138 : List Blob :=
  records136_137 ++ records137_138
theorem aligned136_138 :
    AlignedValid 12 1 missing136_138 records136_138 :=
  aligned136_137.append aligned137_138

def missing138_139 : List (BitVec (edgeCount 12)) :=
  [missing138]
abbrev records138_139 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record138]
theorem aligned138_139 :
    AlignedValid 12 1 missing138_139 records138_139 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check138
    maskCheck138 AlignedValid.nil

def missing139_140 : List (BitVec (edgeCount 12)) :=
  [missing139]
abbrev records139_140 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record139]
theorem aligned139_140 :
    AlignedValid 12 1 missing139_140 records139_140 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check139
    maskCheck139 AlignedValid.nil

def missing138_140 : List (BitVec (edgeCount 12)) :=
  missing138_139 ++ missing139_140
abbrev records138_140 : List Blob :=
  records138_139 ++ records139_140
theorem aligned138_140 :
    AlignedValid 12 1 missing138_140 records138_140 :=
  aligned138_139.append aligned139_140

def missing136_140 : List (BitVec (edgeCount 12)) :=
  missing136_138 ++ missing138_140
abbrev records136_140 : List Blob :=
  records136_138 ++ records138_140
theorem aligned136_140 :
    AlignedValid 12 1 missing136_140 records136_140 :=
  aligned136_138.append aligned138_140

def missing140_141 : List (BitVec (edgeCount 12)) :=
  [missing140]
abbrev records140_141 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record140]
theorem aligned140_141 :
    AlignedValid 12 1 missing140_141 records140_141 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check140
    maskCheck140 AlignedValid.nil

def missing141_142 : List (BitVec (edgeCount 12)) :=
  [missing141]
abbrev records141_142 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record141]
theorem aligned141_142 :
    AlignedValid 12 1 missing141_142 records141_142 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check141
    maskCheck141 AlignedValid.nil

def missing140_142 : List (BitVec (edgeCount 12)) :=
  missing140_141 ++ missing141_142
abbrev records140_142 : List Blob :=
  records140_141 ++ records141_142
theorem aligned140_142 :
    AlignedValid 12 1 missing140_142 records140_142 :=
  aligned140_141.append aligned141_142

def missing142_143 : List (BitVec (edgeCount 12)) :=
  [missing142]
abbrev records142_143 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record142]
theorem aligned142_143 :
    AlignedValid 12 1 missing142_143 records142_143 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check142
    maskCheck142 AlignedValid.nil

def missing143_144 : List (BitVec (edgeCount 12)) :=
  [missing143]
abbrev records143_144 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record143]
theorem aligned143_144 :
    AlignedValid 12 1 missing143_144 records143_144 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check143
    maskCheck143 AlignedValid.nil

def missing142_144 : List (BitVec (edgeCount 12)) :=
  missing142_143 ++ missing143_144
abbrev records142_144 : List Blob :=
  records142_143 ++ records143_144
theorem aligned142_144 :
    AlignedValid 12 1 missing142_144 records142_144 :=
  aligned142_143.append aligned143_144

def missing140_144 : List (BitVec (edgeCount 12)) :=
  missing140_142 ++ missing142_144
abbrev records140_144 : List Blob :=
  records140_142 ++ records142_144
theorem aligned140_144 :
    AlignedValid 12 1 missing140_144 records140_144 :=
  aligned140_142.append aligned142_144

def missing136_144 : List (BitVec (edgeCount 12)) :=
  missing136_140 ++ missing140_144
abbrev records136_144 : List Blob :=
  records136_140 ++ records140_144
theorem aligned136_144 :
    AlignedValid 12 1 missing136_144 records136_144 :=
  aligned136_140.append aligned140_144

def missing128_144 : List (BitVec (edgeCount 12)) :=
  missing128_136 ++ missing136_144
abbrev records128_144 : List Blob :=
  records128_136 ++ records136_144
theorem aligned128_144 :
    AlignedValid 12 1 missing128_144 records128_144 :=
  aligned128_136.append aligned136_144

def missing144_145 : List (BitVec (edgeCount 12)) :=
  [missing144]
abbrev records144_145 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record144]
theorem aligned144_145 :
    AlignedValid 12 1 missing144_145 records144_145 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check144
    maskCheck144 AlignedValid.nil

def missing145_146 : List (BitVec (edgeCount 12)) :=
  [missing145]
abbrev records145_146 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record145]
theorem aligned145_146 :
    AlignedValid 12 1 missing145_146 records145_146 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check145
    maskCheck145 AlignedValid.nil

def missing144_146 : List (BitVec (edgeCount 12)) :=
  missing144_145 ++ missing145_146
abbrev records144_146 : List Blob :=
  records144_145 ++ records145_146
theorem aligned144_146 :
    AlignedValid 12 1 missing144_146 records144_146 :=
  aligned144_145.append aligned145_146

def missing146_147 : List (BitVec (edgeCount 12)) :=
  [missing146]
abbrev records146_147 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record146]
theorem aligned146_147 :
    AlignedValid 12 1 missing146_147 records146_147 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check146
    maskCheck146 AlignedValid.nil

def missing147_148 : List (BitVec (edgeCount 12)) :=
  [missing147]
abbrev records147_148 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record147]
theorem aligned147_148 :
    AlignedValid 12 1 missing147_148 records147_148 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check147
    maskCheck147 AlignedValid.nil

def missing146_148 : List (BitVec (edgeCount 12)) :=
  missing146_147 ++ missing147_148
abbrev records146_148 : List Blob :=
  records146_147 ++ records147_148
theorem aligned146_148 :
    AlignedValid 12 1 missing146_148 records146_148 :=
  aligned146_147.append aligned147_148

def missing144_148 : List (BitVec (edgeCount 12)) :=
  missing144_146 ++ missing146_148
abbrev records144_148 : List Blob :=
  records144_146 ++ records146_148
theorem aligned144_148 :
    AlignedValid 12 1 missing144_148 records144_148 :=
  aligned144_146.append aligned146_148

def missing148_149 : List (BitVec (edgeCount 12)) :=
  [missing148]
abbrev records148_149 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record148]
theorem aligned148_149 :
    AlignedValid 12 1 missing148_149 records148_149 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check148
    maskCheck148 AlignedValid.nil

def missing149_150 : List (BitVec (edgeCount 12)) :=
  [missing149]
abbrev records149_150 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record149]
theorem aligned149_150 :
    AlignedValid 12 1 missing149_150 records149_150 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check149
    maskCheck149 AlignedValid.nil

def missing148_150 : List (BitVec (edgeCount 12)) :=
  missing148_149 ++ missing149_150
abbrev records148_150 : List Blob :=
  records148_149 ++ records149_150
theorem aligned148_150 :
    AlignedValid 12 1 missing148_150 records148_150 :=
  aligned148_149.append aligned149_150

def missing150_151 : List (BitVec (edgeCount 12)) :=
  [missing150]
abbrev records150_151 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record150]
theorem aligned150_151 :
    AlignedValid 12 1 missing150_151 records150_151 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check150
    maskCheck150 AlignedValid.nil

def missing151_152 : List (BitVec (edgeCount 12)) :=
  [missing151]
abbrev records151_152 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record151]
theorem aligned151_152 :
    AlignedValid 12 1 missing151_152 records151_152 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check151
    maskCheck151 AlignedValid.nil

def missing150_152 : List (BitVec (edgeCount 12)) :=
  missing150_151 ++ missing151_152
abbrev records150_152 : List Blob :=
  records150_151 ++ records151_152
theorem aligned150_152 :
    AlignedValid 12 1 missing150_152 records150_152 :=
  aligned150_151.append aligned151_152

def missing148_152 : List (BitVec (edgeCount 12)) :=
  missing148_150 ++ missing150_152
abbrev records148_152 : List Blob :=
  records148_150 ++ records150_152
theorem aligned148_152 :
    AlignedValid 12 1 missing148_152 records148_152 :=
  aligned148_150.append aligned150_152

def missing144_152 : List (BitVec (edgeCount 12)) :=
  missing144_148 ++ missing148_152
abbrev records144_152 : List Blob :=
  records144_148 ++ records148_152
theorem aligned144_152 :
    AlignedValid 12 1 missing144_152 records144_152 :=
  aligned144_148.append aligned148_152

def missing152_153 : List (BitVec (edgeCount 12)) :=
  [missing152]
abbrev records152_153 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record152]
theorem aligned152_153 :
    AlignedValid 12 1 missing152_153 records152_153 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check152
    maskCheck152 AlignedValid.nil

def missing153_154 : List (BitVec (edgeCount 12)) :=
  [missing153]
abbrev records153_154 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record153]
theorem aligned153_154 :
    AlignedValid 12 1 missing153_154 records153_154 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check153
    maskCheck153 AlignedValid.nil

def missing152_154 : List (BitVec (edgeCount 12)) :=
  missing152_153 ++ missing153_154
abbrev records152_154 : List Blob :=
  records152_153 ++ records153_154
theorem aligned152_154 :
    AlignedValid 12 1 missing152_154 records152_154 :=
  aligned152_153.append aligned153_154

def missing154_155 : List (BitVec (edgeCount 12)) :=
  [missing154]
abbrev records154_155 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record154]
theorem aligned154_155 :
    AlignedValid 12 1 missing154_155 records154_155 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check154
    maskCheck154 AlignedValid.nil

def missing155_156 : List (BitVec (edgeCount 12)) :=
  [missing155]
abbrev records155_156 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record155]
theorem aligned155_156 :
    AlignedValid 12 1 missing155_156 records155_156 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check155
    maskCheck155 AlignedValid.nil

def missing154_156 : List (BitVec (edgeCount 12)) :=
  missing154_155 ++ missing155_156
abbrev records154_156 : List Blob :=
  records154_155 ++ records155_156
theorem aligned154_156 :
    AlignedValid 12 1 missing154_156 records154_156 :=
  aligned154_155.append aligned155_156

def missing152_156 : List (BitVec (edgeCount 12)) :=
  missing152_154 ++ missing154_156
abbrev records152_156 : List Blob :=
  records152_154 ++ records154_156
theorem aligned152_156 :
    AlignedValid 12 1 missing152_156 records152_156 :=
  aligned152_154.append aligned154_156

def missing156_157 : List (BitVec (edgeCount 12)) :=
  [missing156]
abbrev records156_157 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record156]
theorem aligned156_157 :
    AlignedValid 12 1 missing156_157 records156_157 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check156
    maskCheck156 AlignedValid.nil

def missing157_158 : List (BitVec (edgeCount 12)) :=
  [missing157]
abbrev records157_158 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record157]
theorem aligned157_158 :
    AlignedValid 12 1 missing157_158 records157_158 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check157
    maskCheck157 AlignedValid.nil

def missing156_158 : List (BitVec (edgeCount 12)) :=
  missing156_157 ++ missing157_158
abbrev records156_158 : List Blob :=
  records156_157 ++ records157_158
theorem aligned156_158 :
    AlignedValid 12 1 missing156_158 records156_158 :=
  aligned156_157.append aligned157_158

def missing158_159 : List (BitVec (edgeCount 12)) :=
  [missing158]
abbrev records158_159 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record158]
theorem aligned158_159 :
    AlignedValid 12 1 missing158_159 records158_159 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check158
    maskCheck158 AlignedValid.nil

def missing159_160 : List (BitVec (edgeCount 12)) :=
  [missing159]
abbrev records159_160 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record159]
theorem aligned159_160 :
    AlignedValid 12 1 missing159_160 records159_160 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check159
    maskCheck159 AlignedValid.nil

def missing158_160 : List (BitVec (edgeCount 12)) :=
  missing158_159 ++ missing159_160
abbrev records158_160 : List Blob :=
  records158_159 ++ records159_160
theorem aligned158_160 :
    AlignedValid 12 1 missing158_160 records158_160 :=
  aligned158_159.append aligned159_160

def missing156_160 : List (BitVec (edgeCount 12)) :=
  missing156_158 ++ missing158_160
abbrev records156_160 : List Blob :=
  records156_158 ++ records158_160
theorem aligned156_160 :
    AlignedValid 12 1 missing156_160 records156_160 :=
  aligned156_158.append aligned158_160

def missing152_160 : List (BitVec (edgeCount 12)) :=
  missing152_156 ++ missing156_160
abbrev records152_160 : List Blob :=
  records152_156 ++ records156_160
theorem aligned152_160 :
    AlignedValid 12 1 missing152_160 records152_160 :=
  aligned152_156.append aligned156_160

def missing144_160 : List (BitVec (edgeCount 12)) :=
  missing144_152 ++ missing152_160
abbrev records144_160 : List Blob :=
  records144_152 ++ records152_160
theorem aligned144_160 :
    AlignedValid 12 1 missing144_160 records144_160 :=
  aligned144_152.append aligned152_160

def missing128_160 : List (BitVec (edgeCount 12)) :=
  missing128_144 ++ missing144_160
abbrev records128_160 : List Blob :=
  records128_144 ++ records144_160
theorem aligned128_160 :
    AlignedValid 12 1 missing128_160 records128_160 :=
  aligned128_144.append aligned144_160

def missing160_161 : List (BitVec (edgeCount 12)) :=
  [missing160]
abbrev records160_161 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record160]
theorem aligned160_161 :
    AlignedValid 12 1 missing160_161 records160_161 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check160
    maskCheck160 AlignedValid.nil

def missing161_162 : List (BitVec (edgeCount 12)) :=
  [missing161]
abbrev records161_162 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record161]
theorem aligned161_162 :
    AlignedValid 12 1 missing161_162 records161_162 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check161
    maskCheck161 AlignedValid.nil

def missing160_162 : List (BitVec (edgeCount 12)) :=
  missing160_161 ++ missing161_162
abbrev records160_162 : List Blob :=
  records160_161 ++ records161_162
theorem aligned160_162 :
    AlignedValid 12 1 missing160_162 records160_162 :=
  aligned160_161.append aligned161_162

def missing162_163 : List (BitVec (edgeCount 12)) :=
  [missing162]
abbrev records162_163 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record162]
theorem aligned162_163 :
    AlignedValid 12 1 missing162_163 records162_163 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check162
    maskCheck162 AlignedValid.nil

def missing163_164 : List (BitVec (edgeCount 12)) :=
  [missing163]
abbrev records163_164 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record163]
theorem aligned163_164 :
    AlignedValid 12 1 missing163_164 records163_164 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check163
    maskCheck163 AlignedValid.nil

def missing162_164 : List (BitVec (edgeCount 12)) :=
  missing162_163 ++ missing163_164
abbrev records162_164 : List Blob :=
  records162_163 ++ records163_164
theorem aligned162_164 :
    AlignedValid 12 1 missing162_164 records162_164 :=
  aligned162_163.append aligned163_164

def missing160_164 : List (BitVec (edgeCount 12)) :=
  missing160_162 ++ missing162_164
abbrev records160_164 : List Blob :=
  records160_162 ++ records162_164
theorem aligned160_164 :
    AlignedValid 12 1 missing160_164 records160_164 :=
  aligned160_162.append aligned162_164

def missing164_165 : List (BitVec (edgeCount 12)) :=
  [missing164]
abbrev records164_165 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record164]
theorem aligned164_165 :
    AlignedValid 12 1 missing164_165 records164_165 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check164
    maskCheck164 AlignedValid.nil

def missing165_166 : List (BitVec (edgeCount 12)) :=
  [missing165]
abbrev records165_166 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record165]
theorem aligned165_166 :
    AlignedValid 12 1 missing165_166 records165_166 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check165
    maskCheck165 AlignedValid.nil

def missing164_166 : List (BitVec (edgeCount 12)) :=
  missing164_165 ++ missing165_166
abbrev records164_166 : List Blob :=
  records164_165 ++ records165_166
theorem aligned164_166 :
    AlignedValid 12 1 missing164_166 records164_166 :=
  aligned164_165.append aligned165_166

def missing166_167 : List (BitVec (edgeCount 12)) :=
  [missing166]
abbrev records166_167 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record166]
theorem aligned166_167 :
    AlignedValid 12 1 missing166_167 records166_167 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check166
    maskCheck166 AlignedValid.nil

def missing167_168 : List (BitVec (edgeCount 12)) :=
  [missing167]
abbrev records167_168 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record167]
theorem aligned167_168 :
    AlignedValid 12 1 missing167_168 records167_168 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check167
    maskCheck167 AlignedValid.nil

def missing166_168 : List (BitVec (edgeCount 12)) :=
  missing166_167 ++ missing167_168
abbrev records166_168 : List Blob :=
  records166_167 ++ records167_168
theorem aligned166_168 :
    AlignedValid 12 1 missing166_168 records166_168 :=
  aligned166_167.append aligned167_168

def missing164_168 : List (BitVec (edgeCount 12)) :=
  missing164_166 ++ missing166_168
abbrev records164_168 : List Blob :=
  records164_166 ++ records166_168
theorem aligned164_168 :
    AlignedValid 12 1 missing164_168 records164_168 :=
  aligned164_166.append aligned166_168

def missing160_168 : List (BitVec (edgeCount 12)) :=
  missing160_164 ++ missing164_168
abbrev records160_168 : List Blob :=
  records160_164 ++ records164_168
theorem aligned160_168 :
    AlignedValid 12 1 missing160_168 records160_168 :=
  aligned160_164.append aligned164_168

def missing168_169 : List (BitVec (edgeCount 12)) :=
  [missing168]
abbrev records168_169 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record168]
theorem aligned168_169 :
    AlignedValid 12 1 missing168_169 records168_169 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check168
    maskCheck168 AlignedValid.nil

def missing169_170 : List (BitVec (edgeCount 12)) :=
  [missing169]
abbrev records169_170 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record169]
theorem aligned169_170 :
    AlignedValid 12 1 missing169_170 records169_170 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check169
    maskCheck169 AlignedValid.nil

def missing168_170 : List (BitVec (edgeCount 12)) :=
  missing168_169 ++ missing169_170
abbrev records168_170 : List Blob :=
  records168_169 ++ records169_170
theorem aligned168_170 :
    AlignedValid 12 1 missing168_170 records168_170 :=
  aligned168_169.append aligned169_170

def missing170_171 : List (BitVec (edgeCount 12)) :=
  [missing170]
abbrev records170_171 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record170]
theorem aligned170_171 :
    AlignedValid 12 1 missing170_171 records170_171 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check170
    maskCheck170 AlignedValid.nil

def missing171_172 : List (BitVec (edgeCount 12)) :=
  [missing171]
abbrev records171_172 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record171]
theorem aligned171_172 :
    AlignedValid 12 1 missing171_172 records171_172 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check171
    maskCheck171 AlignedValid.nil

def missing170_172 : List (BitVec (edgeCount 12)) :=
  missing170_171 ++ missing171_172
abbrev records170_172 : List Blob :=
  records170_171 ++ records171_172
theorem aligned170_172 :
    AlignedValid 12 1 missing170_172 records170_172 :=
  aligned170_171.append aligned171_172

def missing168_172 : List (BitVec (edgeCount 12)) :=
  missing168_170 ++ missing170_172
abbrev records168_172 : List Blob :=
  records168_170 ++ records170_172
theorem aligned168_172 :
    AlignedValid 12 1 missing168_172 records168_172 :=
  aligned168_170.append aligned170_172

def missing172_173 : List (BitVec (edgeCount 12)) :=
  [missing172]
abbrev records172_173 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record172]
theorem aligned172_173 :
    AlignedValid 12 1 missing172_173 records172_173 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check172
    maskCheck172 AlignedValid.nil

def missing173_174 : List (BitVec (edgeCount 12)) :=
  [missing173]
abbrev records173_174 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record173]
theorem aligned173_174 :
    AlignedValid 12 1 missing173_174 records173_174 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check173
    maskCheck173 AlignedValid.nil

def missing172_174 : List (BitVec (edgeCount 12)) :=
  missing172_173 ++ missing173_174
abbrev records172_174 : List Blob :=
  records172_173 ++ records173_174
theorem aligned172_174 :
    AlignedValid 12 1 missing172_174 records172_174 :=
  aligned172_173.append aligned173_174

def missing174_175 : List (BitVec (edgeCount 12)) :=
  [missing174]
abbrev records174_175 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record174]
theorem aligned174_175 :
    AlignedValid 12 1 missing174_175 records174_175 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check174
    maskCheck174 AlignedValid.nil

def missing175_176 : List (BitVec (edgeCount 12)) :=
  [missing175]
abbrev records175_176 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record175]
theorem aligned175_176 :
    AlignedValid 12 1 missing175_176 records175_176 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check175
    maskCheck175 AlignedValid.nil

def missing174_176 : List (BitVec (edgeCount 12)) :=
  missing174_175 ++ missing175_176
abbrev records174_176 : List Blob :=
  records174_175 ++ records175_176
theorem aligned174_176 :
    AlignedValid 12 1 missing174_176 records174_176 :=
  aligned174_175.append aligned175_176

def missing172_176 : List (BitVec (edgeCount 12)) :=
  missing172_174 ++ missing174_176
abbrev records172_176 : List Blob :=
  records172_174 ++ records174_176
theorem aligned172_176 :
    AlignedValid 12 1 missing172_176 records172_176 :=
  aligned172_174.append aligned174_176

def missing168_176 : List (BitVec (edgeCount 12)) :=
  missing168_172 ++ missing172_176
abbrev records168_176 : List Blob :=
  records168_172 ++ records172_176
theorem aligned168_176 :
    AlignedValid 12 1 missing168_176 records168_176 :=
  aligned168_172.append aligned172_176

def missing160_176 : List (BitVec (edgeCount 12)) :=
  missing160_168 ++ missing168_176
abbrev records160_176 : List Blob :=
  records160_168 ++ records168_176
theorem aligned160_176 :
    AlignedValid 12 1 missing160_176 records160_176 :=
  aligned160_168.append aligned168_176

def missing176_177 : List (BitVec (edgeCount 12)) :=
  [missing176]
abbrev records176_177 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record176]
theorem aligned176_177 :
    AlignedValid 12 1 missing176_177 records176_177 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check176
    maskCheck176 AlignedValid.nil

def missing177_178 : List (BitVec (edgeCount 12)) :=
  [missing177]
abbrev records177_178 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record177]
theorem aligned177_178 :
    AlignedValid 12 1 missing177_178 records177_178 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check177
    maskCheck177 AlignedValid.nil

def missing176_178 : List (BitVec (edgeCount 12)) :=
  missing176_177 ++ missing177_178
abbrev records176_178 : List Blob :=
  records176_177 ++ records177_178
theorem aligned176_178 :
    AlignedValid 12 1 missing176_178 records176_178 :=
  aligned176_177.append aligned177_178

def missing178_179 : List (BitVec (edgeCount 12)) :=
  [missing178]
abbrev records178_179 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record178]
theorem aligned178_179 :
    AlignedValid 12 1 missing178_179 records178_179 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check178
    maskCheck178 AlignedValid.nil

def missing179_180 : List (BitVec (edgeCount 12)) :=
  [missing179]
abbrev records179_180 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record179]
theorem aligned179_180 :
    AlignedValid 12 1 missing179_180 records179_180 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check179
    maskCheck179 AlignedValid.nil

def missing178_180 : List (BitVec (edgeCount 12)) :=
  missing178_179 ++ missing179_180
abbrev records178_180 : List Blob :=
  records178_179 ++ records179_180
theorem aligned178_180 :
    AlignedValid 12 1 missing178_180 records178_180 :=
  aligned178_179.append aligned179_180

def missing176_180 : List (BitVec (edgeCount 12)) :=
  missing176_178 ++ missing178_180
abbrev records176_180 : List Blob :=
  records176_178 ++ records178_180
theorem aligned176_180 :
    AlignedValid 12 1 missing176_180 records176_180 :=
  aligned176_178.append aligned178_180

def missing180_181 : List (BitVec (edgeCount 12)) :=
  [missing180]
abbrev records180_181 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record180]
theorem aligned180_181 :
    AlignedValid 12 1 missing180_181 records180_181 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check180
    maskCheck180 AlignedValid.nil

def missing181_182 : List (BitVec (edgeCount 12)) :=
  [missing181]
abbrev records181_182 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record181]
theorem aligned181_182 :
    AlignedValid 12 1 missing181_182 records181_182 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check181
    maskCheck181 AlignedValid.nil

def missing180_182 : List (BitVec (edgeCount 12)) :=
  missing180_181 ++ missing181_182
abbrev records180_182 : List Blob :=
  records180_181 ++ records181_182
theorem aligned180_182 :
    AlignedValid 12 1 missing180_182 records180_182 :=
  aligned180_181.append aligned181_182

def missing182_183 : List (BitVec (edgeCount 12)) :=
  [missing182]
abbrev records182_183 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record182]
theorem aligned182_183 :
    AlignedValid 12 1 missing182_183 records182_183 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check182
    maskCheck182 AlignedValid.nil

def missing183_184 : List (BitVec (edgeCount 12)) :=
  [missing183]
abbrev records183_184 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record183]
theorem aligned183_184 :
    AlignedValid 12 1 missing183_184 records183_184 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check183
    maskCheck183 AlignedValid.nil

def missing182_184 : List (BitVec (edgeCount 12)) :=
  missing182_183 ++ missing183_184
abbrev records182_184 : List Blob :=
  records182_183 ++ records183_184
theorem aligned182_184 :
    AlignedValid 12 1 missing182_184 records182_184 :=
  aligned182_183.append aligned183_184

def missing180_184 : List (BitVec (edgeCount 12)) :=
  missing180_182 ++ missing182_184
abbrev records180_184 : List Blob :=
  records180_182 ++ records182_184
theorem aligned180_184 :
    AlignedValid 12 1 missing180_184 records180_184 :=
  aligned180_182.append aligned182_184

def missing176_184 : List (BitVec (edgeCount 12)) :=
  missing176_180 ++ missing180_184
abbrev records176_184 : List Blob :=
  records176_180 ++ records180_184
theorem aligned176_184 :
    AlignedValid 12 1 missing176_184 records176_184 :=
  aligned176_180.append aligned180_184

def missing184_185 : List (BitVec (edgeCount 12)) :=
  [missing184]
abbrev records184_185 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record184]
theorem aligned184_185 :
    AlignedValid 12 1 missing184_185 records184_185 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check184
    maskCheck184 AlignedValid.nil

def missing185_186 : List (BitVec (edgeCount 12)) :=
  [missing185]
abbrev records185_186 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record185]
theorem aligned185_186 :
    AlignedValid 12 1 missing185_186 records185_186 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check185
    maskCheck185 AlignedValid.nil

def missing184_186 : List (BitVec (edgeCount 12)) :=
  missing184_185 ++ missing185_186
abbrev records184_186 : List Blob :=
  records184_185 ++ records185_186
theorem aligned184_186 :
    AlignedValid 12 1 missing184_186 records184_186 :=
  aligned184_185.append aligned185_186

def missing186_187 : List (BitVec (edgeCount 12)) :=
  [missing186]
abbrev records186_187 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record186]
theorem aligned186_187 :
    AlignedValid 12 1 missing186_187 records186_187 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check186
    maskCheck186 AlignedValid.nil

def missing187_188 : List (BitVec (edgeCount 12)) :=
  [missing187]
abbrev records187_188 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record187]
theorem aligned187_188 :
    AlignedValid 12 1 missing187_188 records187_188 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check187
    maskCheck187 AlignedValid.nil

def missing186_188 : List (BitVec (edgeCount 12)) :=
  missing186_187 ++ missing187_188
abbrev records186_188 : List Blob :=
  records186_187 ++ records187_188
theorem aligned186_188 :
    AlignedValid 12 1 missing186_188 records186_188 :=
  aligned186_187.append aligned187_188

def missing184_188 : List (BitVec (edgeCount 12)) :=
  missing184_186 ++ missing186_188
abbrev records184_188 : List Blob :=
  records184_186 ++ records186_188
theorem aligned184_188 :
    AlignedValid 12 1 missing184_188 records184_188 :=
  aligned184_186.append aligned186_188

def missing188_189 : List (BitVec (edgeCount 12)) :=
  [missing188]
abbrev records188_189 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record188]
theorem aligned188_189 :
    AlignedValid 12 1 missing188_189 records188_189 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check188
    maskCheck188 AlignedValid.nil

def missing189_190 : List (BitVec (edgeCount 12)) :=
  [missing189]
abbrev records189_190 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record189]
theorem aligned189_190 :
    AlignedValid 12 1 missing189_190 records189_190 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check189
    maskCheck189 AlignedValid.nil

def missing188_190 : List (BitVec (edgeCount 12)) :=
  missing188_189 ++ missing189_190
abbrev records188_190 : List Blob :=
  records188_189 ++ records189_190
theorem aligned188_190 :
    AlignedValid 12 1 missing188_190 records188_190 :=
  aligned188_189.append aligned189_190

def missing190_191 : List (BitVec (edgeCount 12)) :=
  [missing190]
abbrev records190_191 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record190]
theorem aligned190_191 :
    AlignedValid 12 1 missing190_191 records190_191 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check190
    maskCheck190 AlignedValid.nil

def missing191_192 : List (BitVec (edgeCount 12)) :=
  [missing191]
abbrev records191_192 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record191]
theorem aligned191_192 :
    AlignedValid 12 1 missing191_192 records191_192 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check191
    maskCheck191 AlignedValid.nil

def missing190_192 : List (BitVec (edgeCount 12)) :=
  missing190_191 ++ missing191_192
abbrev records190_192 : List Blob :=
  records190_191 ++ records191_192
theorem aligned190_192 :
    AlignedValid 12 1 missing190_192 records190_192 :=
  aligned190_191.append aligned191_192

def missing188_192 : List (BitVec (edgeCount 12)) :=
  missing188_190 ++ missing190_192
abbrev records188_192 : List Blob :=
  records188_190 ++ records190_192
theorem aligned188_192 :
    AlignedValid 12 1 missing188_192 records188_192 :=
  aligned188_190.append aligned190_192

def missing184_192 : List (BitVec (edgeCount 12)) :=
  missing184_188 ++ missing188_192
abbrev records184_192 : List Blob :=
  records184_188 ++ records188_192
theorem aligned184_192 :
    AlignedValid 12 1 missing184_192 records184_192 :=
  aligned184_188.append aligned188_192

def missing176_192 : List (BitVec (edgeCount 12)) :=
  missing176_184 ++ missing184_192
abbrev records176_192 : List Blob :=
  records176_184 ++ records184_192
theorem aligned176_192 :
    AlignedValid 12 1 missing176_192 records176_192 :=
  aligned176_184.append aligned184_192

def missing160_192 : List (BitVec (edgeCount 12)) :=
  missing160_176 ++ missing176_192
abbrev records160_192 : List Blob :=
  records160_176 ++ records176_192
theorem aligned160_192 :
    AlignedValid 12 1 missing160_192 records160_192 :=
  aligned160_176.append aligned176_192

def missing128_192 : List (BitVec (edgeCount 12)) :=
  missing128_160 ++ missing160_192
abbrev records128_192 : List Blob :=
  records128_160 ++ records160_192
theorem aligned128_192 :
    AlignedValid 12 1 missing128_192 records128_192 :=
  aligned128_160.append aligned160_192

def missing192_193 : List (BitVec (edgeCount 12)) :=
  [missing192]
abbrev records192_193 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record192]
theorem aligned192_193 :
    AlignedValid 12 1 missing192_193 records192_193 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check192
    maskCheck192 AlignedValid.nil

def missing193_194 : List (BitVec (edgeCount 12)) :=
  [missing193]
abbrev records193_194 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record193]
theorem aligned193_194 :
    AlignedValid 12 1 missing193_194 records193_194 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check193
    maskCheck193 AlignedValid.nil

def missing192_194 : List (BitVec (edgeCount 12)) :=
  missing192_193 ++ missing193_194
abbrev records192_194 : List Blob :=
  records192_193 ++ records193_194
theorem aligned192_194 :
    AlignedValid 12 1 missing192_194 records192_194 :=
  aligned192_193.append aligned193_194

def missing194_195 : List (BitVec (edgeCount 12)) :=
  [missing194]
abbrev records194_195 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record194]
theorem aligned194_195 :
    AlignedValid 12 1 missing194_195 records194_195 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check194
    maskCheck194 AlignedValid.nil

def missing195_196 : List (BitVec (edgeCount 12)) :=
  [missing195]
abbrev records195_196 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record195]
theorem aligned195_196 :
    AlignedValid 12 1 missing195_196 records195_196 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check195
    maskCheck195 AlignedValid.nil

def missing194_196 : List (BitVec (edgeCount 12)) :=
  missing194_195 ++ missing195_196
abbrev records194_196 : List Blob :=
  records194_195 ++ records195_196
theorem aligned194_196 :
    AlignedValid 12 1 missing194_196 records194_196 :=
  aligned194_195.append aligned195_196

def missing192_196 : List (BitVec (edgeCount 12)) :=
  missing192_194 ++ missing194_196
abbrev records192_196 : List Blob :=
  records192_194 ++ records194_196
theorem aligned192_196 :
    AlignedValid 12 1 missing192_196 records192_196 :=
  aligned192_194.append aligned194_196

def missing196_197 : List (BitVec (edgeCount 12)) :=
  [missing196]
abbrev records196_197 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record196]
theorem aligned196_197 :
    AlignedValid 12 1 missing196_197 records196_197 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check196
    maskCheck196 AlignedValid.nil

def missing197_198 : List (BitVec (edgeCount 12)) :=
  [missing197]
abbrev records197_198 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record197]
theorem aligned197_198 :
    AlignedValid 12 1 missing197_198 records197_198 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check197
    maskCheck197 AlignedValid.nil

def missing196_198 : List (BitVec (edgeCount 12)) :=
  missing196_197 ++ missing197_198
abbrev records196_198 : List Blob :=
  records196_197 ++ records197_198
theorem aligned196_198 :
    AlignedValid 12 1 missing196_198 records196_198 :=
  aligned196_197.append aligned197_198

def missing198_199 : List (BitVec (edgeCount 12)) :=
  [missing198]
abbrev records198_199 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record198]
theorem aligned198_199 :
    AlignedValid 12 1 missing198_199 records198_199 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check198
    maskCheck198 AlignedValid.nil

def missing199_200 : List (BitVec (edgeCount 12)) :=
  [missing199]
abbrev records199_200 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record199]
theorem aligned199_200 :
    AlignedValid 12 1 missing199_200 records199_200 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check199
    maskCheck199 AlignedValid.nil

def missing198_200 : List (BitVec (edgeCount 12)) :=
  missing198_199 ++ missing199_200
abbrev records198_200 : List Blob :=
  records198_199 ++ records199_200
theorem aligned198_200 :
    AlignedValid 12 1 missing198_200 records198_200 :=
  aligned198_199.append aligned199_200

def missing196_200 : List (BitVec (edgeCount 12)) :=
  missing196_198 ++ missing198_200
abbrev records196_200 : List Blob :=
  records196_198 ++ records198_200
theorem aligned196_200 :
    AlignedValid 12 1 missing196_200 records196_200 :=
  aligned196_198.append aligned198_200

def missing192_200 : List (BitVec (edgeCount 12)) :=
  missing192_196 ++ missing196_200
abbrev records192_200 : List Blob :=
  records192_196 ++ records196_200
theorem aligned192_200 :
    AlignedValid 12 1 missing192_200 records192_200 :=
  aligned192_196.append aligned196_200

def missing200_201 : List (BitVec (edgeCount 12)) :=
  [missing200]
abbrev records200_201 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record200]
theorem aligned200_201 :
    AlignedValid 12 1 missing200_201 records200_201 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check200
    maskCheck200 AlignedValid.nil

def missing201_202 : List (BitVec (edgeCount 12)) :=
  [missing201]
abbrev records201_202 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record201]
theorem aligned201_202 :
    AlignedValid 12 1 missing201_202 records201_202 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check201
    maskCheck201 AlignedValid.nil

def missing200_202 : List (BitVec (edgeCount 12)) :=
  missing200_201 ++ missing201_202
abbrev records200_202 : List Blob :=
  records200_201 ++ records201_202
theorem aligned200_202 :
    AlignedValid 12 1 missing200_202 records200_202 :=
  aligned200_201.append aligned201_202

def missing202_203 : List (BitVec (edgeCount 12)) :=
  [missing202]
abbrev records202_203 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record202]
theorem aligned202_203 :
    AlignedValid 12 1 missing202_203 records202_203 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check202
    maskCheck202 AlignedValid.nil

def missing203_204 : List (BitVec (edgeCount 12)) :=
  [missing203]
abbrev records203_204 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record203]
theorem aligned203_204 :
    AlignedValid 12 1 missing203_204 records203_204 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check203
    maskCheck203 AlignedValid.nil

def missing202_204 : List (BitVec (edgeCount 12)) :=
  missing202_203 ++ missing203_204
abbrev records202_204 : List Blob :=
  records202_203 ++ records203_204
theorem aligned202_204 :
    AlignedValid 12 1 missing202_204 records202_204 :=
  aligned202_203.append aligned203_204

def missing200_204 : List (BitVec (edgeCount 12)) :=
  missing200_202 ++ missing202_204
abbrev records200_204 : List Blob :=
  records200_202 ++ records202_204
theorem aligned200_204 :
    AlignedValid 12 1 missing200_204 records200_204 :=
  aligned200_202.append aligned202_204

def missing204_205 : List (BitVec (edgeCount 12)) :=
  [missing204]
abbrev records204_205 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record204]
theorem aligned204_205 :
    AlignedValid 12 1 missing204_205 records204_205 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check204
    maskCheck204 AlignedValid.nil

def missing205_206 : List (BitVec (edgeCount 12)) :=
  [missing205]
abbrev records205_206 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record205]
theorem aligned205_206 :
    AlignedValid 12 1 missing205_206 records205_206 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check205
    maskCheck205 AlignedValid.nil

def missing204_206 : List (BitVec (edgeCount 12)) :=
  missing204_205 ++ missing205_206
abbrev records204_206 : List Blob :=
  records204_205 ++ records205_206
theorem aligned204_206 :
    AlignedValid 12 1 missing204_206 records204_206 :=
  aligned204_205.append aligned205_206

def missing206_207 : List (BitVec (edgeCount 12)) :=
  [missing206]
abbrev records206_207 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record206]
theorem aligned206_207 :
    AlignedValid 12 1 missing206_207 records206_207 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check206
    maskCheck206 AlignedValid.nil

def missing207_208 : List (BitVec (edgeCount 12)) :=
  [missing207]
abbrev records207_208 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record207]
theorem aligned207_208 :
    AlignedValid 12 1 missing207_208 records207_208 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check207
    maskCheck207 AlignedValid.nil

def missing206_208 : List (BitVec (edgeCount 12)) :=
  missing206_207 ++ missing207_208
abbrev records206_208 : List Blob :=
  records206_207 ++ records207_208
theorem aligned206_208 :
    AlignedValid 12 1 missing206_208 records206_208 :=
  aligned206_207.append aligned207_208

def missing204_208 : List (BitVec (edgeCount 12)) :=
  missing204_206 ++ missing206_208
abbrev records204_208 : List Blob :=
  records204_206 ++ records206_208
theorem aligned204_208 :
    AlignedValid 12 1 missing204_208 records204_208 :=
  aligned204_206.append aligned206_208

def missing200_208 : List (BitVec (edgeCount 12)) :=
  missing200_204 ++ missing204_208
abbrev records200_208 : List Blob :=
  records200_204 ++ records204_208
theorem aligned200_208 :
    AlignedValid 12 1 missing200_208 records200_208 :=
  aligned200_204.append aligned204_208

def missing192_208 : List (BitVec (edgeCount 12)) :=
  missing192_200 ++ missing200_208
abbrev records192_208 : List Blob :=
  records192_200 ++ records200_208
theorem aligned192_208 :
    AlignedValid 12 1 missing192_208 records192_208 :=
  aligned192_200.append aligned200_208

def missing208_209 : List (BitVec (edgeCount 12)) :=
  [missing208]
abbrev records208_209 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record208]
theorem aligned208_209 :
    AlignedValid 12 1 missing208_209 records208_209 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check208
    maskCheck208 AlignedValid.nil

def missing209_210 : List (BitVec (edgeCount 12)) :=
  [missing209]
abbrev records209_210 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record209]
theorem aligned209_210 :
    AlignedValid 12 1 missing209_210 records209_210 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check209
    maskCheck209 AlignedValid.nil

def missing208_210 : List (BitVec (edgeCount 12)) :=
  missing208_209 ++ missing209_210
abbrev records208_210 : List Blob :=
  records208_209 ++ records209_210
theorem aligned208_210 :
    AlignedValid 12 1 missing208_210 records208_210 :=
  aligned208_209.append aligned209_210

def missing210_211 : List (BitVec (edgeCount 12)) :=
  [missing210]
abbrev records210_211 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record210]
theorem aligned210_211 :
    AlignedValid 12 1 missing210_211 records210_211 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check210
    maskCheck210 AlignedValid.nil

def missing211_212 : List (BitVec (edgeCount 12)) :=
  [missing211]
abbrev records211_212 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record211]
theorem aligned211_212 :
    AlignedValid 12 1 missing211_212 records211_212 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check211
    maskCheck211 AlignedValid.nil

def missing210_212 : List (BitVec (edgeCount 12)) :=
  missing210_211 ++ missing211_212
abbrev records210_212 : List Blob :=
  records210_211 ++ records211_212
theorem aligned210_212 :
    AlignedValid 12 1 missing210_212 records210_212 :=
  aligned210_211.append aligned211_212

def missing208_212 : List (BitVec (edgeCount 12)) :=
  missing208_210 ++ missing210_212
abbrev records208_212 : List Blob :=
  records208_210 ++ records210_212
theorem aligned208_212 :
    AlignedValid 12 1 missing208_212 records208_212 :=
  aligned208_210.append aligned210_212

def missing212_213 : List (BitVec (edgeCount 12)) :=
  [missing212]
abbrev records212_213 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record212]
theorem aligned212_213 :
    AlignedValid 12 1 missing212_213 records212_213 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check212
    maskCheck212 AlignedValid.nil

def missing213_214 : List (BitVec (edgeCount 12)) :=
  [missing213]
abbrev records213_214 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record213]
theorem aligned213_214 :
    AlignedValid 12 1 missing213_214 records213_214 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check213
    maskCheck213 AlignedValid.nil

def missing212_214 : List (BitVec (edgeCount 12)) :=
  missing212_213 ++ missing213_214
abbrev records212_214 : List Blob :=
  records212_213 ++ records213_214
theorem aligned212_214 :
    AlignedValid 12 1 missing212_214 records212_214 :=
  aligned212_213.append aligned213_214

def missing214_215 : List (BitVec (edgeCount 12)) :=
  [missing214]
abbrev records214_215 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record214]
theorem aligned214_215 :
    AlignedValid 12 1 missing214_215 records214_215 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check214
    maskCheck214 AlignedValid.nil

def missing215_216 : List (BitVec (edgeCount 12)) :=
  [missing215]
abbrev records215_216 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record215]
theorem aligned215_216 :
    AlignedValid 12 1 missing215_216 records215_216 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check215
    maskCheck215 AlignedValid.nil

def missing214_216 : List (BitVec (edgeCount 12)) :=
  missing214_215 ++ missing215_216
abbrev records214_216 : List Blob :=
  records214_215 ++ records215_216
theorem aligned214_216 :
    AlignedValid 12 1 missing214_216 records214_216 :=
  aligned214_215.append aligned215_216

def missing212_216 : List (BitVec (edgeCount 12)) :=
  missing212_214 ++ missing214_216
abbrev records212_216 : List Blob :=
  records212_214 ++ records214_216
theorem aligned212_216 :
    AlignedValid 12 1 missing212_216 records212_216 :=
  aligned212_214.append aligned214_216

def missing208_216 : List (BitVec (edgeCount 12)) :=
  missing208_212 ++ missing212_216
abbrev records208_216 : List Blob :=
  records208_212 ++ records212_216
theorem aligned208_216 :
    AlignedValid 12 1 missing208_216 records208_216 :=
  aligned208_212.append aligned212_216

def missing216_217 : List (BitVec (edgeCount 12)) :=
  [missing216]
abbrev records216_217 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record216]
theorem aligned216_217 :
    AlignedValid 12 1 missing216_217 records216_217 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check216
    maskCheck216 AlignedValid.nil

def missing217_218 : List (BitVec (edgeCount 12)) :=
  [missing217]
abbrev records217_218 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record217]
theorem aligned217_218 :
    AlignedValid 12 1 missing217_218 records217_218 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check217
    maskCheck217 AlignedValid.nil

def missing216_218 : List (BitVec (edgeCount 12)) :=
  missing216_217 ++ missing217_218
abbrev records216_218 : List Blob :=
  records216_217 ++ records217_218
theorem aligned216_218 :
    AlignedValid 12 1 missing216_218 records216_218 :=
  aligned216_217.append aligned217_218

def missing218_219 : List (BitVec (edgeCount 12)) :=
  [missing218]
abbrev records218_219 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record218]
theorem aligned218_219 :
    AlignedValid 12 1 missing218_219 records218_219 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check218
    maskCheck218 AlignedValid.nil

def missing219_220 : List (BitVec (edgeCount 12)) :=
  [missing219]
abbrev records219_220 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record219]
theorem aligned219_220 :
    AlignedValid 12 1 missing219_220 records219_220 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check219
    maskCheck219 AlignedValid.nil

def missing218_220 : List (BitVec (edgeCount 12)) :=
  missing218_219 ++ missing219_220
abbrev records218_220 : List Blob :=
  records218_219 ++ records219_220
theorem aligned218_220 :
    AlignedValid 12 1 missing218_220 records218_220 :=
  aligned218_219.append aligned219_220

def missing216_220 : List (BitVec (edgeCount 12)) :=
  missing216_218 ++ missing218_220
abbrev records216_220 : List Blob :=
  records216_218 ++ records218_220
theorem aligned216_220 :
    AlignedValid 12 1 missing216_220 records216_220 :=
  aligned216_218.append aligned218_220

def missing220_221 : List (BitVec (edgeCount 12)) :=
  [missing220]
abbrev records220_221 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record220]
theorem aligned220_221 :
    AlignedValid 12 1 missing220_221 records220_221 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check220
    maskCheck220 AlignedValid.nil

def missing221_222 : List (BitVec (edgeCount 12)) :=
  [missing221]
abbrev records221_222 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record221]
theorem aligned221_222 :
    AlignedValid 12 1 missing221_222 records221_222 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check221
    maskCheck221 AlignedValid.nil

def missing220_222 : List (BitVec (edgeCount 12)) :=
  missing220_221 ++ missing221_222
abbrev records220_222 : List Blob :=
  records220_221 ++ records221_222
theorem aligned220_222 :
    AlignedValid 12 1 missing220_222 records220_222 :=
  aligned220_221.append aligned221_222

def missing222_223 : List (BitVec (edgeCount 12)) :=
  [missing222]
abbrev records222_223 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record222]
theorem aligned222_223 :
    AlignedValid 12 1 missing222_223 records222_223 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check222
    maskCheck222 AlignedValid.nil

def missing223_224 : List (BitVec (edgeCount 12)) :=
  [missing223]
abbrev records223_224 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record223]
theorem aligned223_224 :
    AlignedValid 12 1 missing223_224 records223_224 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check223
    maskCheck223 AlignedValid.nil

def missing222_224 : List (BitVec (edgeCount 12)) :=
  missing222_223 ++ missing223_224
abbrev records222_224 : List Blob :=
  records222_223 ++ records223_224
theorem aligned222_224 :
    AlignedValid 12 1 missing222_224 records222_224 :=
  aligned222_223.append aligned223_224

def missing220_224 : List (BitVec (edgeCount 12)) :=
  missing220_222 ++ missing222_224
abbrev records220_224 : List Blob :=
  records220_222 ++ records222_224
theorem aligned220_224 :
    AlignedValid 12 1 missing220_224 records220_224 :=
  aligned220_222.append aligned222_224

def missing216_224 : List (BitVec (edgeCount 12)) :=
  missing216_220 ++ missing220_224
abbrev records216_224 : List Blob :=
  records216_220 ++ records220_224
theorem aligned216_224 :
    AlignedValid 12 1 missing216_224 records216_224 :=
  aligned216_220.append aligned220_224

def missing208_224 : List (BitVec (edgeCount 12)) :=
  missing208_216 ++ missing216_224
abbrev records208_224 : List Blob :=
  records208_216 ++ records216_224
theorem aligned208_224 :
    AlignedValid 12 1 missing208_224 records208_224 :=
  aligned208_216.append aligned216_224

def missing192_224 : List (BitVec (edgeCount 12)) :=
  missing192_208 ++ missing208_224
abbrev records192_224 : List Blob :=
  records192_208 ++ records208_224
theorem aligned192_224 :
    AlignedValid 12 1 missing192_224 records192_224 :=
  aligned192_208.append aligned208_224

def missing224_225 : List (BitVec (edgeCount 12)) :=
  [missing224]
abbrev records224_225 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record224]
theorem aligned224_225 :
    AlignedValid 12 1 missing224_225 records224_225 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check224
    maskCheck224 AlignedValid.nil

def missing225_226 : List (BitVec (edgeCount 12)) :=
  [missing225]
abbrev records225_226 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record225]
theorem aligned225_226 :
    AlignedValid 12 1 missing225_226 records225_226 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check225
    maskCheck225 AlignedValid.nil

def missing224_226 : List (BitVec (edgeCount 12)) :=
  missing224_225 ++ missing225_226
abbrev records224_226 : List Blob :=
  records224_225 ++ records225_226
theorem aligned224_226 :
    AlignedValid 12 1 missing224_226 records224_226 :=
  aligned224_225.append aligned225_226

def missing226_227 : List (BitVec (edgeCount 12)) :=
  [missing226]
abbrev records226_227 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record226]
theorem aligned226_227 :
    AlignedValid 12 1 missing226_227 records226_227 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check226
    maskCheck226 AlignedValid.nil

def missing227_228 : List (BitVec (edgeCount 12)) :=
  [missing227]
abbrev records227_228 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record227]
theorem aligned227_228 :
    AlignedValid 12 1 missing227_228 records227_228 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check227
    maskCheck227 AlignedValid.nil

def missing226_228 : List (BitVec (edgeCount 12)) :=
  missing226_227 ++ missing227_228
abbrev records226_228 : List Blob :=
  records226_227 ++ records227_228
theorem aligned226_228 :
    AlignedValid 12 1 missing226_228 records226_228 :=
  aligned226_227.append aligned227_228

def missing224_228 : List (BitVec (edgeCount 12)) :=
  missing224_226 ++ missing226_228
abbrev records224_228 : List Blob :=
  records224_226 ++ records226_228
theorem aligned224_228 :
    AlignedValid 12 1 missing224_228 records224_228 :=
  aligned224_226.append aligned226_228

def missing228_229 : List (BitVec (edgeCount 12)) :=
  [missing228]
abbrev records228_229 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record228]
theorem aligned228_229 :
    AlignedValid 12 1 missing228_229 records228_229 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check228
    maskCheck228 AlignedValid.nil

def missing229_230 : List (BitVec (edgeCount 12)) :=
  [missing229]
abbrev records229_230 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record229]
theorem aligned229_230 :
    AlignedValid 12 1 missing229_230 records229_230 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check229
    maskCheck229 AlignedValid.nil

def missing228_230 : List (BitVec (edgeCount 12)) :=
  missing228_229 ++ missing229_230
abbrev records228_230 : List Blob :=
  records228_229 ++ records229_230
theorem aligned228_230 :
    AlignedValid 12 1 missing228_230 records228_230 :=
  aligned228_229.append aligned229_230

def missing230_231 : List (BitVec (edgeCount 12)) :=
  [missing230]
abbrev records230_231 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record230]
theorem aligned230_231 :
    AlignedValid 12 1 missing230_231 records230_231 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check230
    maskCheck230 AlignedValid.nil

def missing231_232 : List (BitVec (edgeCount 12)) :=
  [missing231]
abbrev records231_232 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record231]
theorem aligned231_232 :
    AlignedValid 12 1 missing231_232 records231_232 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check231
    maskCheck231 AlignedValid.nil

def missing230_232 : List (BitVec (edgeCount 12)) :=
  missing230_231 ++ missing231_232
abbrev records230_232 : List Blob :=
  records230_231 ++ records231_232
theorem aligned230_232 :
    AlignedValid 12 1 missing230_232 records230_232 :=
  aligned230_231.append aligned231_232

def missing228_232 : List (BitVec (edgeCount 12)) :=
  missing228_230 ++ missing230_232
abbrev records228_232 : List Blob :=
  records228_230 ++ records230_232
theorem aligned228_232 :
    AlignedValid 12 1 missing228_232 records228_232 :=
  aligned228_230.append aligned230_232

def missing224_232 : List (BitVec (edgeCount 12)) :=
  missing224_228 ++ missing228_232
abbrev records224_232 : List Blob :=
  records224_228 ++ records228_232
theorem aligned224_232 :
    AlignedValid 12 1 missing224_232 records224_232 :=
  aligned224_228.append aligned228_232

def missing232_233 : List (BitVec (edgeCount 12)) :=
  [missing232]
abbrev records232_233 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record232]
theorem aligned232_233 :
    AlignedValid 12 1 missing232_233 records232_233 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check232
    maskCheck232 AlignedValid.nil

def missing233_234 : List (BitVec (edgeCount 12)) :=
  [missing233]
abbrev records233_234 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record233]
theorem aligned233_234 :
    AlignedValid 12 1 missing233_234 records233_234 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check233
    maskCheck233 AlignedValid.nil

def missing232_234 : List (BitVec (edgeCount 12)) :=
  missing232_233 ++ missing233_234
abbrev records232_234 : List Blob :=
  records232_233 ++ records233_234
theorem aligned232_234 :
    AlignedValid 12 1 missing232_234 records232_234 :=
  aligned232_233.append aligned233_234

def missing234_235 : List (BitVec (edgeCount 12)) :=
  [missing234]
abbrev records234_235 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record234]
theorem aligned234_235 :
    AlignedValid 12 1 missing234_235 records234_235 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check234
    maskCheck234 AlignedValid.nil

def missing235_236 : List (BitVec (edgeCount 12)) :=
  [missing235]
abbrev records235_236 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record235]
theorem aligned235_236 :
    AlignedValid 12 1 missing235_236 records235_236 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check235
    maskCheck235 AlignedValid.nil

def missing234_236 : List (BitVec (edgeCount 12)) :=
  missing234_235 ++ missing235_236
abbrev records234_236 : List Blob :=
  records234_235 ++ records235_236
theorem aligned234_236 :
    AlignedValid 12 1 missing234_236 records234_236 :=
  aligned234_235.append aligned235_236

def missing232_236 : List (BitVec (edgeCount 12)) :=
  missing232_234 ++ missing234_236
abbrev records232_236 : List Blob :=
  records232_234 ++ records234_236
theorem aligned232_236 :
    AlignedValid 12 1 missing232_236 records232_236 :=
  aligned232_234.append aligned234_236

def missing236_237 : List (BitVec (edgeCount 12)) :=
  [missing236]
abbrev records236_237 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record236]
theorem aligned236_237 :
    AlignedValid 12 1 missing236_237 records236_237 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check236
    maskCheck236 AlignedValid.nil

def missing237_238 : List (BitVec (edgeCount 12)) :=
  [missing237]
abbrev records237_238 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record237]
theorem aligned237_238 :
    AlignedValid 12 1 missing237_238 records237_238 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check237
    maskCheck237 AlignedValid.nil

def missing236_238 : List (BitVec (edgeCount 12)) :=
  missing236_237 ++ missing237_238
abbrev records236_238 : List Blob :=
  records236_237 ++ records237_238
theorem aligned236_238 :
    AlignedValid 12 1 missing236_238 records236_238 :=
  aligned236_237.append aligned237_238

def missing238_239 : List (BitVec (edgeCount 12)) :=
  [missing238]
abbrev records238_239 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record238]
theorem aligned238_239 :
    AlignedValid 12 1 missing238_239 records238_239 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check238
    maskCheck238 AlignedValid.nil

def missing239_240 : List (BitVec (edgeCount 12)) :=
  [missing239]
abbrev records239_240 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record239]
theorem aligned239_240 :
    AlignedValid 12 1 missing239_240 records239_240 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check239
    maskCheck239 AlignedValid.nil

def missing238_240 : List (BitVec (edgeCount 12)) :=
  missing238_239 ++ missing239_240
abbrev records238_240 : List Blob :=
  records238_239 ++ records239_240
theorem aligned238_240 :
    AlignedValid 12 1 missing238_240 records238_240 :=
  aligned238_239.append aligned239_240

def missing236_240 : List (BitVec (edgeCount 12)) :=
  missing236_238 ++ missing238_240
abbrev records236_240 : List Blob :=
  records236_238 ++ records238_240
theorem aligned236_240 :
    AlignedValid 12 1 missing236_240 records236_240 :=
  aligned236_238.append aligned238_240

def missing232_240 : List (BitVec (edgeCount 12)) :=
  missing232_236 ++ missing236_240
abbrev records232_240 : List Blob :=
  records232_236 ++ records236_240
theorem aligned232_240 :
    AlignedValid 12 1 missing232_240 records232_240 :=
  aligned232_236.append aligned236_240

def missing224_240 : List (BitVec (edgeCount 12)) :=
  missing224_232 ++ missing232_240
abbrev records224_240 : List Blob :=
  records224_232 ++ records232_240
theorem aligned224_240 :
    AlignedValid 12 1 missing224_240 records224_240 :=
  aligned224_232.append aligned232_240

def missing240_241 : List (BitVec (edgeCount 12)) :=
  [missing240]
abbrev records240_241 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record240]
theorem aligned240_241 :
    AlignedValid 12 1 missing240_241 records240_241 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check240
    maskCheck240 AlignedValid.nil

def missing241_242 : List (BitVec (edgeCount 12)) :=
  [missing241]
abbrev records241_242 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record241]
theorem aligned241_242 :
    AlignedValid 12 1 missing241_242 records241_242 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check241
    maskCheck241 AlignedValid.nil

def missing240_242 : List (BitVec (edgeCount 12)) :=
  missing240_241 ++ missing241_242
abbrev records240_242 : List Blob :=
  records240_241 ++ records241_242
theorem aligned240_242 :
    AlignedValid 12 1 missing240_242 records240_242 :=
  aligned240_241.append aligned241_242

def missing242_243 : List (BitVec (edgeCount 12)) :=
  [missing242]
abbrev records242_243 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record242]
theorem aligned242_243 :
    AlignedValid 12 1 missing242_243 records242_243 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check242
    maskCheck242 AlignedValid.nil

def missing243_244 : List (BitVec (edgeCount 12)) :=
  [missing243]
abbrev records243_244 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record243]
theorem aligned243_244 :
    AlignedValid 12 1 missing243_244 records243_244 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check243
    maskCheck243 AlignedValid.nil

def missing242_244 : List (BitVec (edgeCount 12)) :=
  missing242_243 ++ missing243_244
abbrev records242_244 : List Blob :=
  records242_243 ++ records243_244
theorem aligned242_244 :
    AlignedValid 12 1 missing242_244 records242_244 :=
  aligned242_243.append aligned243_244

def missing240_244 : List (BitVec (edgeCount 12)) :=
  missing240_242 ++ missing242_244
abbrev records240_244 : List Blob :=
  records240_242 ++ records242_244
theorem aligned240_244 :
    AlignedValid 12 1 missing240_244 records240_244 :=
  aligned240_242.append aligned242_244

def missing244_245 : List (BitVec (edgeCount 12)) :=
  [missing244]
abbrev records244_245 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record244]
theorem aligned244_245 :
    AlignedValid 12 1 missing244_245 records244_245 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check244
    maskCheck244 AlignedValid.nil

def missing245_246 : List (BitVec (edgeCount 12)) :=
  [missing245]
abbrev records245_246 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record245]
theorem aligned245_246 :
    AlignedValid 12 1 missing245_246 records245_246 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check245
    maskCheck245 AlignedValid.nil

def missing244_246 : List (BitVec (edgeCount 12)) :=
  missing244_245 ++ missing245_246
abbrev records244_246 : List Blob :=
  records244_245 ++ records245_246
theorem aligned244_246 :
    AlignedValid 12 1 missing244_246 records244_246 :=
  aligned244_245.append aligned245_246

def missing246_247 : List (BitVec (edgeCount 12)) :=
  [missing246]
abbrev records246_247 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record246]
theorem aligned246_247 :
    AlignedValid 12 1 missing246_247 records246_247 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check246
    maskCheck246 AlignedValid.nil

def missing247_248 : List (BitVec (edgeCount 12)) :=
  [missing247]
abbrev records247_248 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record247]
theorem aligned247_248 :
    AlignedValid 12 1 missing247_248 records247_248 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check247
    maskCheck247 AlignedValid.nil

def missing246_248 : List (BitVec (edgeCount 12)) :=
  missing246_247 ++ missing247_248
abbrev records246_248 : List Blob :=
  records246_247 ++ records247_248
theorem aligned246_248 :
    AlignedValid 12 1 missing246_248 records246_248 :=
  aligned246_247.append aligned247_248

def missing244_248 : List (BitVec (edgeCount 12)) :=
  missing244_246 ++ missing246_248
abbrev records244_248 : List Blob :=
  records244_246 ++ records246_248
theorem aligned244_248 :
    AlignedValid 12 1 missing244_248 records244_248 :=
  aligned244_246.append aligned246_248

def missing240_248 : List (BitVec (edgeCount 12)) :=
  missing240_244 ++ missing244_248
abbrev records240_248 : List Blob :=
  records240_244 ++ records244_248
theorem aligned240_248 :
    AlignedValid 12 1 missing240_248 records240_248 :=
  aligned240_244.append aligned244_248

def missing248_249 : List (BitVec (edgeCount 12)) :=
  [missing248]
abbrev records248_249 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record248]
theorem aligned248_249 :
    AlignedValid 12 1 missing248_249 records248_249 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check248
    maskCheck248 AlignedValid.nil

def missing249_250 : List (BitVec (edgeCount 12)) :=
  [missing249]
abbrev records249_250 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record249]
theorem aligned249_250 :
    AlignedValid 12 1 missing249_250 records249_250 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check249
    maskCheck249 AlignedValid.nil

def missing248_250 : List (BitVec (edgeCount 12)) :=
  missing248_249 ++ missing249_250
abbrev records248_250 : List Blob :=
  records248_249 ++ records249_250
theorem aligned248_250 :
    AlignedValid 12 1 missing248_250 records248_250 :=
  aligned248_249.append aligned249_250

def missing250_251 : List (BitVec (edgeCount 12)) :=
  [missing250]
abbrev records250_251 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record250]
theorem aligned250_251 :
    AlignedValid 12 1 missing250_251 records250_251 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check250
    maskCheck250 AlignedValid.nil

def missing251_252 : List (BitVec (edgeCount 12)) :=
  [missing251]
abbrev records251_252 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record251]
theorem aligned251_252 :
    AlignedValid 12 1 missing251_252 records251_252 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check251
    maskCheck251 AlignedValid.nil

def missing250_252 : List (BitVec (edgeCount 12)) :=
  missing250_251 ++ missing251_252
abbrev records250_252 : List Blob :=
  records250_251 ++ records251_252
theorem aligned250_252 :
    AlignedValid 12 1 missing250_252 records250_252 :=
  aligned250_251.append aligned251_252

def missing248_252 : List (BitVec (edgeCount 12)) :=
  missing248_250 ++ missing250_252
abbrev records248_252 : List Blob :=
  records248_250 ++ records250_252
theorem aligned248_252 :
    AlignedValid 12 1 missing248_252 records248_252 :=
  aligned248_250.append aligned250_252

def missing252_253 : List (BitVec (edgeCount 12)) :=
  [missing252]
abbrev records252_253 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record252]
theorem aligned252_253 :
    AlignedValid 12 1 missing252_253 records252_253 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check252
    maskCheck252 AlignedValid.nil

def missing253_254 : List (BitVec (edgeCount 12)) :=
  [missing253]
abbrev records253_254 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record253]
theorem aligned253_254 :
    AlignedValid 12 1 missing253_254 records253_254 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check253
    maskCheck253 AlignedValid.nil

def missing252_254 : List (BitVec (edgeCount 12)) :=
  missing252_253 ++ missing253_254
abbrev records252_254 : List Blob :=
  records252_253 ++ records253_254
theorem aligned252_254 :
    AlignedValid 12 1 missing252_254 records252_254 :=
  aligned252_253.append aligned253_254

def missing254_255 : List (BitVec (edgeCount 12)) :=
  [missing254]
abbrev records254_255 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record254]
theorem aligned254_255 :
    AlignedValid 12 1 missing254_255 records254_255 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check254
    maskCheck254 AlignedValid.nil

def missing255_256 : List (BitVec (edgeCount 12)) :=
  [missing255]
abbrev records255_256 : List Blob :=
  [StrongPackedBucketN12A1Shard001.record255]
theorem aligned255_256 :
    AlignedValid 12 1 missing255_256 records255_256 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A1Shard001.check255
    maskCheck255 AlignedValid.nil

def missing254_256 : List (BitVec (edgeCount 12)) :=
  missing254_255 ++ missing255_256
abbrev records254_256 : List Blob :=
  records254_255 ++ records255_256
theorem aligned254_256 :
    AlignedValid 12 1 missing254_256 records254_256 :=
  aligned254_255.append aligned255_256

def missing252_256 : List (BitVec (edgeCount 12)) :=
  missing252_254 ++ missing254_256
abbrev records252_256 : List Blob :=
  records252_254 ++ records254_256
theorem aligned252_256 :
    AlignedValid 12 1 missing252_256 records252_256 :=
  aligned252_254.append aligned254_256

def missing248_256 : List (BitVec (edgeCount 12)) :=
  missing248_252 ++ missing252_256
abbrev records248_256 : List Blob :=
  records248_252 ++ records252_256
theorem aligned248_256 :
    AlignedValid 12 1 missing248_256 records248_256 :=
  aligned248_252.append aligned252_256

def missing240_256 : List (BitVec (edgeCount 12)) :=
  missing240_248 ++ missing248_256
abbrev records240_256 : List Blob :=
  records240_248 ++ records248_256
theorem aligned240_256 :
    AlignedValid 12 1 missing240_256 records240_256 :=
  aligned240_248.append aligned248_256

def missing224_256 : List (BitVec (edgeCount 12)) :=
  missing224_240 ++ missing240_256
abbrev records224_256 : List Blob :=
  records224_240 ++ records240_256
theorem aligned224_256 :
    AlignedValid 12 1 missing224_256 records224_256 :=
  aligned224_240.append aligned240_256

def missing192_256 : List (BitVec (edgeCount 12)) :=
  missing192_224 ++ missing224_256
abbrev records192_256 : List Blob :=
  records192_224 ++ records224_256
theorem aligned192_256 :
    AlignedValid 12 1 missing192_256 records192_256 :=
  aligned192_224.append aligned224_256

def missing128_256 : List (BitVec (edgeCount 12)) :=
  missing128_192 ++ missing192_256
abbrev records128_256 : List Blob :=
  records128_192 ++ records192_256
theorem aligned128_256 :
    AlignedValid 12 1 missing128_256 records128_256 :=
  aligned128_192.append aligned192_256

abbrev missing : List (BitVec (edgeCount 12)) := missing128_256
abbrev records : List Blob := records128_256
theorem aligned : AlignedValid 12 1 missing records := aligned128_256

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A1AlignedShard001
