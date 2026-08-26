/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard180

/-! Decode-only alignment checks for n=12, a=4, records 23040--23167. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard180

open PackedBucketCertificate

def missing23040 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14019812018561744896
theorem maskCheck23040 :
    checkMaskFor missing23040 StrongPackedBucketN12A4Shard180.record23040 = true := by
  decide

def missing23041 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14055840815580708864
theorem maskCheck23041 :
    checkMaskFor missing23041 StrongPackedBucketN12A4Shard180.record23041 = true := by
  decide

def missing23042 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14488186379808276480
theorem maskCheck23042 :
    checkMaskFor missing23042 StrongPackedBucketN12A4Shard180.record23042 = true := by
  decide

def missing23043 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18955757210159808512
theorem maskCheck23043 :
    checkMaskFor missing23043 StrongPackedBucketN12A4Shard180.record23043 = true := by
  decide

def missing23044 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19243987586311520256
theorem maskCheck23044 :
    checkMaskFor missing23044 StrongPackedBucketN12A4Shard180.record23044 = true := by
  decide

def missing23045 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19460160368425304064
theorem maskCheck23045 :
    checkMaskFor missing23045 StrongPackedBucketN12A4Shard180.record23045 = true := by
  decide

def missing23046 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20252793902842511360
theorem maskCheck23046 :
    checkMaskFor missing23046 StrongPackedBucketN12A4Shard180.record23046 = true := by
  decide

def missing23047 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20324851496880439296
theorem maskCheck23047 :
    checkMaskFor missing23047 StrongPackedBucketN12A4Shard180.record23047 = true := by
  decide

def missing23048 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22486579318018277376
theorem maskCheck23048 :
    checkMaskFor missing23048 StrongPackedBucketN12A4Shard180.record23048 = true := by
  decide

def missing23049 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23279212852435484672
theorem maskCheck23049 :
    checkMaskFor missing23049 StrongPackedBucketN12A4Shard180.record23049 = true := by
  decide

def missing23050 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23495385634549268480
theorem maskCheck23050 :
    checkMaskFor missing23050 StrongPackedBucketN12A4Shard180.record23050 = true := by
  decide

def missing23051 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23711558416663052288
theorem maskCheck23051 :
    checkMaskFor missing23051 StrongPackedBucketN12A4Shard180.record23051 = true := by
  decide

def missing23052 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23783616010700980224
theorem maskCheck23052 :
    checkMaskFor missing23052 StrongPackedBucketN12A4Shard180.record23052 = true := by
  decide

def missing23053 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 24792422327231971328
theorem maskCheck23053 :
    checkMaskFor missing23053 StrongPackedBucketN12A4Shard180.record23053 = true := by
  decide

def missing23054 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27890898870862872576
theorem maskCheck23054 :
    checkMaskFor missing23054 StrongPackedBucketN12A4Shard180.record23054 = true := by
  decide

def missing23055 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28323244435090440192
theorem maskCheck23055 :
    checkMaskFor missing23055 StrongPackedBucketN12A4Shard180.record23055 = true := by
  decide

def missing23056 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32358469701214404608
theorem maskCheck23056 :
    checkMaskFor missing23056 StrongPackedBucketN12A4Shard180.record23056 = true := by
  decide

def missing23057 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37150299704736612352
theorem maskCheck23057 :
    checkMaskFor missing23057 StrongPackedBucketN12A4Shard180.record23057 = true := by
  decide

def missing23058 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37366472486850396160
theorem maskCheck23058 :
    checkMaskFor missing23058 StrongPackedBucketN12A4Shard180.record23058 = true := by
  decide

def missing23059 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46229556553515532288
theorem maskCheck23059 :
    checkMaskFor missing23059 StrongPackedBucketN12A4Shard180.record23059 = true := by
  decide

def missing23060 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 545147486585487360
theorem maskCheck23060 :
    checkMaskFor missing23060 StrongPackedBucketN12A4Shard180.record23060 = true := by
  decide

def missing23061 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 833377862737199104
theorem maskCheck23061 :
    checkMaskFor missing23061 StrongPackedBucketN12A4Shard180.record23061 = true := by
  decide

def missing23062 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 977493050813054976
theorem maskCheck23062 :
    checkMaskFor missing23062 StrongPackedBucketN12A4Shard180.record23062 = true := by
  decide

def missing23063 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1049550644850982912
theorem maskCheck23063 :
    checkMaskFor missing23063 StrongPackedBucketN12A4Shard180.record23063 = true := by
  decide

def missing23064 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1085579441869946880
theorem maskCheck23064 :
    checkMaskFor missing23064 StrongPackedBucketN12A4Shard180.record23064 = true := by
  decide

def missing23065 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1842184179268190208
theorem maskCheck23065 :
    checkMaskFor missing23065 StrongPackedBucketN12A4Shard180.record23065 = true := by
  decide

def missing23066 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1914241773306118144
theorem maskCheck23066 :
    checkMaskFor missing23066 StrongPackedBucketN12A4Shard180.record23066 = true := by
  decide

def missing23067 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1950270570325082112
theorem maskCheck23067 :
    checkMaskFor missing23067 StrongPackedBucketN12A4Shard180.record23067 = true := by
  decide

def missing23068 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2058356961381974016
theorem maskCheck23068 :
    checkMaskFor missing23068 StrongPackedBucketN12A4Shard180.record23068 = true := by
  decide

def missing23069 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2094385758400937984
theorem maskCheck23069 :
    checkMaskFor missing23069 StrongPackedBucketN12A4Shard180.record23069 = true := by
  decide

def missing23070 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2166443352438865920
theorem maskCheck23070 :
    checkMaskFor missing23070 StrongPackedBucketN12A4Shard180.record23070 = true := by
  decide

def missing23071 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4075969594443956224
theorem maskCheck23071 :
    checkMaskFor missing23071 StrongPackedBucketN12A4Shard180.record23071 = true := by
  decide

def missing23072 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4111998391462920192
theorem maskCheck23072 :
    checkMaskFor missing23072 StrongPackedBucketN12A4Shard180.record23072 = true := by
  decide

def missing23073 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4184055985500848128
theorem maskCheck23073 :
    checkMaskFor missing23073 StrongPackedBucketN12A4Shard180.record23073 = true := by
  decide

def missing23074 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4328171173576704000
theorem maskCheck23074 :
    checkMaskFor missing23074 StrongPackedBucketN12A4Shard180.record23074 = true := by
  decide

def missing23075 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4868603128861163520
theorem maskCheck23075 :
    checkMaskFor missing23075 StrongPackedBucketN12A4Shard180.record23075 = true := by
  decide

def missing23076 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5012718316937019392
theorem maskCheck23076 :
    checkMaskFor missing23076 StrongPackedBucketN12A4Shard180.record23076 = true := by
  decide

def missing23077 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5084775910974947328
theorem maskCheck23077 :
    checkMaskFor missing23077 StrongPackedBucketN12A4Shard180.record23077 = true := by
  decide

def missing23078 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5120804707993911296
theorem maskCheck23078 :
    checkMaskFor missing23078 StrongPackedBucketN12A4Shard180.record23078 = true := by
  decide

def missing23079 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5300948693088731136
theorem maskCheck23079 :
    checkMaskFor missing23079 StrongPackedBucketN12A4Shard180.record23079 = true := by
  decide

def missing23080 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5373006287126659072
theorem maskCheck23080 :
    checkMaskFor missing23080 StrongPackedBucketN12A4Shard180.record23080 = true := by
  decide

def missing23081 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5409035084145623040
theorem maskCheck23081 :
    checkMaskFor missing23081 StrongPackedBucketN12A4Shard180.record23081 = true := by
  decide

def missing23082 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5517121475202514944
theorem maskCheck23082 :
    checkMaskFor missing23082 StrongPackedBucketN12A4Shard180.record23082 = true := by
  decide

def missing23083 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5553150272221478912
theorem maskCheck23083 :
    checkMaskFor missing23083 StrongPackedBucketN12A4Shard180.record23083 = true := by
  decide

def missing23084 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6381812603657650176
theorem maskCheck23084 :
    checkMaskFor missing23084 StrongPackedBucketN12A4Shard180.record23084 = true := by
  decide

def missing23085 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6417841400676614144
theorem maskCheck23085 :
    checkMaskFor missing23085 StrongPackedBucketN12A4Shard180.record23085 = true := by
  decide

def missing23086 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9480289147288551424
theorem maskCheck23086 :
    checkMaskFor missing23086 StrongPackedBucketN12A4Shard180.record23086 = true := by
  decide

def missing23087 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9624404335364407296
theorem maskCheck23087 :
    checkMaskFor missing23087 StrongPackedBucketN12A4Shard180.record23087 = true := by
  decide

def missing23088 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9696461929402335232
theorem maskCheck23088 :
    checkMaskFor missing23088 StrongPackedBucketN12A4Shard180.record23088 = true := by
  decide

def missing23089 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9912634711516119040
theorem maskCheck23089 :
    checkMaskFor missing23089 StrongPackedBucketN12A4Shard180.record23089 = true := by
  decide

def missing23090 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9984692305554046976
theorem maskCheck23090 :
    checkMaskFor missing23090 StrongPackedBucketN12A4Shard180.record23090 = true := by
  decide

def missing23091 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10128807493629902848
theorem maskCheck23091 :
    checkMaskFor missing23091 StrongPackedBucketN12A4Shard180.record23091 = true := by
  decide

def missing23092 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10993498622085038080
theorem maskCheck23092 :
    checkMaskFor missing23092 StrongPackedBucketN12A4Shard180.record23092 = true := by
  decide

def missing23093 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13947859977640083456
theorem maskCheck23093 :
    checkMaskFor missing23093 StrongPackedBucketN12A4Shard180.record23093 = true := by
  decide

def missing23094 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18703661184143327232
theorem maskCheck23094 :
    checkMaskFor missing23094 StrongPackedBucketN12A4Shard180.record23094 = true := by
  decide

def missing23095 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18847776372219183104
theorem maskCheck23095 :
    checkMaskFor missing23095 StrongPackedBucketN12A4Shard180.record23095 = true := by
  decide

def missing23096 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18919833966257111040
theorem maskCheck23096 :
    checkMaskFor missing23096 StrongPackedBucketN12A4Shard180.record23096 = true := by
  decide

def missing23097 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18955862763276075008
theorem maskCheck23097 :
    checkMaskFor missing23097 StrongPackedBucketN12A4Shard180.record23097 = true := by
  decide

def missing23098 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19136006748370894848
theorem maskCheck23098 :
    checkMaskFor missing23098 StrongPackedBucketN12A4Shard180.record23098 = true := by
  decide

def missing23099 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19208064342408822784
theorem maskCheck23099 :
    checkMaskFor missing23099 StrongPackedBucketN12A4Shard180.record23099 = true := by
  decide

def missing23100 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19244093139427786752
theorem maskCheck23100 :
    checkMaskFor missing23100 StrongPackedBucketN12A4Shard180.record23100 = true := by
  decide

def missing23101 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19352179530484678656
theorem maskCheck23101 :
    checkMaskFor missing23101 StrongPackedBucketN12A4Shard180.record23101 = true := by
  decide

def missing23102 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19388208327503642624
theorem maskCheck23102 :
    checkMaskFor missing23102 StrongPackedBucketN12A4Shard180.record23102 = true := by
  decide

def missing23103 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19460265921541570560
theorem maskCheck23103 :
    checkMaskFor missing23103 StrongPackedBucketN12A4Shard180.record23103 = true := by
  decide

def missing23104 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20216870658939813888
theorem maskCheck23104 :
    checkMaskFor missing23104 StrongPackedBucketN12A4Shard180.record23104 = true := by
  decide

def missing23105 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20252899455958777856
theorem maskCheck23105 :
    checkMaskFor missing23105 StrongPackedBucketN12A4Shard180.record23105 = true := by
  decide

def missing23106 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20324957049996705792
theorem maskCheck23106 :
    checkMaskFor missing23106 StrongPackedBucketN12A4Shard180.record23106 = true := by
  decide

def missing23107 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20469072238072561664
theorem maskCheck23107 :
    checkMaskFor missing23107 StrongPackedBucketN12A4Shard180.record23107 = true := by
  decide

def missing23108 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22486684871134543872
theorem maskCheck23108 :
    checkMaskFor missing23108 StrongPackedBucketN12A4Shard180.record23108 = true := by
  decide

def missing23109 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23171232014494859264
theorem maskCheck23109 :
    checkMaskFor missing23109 StrongPackedBucketN12A4Shard180.record23109 = true := by
  decide

def missing23110 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23243289608532787200
theorem maskCheck23110 :
    checkMaskFor missing23110 StrongPackedBucketN12A4Shard180.record23110 = true := by
  decide

def missing23111 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23279318405551751168
theorem maskCheck23111 :
    checkMaskFor missing23111 StrongPackedBucketN12A4Shard180.record23111 = true := by
  decide

def missing23112 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23387404796608643072
theorem maskCheck23112 :
    checkMaskFor missing23112 StrongPackedBucketN12A4Shard180.record23112 = true := by
  decide

def missing23113 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23423433593627607040
theorem maskCheck23113 :
    checkMaskFor missing23113 StrongPackedBucketN12A4Shard180.record23113 = true := by
  decide

def missing23114 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23675635172760354816
theorem maskCheck23114 :
    checkMaskFor missing23114 StrongPackedBucketN12A4Shard180.record23114 = true := by
  decide

def missing23115 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23711663969779318784
theorem maskCheck23115 :
    checkMaskFor missing23115 StrongPackedBucketN12A4Shard180.record23115 = true := by
  decide

def missing23116 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27782918032922247168
theorem maskCheck23116 :
    checkMaskFor missing23116 StrongPackedBucketN12A4Shard180.record23116 = true := by
  decide

def missing23117 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27854975626960175104
theorem maskCheck23117 :
    checkMaskFor missing23117 StrongPackedBucketN12A4Shard180.record23117 = true := by
  decide

def missing23118 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27999090815036030976
theorem maskCheck23118 :
    checkMaskFor missing23118 StrongPackedBucketN12A4Shard180.record23118 = true := by
  decide

def missing23119 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28287321191187742720
theorem maskCheck23119 :
    checkMaskFor missing23119 StrongPackedBucketN12A4Shard180.record23119 = true := by
  decide

def missing23120 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41726062479261302784
theorem maskCheck23120 :
    checkMaskFor missing23120 StrongPackedBucketN12A4Shard180.record23120 = true := by
  decide

def missing23121 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41870177667337158656
theorem maskCheck23121 :
    checkMaskFor missing23121 StrongPackedBucketN12A4Shard180.record23121 = true := by
  decide

def missing23122 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 545569699050553344
theorem maskCheck23122 :
    checkMaskFor missing23122 StrongPackedBucketN12A4Shard180.record23122 = true := by
  decide

def missing23123 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 833800075202265088
theorem maskCheck23123 :
    checkMaskFor missing23123 StrongPackedBucketN12A4Shard180.record23123 = true := by
  decide

def missing23124 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1049972857316048896
theorem maskCheck23124 :
    checkMaskFor missing23124 StrongPackedBucketN12A4Shard180.record23124 = true := by
  decide

def missing23125 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1086001654335012864
theorem maskCheck23125 :
    checkMaskFor missing23125 StrongPackedBucketN12A4Shard180.record23125 = true := by
  decide

def missing23126 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1410260827505688576
theorem maskCheck23126 :
    checkMaskFor missing23126 StrongPackedBucketN12A4Shard180.record23126 = true := by
  decide

def missing23127 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1626433609619472384
theorem maskCheck23127 :
    checkMaskFor missing23127 StrongPackedBucketN12A4Shard180.record23127 = true := by
  decide

def missing23128 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1662462406638436352
theorem maskCheck23128 :
    checkMaskFor missing23128 StrongPackedBucketN12A4Shard180.record23128 = true := by
  decide

def missing23129 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1842606391733256192
theorem maskCheck23129 :
    checkMaskFor missing23129 StrongPackedBucketN12A4Shard180.record23129 = true := by
  decide

def missing23130 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1914663985771184128
theorem maskCheck23130 :
    checkMaskFor missing23130 StrongPackedBucketN12A4Shard180.record23130 = true := by
  decide

def missing23131 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1950692782790148096
theorem maskCheck23131 :
    checkMaskFor missing23131 StrongPackedBucketN12A4Shard180.record23131 = true := by
  decide

def missing23132 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2166865564903931904
theorem maskCheck23132 :
    checkMaskFor missing23132 StrongPackedBucketN12A4Shard180.record23132 = true := by
  decide

def missing23133 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3571988648643526656
theorem maskCheck23133 :
    checkMaskFor missing23133 StrongPackedBucketN12A4Shard180.record23133 = true := by
  decide

def missing23134 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3644046242681454592
theorem maskCheck23134 :
    checkMaskFor missing23134 StrongPackedBucketN12A4Shard180.record23134 = true := by
  decide

def missing23135 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3680075039700418560
theorem maskCheck23135 :
    checkMaskFor missing23135 StrongPackedBucketN12A4Shard180.record23135 = true := by
  decide

def missing23136 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3896247821814202368
theorem maskCheck23136 :
    checkMaskFor missing23136 StrongPackedBucketN12A4Shard180.record23136 = true := by
  decide

def missing23137 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4076391806909022208
theorem maskCheck23137 :
    checkMaskFor missing23137 StrongPackedBucketN12A4Shard180.record23137 = true := by
  decide

def missing23138 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4112420603927986176
theorem maskCheck23138 :
    checkMaskFor missing23138 StrongPackedBucketN12A4Shard180.record23138 = true := by
  decide

def missing23139 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4184478197965914112
theorem maskCheck23139 :
    checkMaskFor missing23139 StrongPackedBucketN12A4Shard180.record23139 = true := by
  decide

def missing23140 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4869025341326229504
theorem maskCheck23140 :
    checkMaskFor missing23140 StrongPackedBucketN12A4Shard180.record23140 = true := by
  decide

def missing23141 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5085198123440013312
theorem maskCheck23141 :
    checkMaskFor missing23141 StrongPackedBucketN12A4Shard180.record23141 = true := by
  decide

def missing23142 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5121226920458977280
theorem maskCheck23142 :
    checkMaskFor missing23142 StrongPackedBucketN12A4Shard180.record23142 = true := by
  decide

def missing23143 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5301370905553797120
theorem maskCheck23143 :
    checkMaskFor missing23143 StrongPackedBucketN12A4Shard180.record23143 = true := by
  decide

def missing23144 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5373428499591725056
theorem maskCheck23144 :
    checkMaskFor missing23144 StrongPackedBucketN12A4Shard180.record23144 = true := by
  decide

def missing23145 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5409457296610689024
theorem maskCheck23145 :
    checkMaskFor missing23145 StrongPackedBucketN12A4Shard180.record23145 = true := by
  decide

def missing23146 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5877831657857220608
theorem maskCheck23146 :
    checkMaskFor missing23146 StrongPackedBucketN12A4Shard180.record23146 = true := by
  decide

def missing23147 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5949889251895148544
theorem maskCheck23147 :
    checkMaskFor missing23147 StrongPackedBucketN12A4Shard180.record23147 = true := by
  decide

def missing23148 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5985918048914112512
theorem maskCheck23148 :
    checkMaskFor missing23148 StrongPackedBucketN12A4Shard180.record23148 = true := by
  decide

def missing23149 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6382234816122716160
theorem maskCheck23149 :
    checkMaskFor missing23149 StrongPackedBucketN12A4Shard180.record23149 = true := by
  decide

def missing23150 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 6418263613141680128
theorem maskCheck23150 :
    checkMaskFor missing23150 StrongPackedBucketN12A4Shard180.record23150 = true := by
  decide

def missing23151 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8111617073032986624
theorem maskCheck23151 :
    checkMaskFor missing23151 StrongPackedBucketN12A4Shard180.record23151 = true := by
  decide

def missing23152 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8147645870051950592
theorem maskCheck23152 :
    checkMaskFor missing23152 StrongPackedBucketN12A4Shard180.record23152 = true := by
  decide

def missing23153 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9480711359753617408
theorem maskCheck23153 :
    checkMaskFor missing23153 StrongPackedBucketN12A4Shard180.record23153 = true := by
  decide

def missing23154 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9696884141867401216
theorem maskCheck23154 :
    checkMaskFor missing23154 StrongPackedBucketN12A4Shard180.record23154 = true := by
  decide

def missing23155 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9913056923981185024
theorem maskCheck23155 :
    checkMaskFor missing23155 StrongPackedBucketN12A4Shard180.record23155 = true := by
  decide

def missing23156 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9985114518019112960
theorem maskCheck23156 :
    checkMaskFor missing23156 StrongPackedBucketN12A4Shard180.record23156 = true := by
  decide

def missing23157 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10489517676284608512
theorem maskCheck23157 :
    checkMaskFor missing23157 StrongPackedBucketN12A4Shard180.record23157 = true := by
  decide

def missing23158 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10561575270322536448
theorem maskCheck23158 :
    checkMaskFor missing23158 StrongPackedBucketN12A4Shard180.record23158 = true := by
  decide

def missing23159 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10993920834550104064
theorem maskCheck23159 :
    checkMaskFor missing23159 StrongPackedBucketN12A4Shard180.record23159 = true := by
  decide

def missing23160 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 12723303091460374528
theorem maskCheck23160 :
    checkMaskFor missing23160 StrongPackedBucketN12A4Shard180.record23160 = true := by
  decide

def missing23161 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13948282190105149440
theorem maskCheck23161 :
    checkMaskFor missing23161 StrongPackedBucketN12A4Shard180.record23161 = true := by
  decide

def missing23162 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18704083396608393216
theorem maskCheck23162 :
    checkMaskFor missing23162 StrongPackedBucketN12A4Shard180.record23162 = true := by
  decide

def missing23163 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18920256178722177024
theorem maskCheck23163 :
    checkMaskFor missing23163 StrongPackedBucketN12A4Shard180.record23163 = true := by
  decide

def missing23164 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18956284975741140992
theorem maskCheck23164 :
    checkMaskFor missing23164 StrongPackedBucketN12A4Shard180.record23164 = true := by
  decide

def missing23165 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19136428960835960832
theorem maskCheck23165 :
    checkMaskFor missing23165 StrongPackedBucketN12A4Shard180.record23165 = true := by
  decide

def missing23166 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19208486554873888768
theorem maskCheck23166 :
    checkMaskFor missing23166 StrongPackedBucketN12A4Shard180.record23166 = true := by
  decide

def missing23167 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19244515351892852736
theorem maskCheck23167 :
    checkMaskFor missing23167 StrongPackedBucketN12A4Shard180.record23167 = true := by
  decide

def missing23040_23041 : List (BitVec (edgeCount 12)) :=
  [missing23040]
abbrev records23040_23041 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23040]
theorem aligned23040_23041 :
    AlignedValid 12 4 missing23040_23041 records23040_23041 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23040
    maskCheck23040 AlignedValid.nil

def missing23041_23042 : List (BitVec (edgeCount 12)) :=
  [missing23041]
abbrev records23041_23042 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23041]
theorem aligned23041_23042 :
    AlignedValid 12 4 missing23041_23042 records23041_23042 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23041
    maskCheck23041 AlignedValid.nil

def missing23040_23042 : List (BitVec (edgeCount 12)) :=
  missing23040_23041 ++ missing23041_23042
abbrev records23040_23042 : List Blob :=
  records23040_23041 ++ records23041_23042
theorem aligned23040_23042 :
    AlignedValid 12 4 missing23040_23042 records23040_23042 :=
  aligned23040_23041.append aligned23041_23042

def missing23042_23043 : List (BitVec (edgeCount 12)) :=
  [missing23042]
abbrev records23042_23043 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23042]
theorem aligned23042_23043 :
    AlignedValid 12 4 missing23042_23043 records23042_23043 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23042
    maskCheck23042 AlignedValid.nil

def missing23043_23044 : List (BitVec (edgeCount 12)) :=
  [missing23043]
abbrev records23043_23044 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23043]
theorem aligned23043_23044 :
    AlignedValid 12 4 missing23043_23044 records23043_23044 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23043
    maskCheck23043 AlignedValid.nil

def missing23042_23044 : List (BitVec (edgeCount 12)) :=
  missing23042_23043 ++ missing23043_23044
abbrev records23042_23044 : List Blob :=
  records23042_23043 ++ records23043_23044
theorem aligned23042_23044 :
    AlignedValid 12 4 missing23042_23044 records23042_23044 :=
  aligned23042_23043.append aligned23043_23044

def missing23040_23044 : List (BitVec (edgeCount 12)) :=
  missing23040_23042 ++ missing23042_23044
abbrev records23040_23044 : List Blob :=
  records23040_23042 ++ records23042_23044
theorem aligned23040_23044 :
    AlignedValid 12 4 missing23040_23044 records23040_23044 :=
  aligned23040_23042.append aligned23042_23044

def missing23044_23045 : List (BitVec (edgeCount 12)) :=
  [missing23044]
abbrev records23044_23045 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23044]
theorem aligned23044_23045 :
    AlignedValid 12 4 missing23044_23045 records23044_23045 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23044
    maskCheck23044 AlignedValid.nil

def missing23045_23046 : List (BitVec (edgeCount 12)) :=
  [missing23045]
abbrev records23045_23046 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23045]
theorem aligned23045_23046 :
    AlignedValid 12 4 missing23045_23046 records23045_23046 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23045
    maskCheck23045 AlignedValid.nil

def missing23044_23046 : List (BitVec (edgeCount 12)) :=
  missing23044_23045 ++ missing23045_23046
abbrev records23044_23046 : List Blob :=
  records23044_23045 ++ records23045_23046
theorem aligned23044_23046 :
    AlignedValid 12 4 missing23044_23046 records23044_23046 :=
  aligned23044_23045.append aligned23045_23046

def missing23046_23047 : List (BitVec (edgeCount 12)) :=
  [missing23046]
abbrev records23046_23047 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23046]
theorem aligned23046_23047 :
    AlignedValid 12 4 missing23046_23047 records23046_23047 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23046
    maskCheck23046 AlignedValid.nil

def missing23047_23048 : List (BitVec (edgeCount 12)) :=
  [missing23047]
abbrev records23047_23048 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23047]
theorem aligned23047_23048 :
    AlignedValid 12 4 missing23047_23048 records23047_23048 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23047
    maskCheck23047 AlignedValid.nil

def missing23046_23048 : List (BitVec (edgeCount 12)) :=
  missing23046_23047 ++ missing23047_23048
abbrev records23046_23048 : List Blob :=
  records23046_23047 ++ records23047_23048
theorem aligned23046_23048 :
    AlignedValid 12 4 missing23046_23048 records23046_23048 :=
  aligned23046_23047.append aligned23047_23048

def missing23044_23048 : List (BitVec (edgeCount 12)) :=
  missing23044_23046 ++ missing23046_23048
abbrev records23044_23048 : List Blob :=
  records23044_23046 ++ records23046_23048
theorem aligned23044_23048 :
    AlignedValid 12 4 missing23044_23048 records23044_23048 :=
  aligned23044_23046.append aligned23046_23048

def missing23040_23048 : List (BitVec (edgeCount 12)) :=
  missing23040_23044 ++ missing23044_23048
abbrev records23040_23048 : List Blob :=
  records23040_23044 ++ records23044_23048
theorem aligned23040_23048 :
    AlignedValid 12 4 missing23040_23048 records23040_23048 :=
  aligned23040_23044.append aligned23044_23048

def missing23048_23049 : List (BitVec (edgeCount 12)) :=
  [missing23048]
abbrev records23048_23049 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23048]
theorem aligned23048_23049 :
    AlignedValid 12 4 missing23048_23049 records23048_23049 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23048
    maskCheck23048 AlignedValid.nil

def missing23049_23050 : List (BitVec (edgeCount 12)) :=
  [missing23049]
abbrev records23049_23050 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23049]
theorem aligned23049_23050 :
    AlignedValid 12 4 missing23049_23050 records23049_23050 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23049
    maskCheck23049 AlignedValid.nil

def missing23048_23050 : List (BitVec (edgeCount 12)) :=
  missing23048_23049 ++ missing23049_23050
abbrev records23048_23050 : List Blob :=
  records23048_23049 ++ records23049_23050
theorem aligned23048_23050 :
    AlignedValid 12 4 missing23048_23050 records23048_23050 :=
  aligned23048_23049.append aligned23049_23050

def missing23050_23051 : List (BitVec (edgeCount 12)) :=
  [missing23050]
abbrev records23050_23051 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23050]
theorem aligned23050_23051 :
    AlignedValid 12 4 missing23050_23051 records23050_23051 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23050
    maskCheck23050 AlignedValid.nil

def missing23051_23052 : List (BitVec (edgeCount 12)) :=
  [missing23051]
abbrev records23051_23052 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23051]
theorem aligned23051_23052 :
    AlignedValid 12 4 missing23051_23052 records23051_23052 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23051
    maskCheck23051 AlignedValid.nil

def missing23050_23052 : List (BitVec (edgeCount 12)) :=
  missing23050_23051 ++ missing23051_23052
abbrev records23050_23052 : List Blob :=
  records23050_23051 ++ records23051_23052
theorem aligned23050_23052 :
    AlignedValid 12 4 missing23050_23052 records23050_23052 :=
  aligned23050_23051.append aligned23051_23052

def missing23048_23052 : List (BitVec (edgeCount 12)) :=
  missing23048_23050 ++ missing23050_23052
abbrev records23048_23052 : List Blob :=
  records23048_23050 ++ records23050_23052
theorem aligned23048_23052 :
    AlignedValid 12 4 missing23048_23052 records23048_23052 :=
  aligned23048_23050.append aligned23050_23052

def missing23052_23053 : List (BitVec (edgeCount 12)) :=
  [missing23052]
abbrev records23052_23053 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23052]
theorem aligned23052_23053 :
    AlignedValid 12 4 missing23052_23053 records23052_23053 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23052
    maskCheck23052 AlignedValid.nil

def missing23053_23054 : List (BitVec (edgeCount 12)) :=
  [missing23053]
abbrev records23053_23054 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23053]
theorem aligned23053_23054 :
    AlignedValid 12 4 missing23053_23054 records23053_23054 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23053
    maskCheck23053 AlignedValid.nil

def missing23052_23054 : List (BitVec (edgeCount 12)) :=
  missing23052_23053 ++ missing23053_23054
abbrev records23052_23054 : List Blob :=
  records23052_23053 ++ records23053_23054
theorem aligned23052_23054 :
    AlignedValid 12 4 missing23052_23054 records23052_23054 :=
  aligned23052_23053.append aligned23053_23054

def missing23054_23055 : List (BitVec (edgeCount 12)) :=
  [missing23054]
abbrev records23054_23055 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23054]
theorem aligned23054_23055 :
    AlignedValid 12 4 missing23054_23055 records23054_23055 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23054
    maskCheck23054 AlignedValid.nil

def missing23055_23056 : List (BitVec (edgeCount 12)) :=
  [missing23055]
abbrev records23055_23056 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23055]
theorem aligned23055_23056 :
    AlignedValid 12 4 missing23055_23056 records23055_23056 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23055
    maskCheck23055 AlignedValid.nil

def missing23054_23056 : List (BitVec (edgeCount 12)) :=
  missing23054_23055 ++ missing23055_23056
abbrev records23054_23056 : List Blob :=
  records23054_23055 ++ records23055_23056
theorem aligned23054_23056 :
    AlignedValid 12 4 missing23054_23056 records23054_23056 :=
  aligned23054_23055.append aligned23055_23056

def missing23052_23056 : List (BitVec (edgeCount 12)) :=
  missing23052_23054 ++ missing23054_23056
abbrev records23052_23056 : List Blob :=
  records23052_23054 ++ records23054_23056
theorem aligned23052_23056 :
    AlignedValid 12 4 missing23052_23056 records23052_23056 :=
  aligned23052_23054.append aligned23054_23056

def missing23048_23056 : List (BitVec (edgeCount 12)) :=
  missing23048_23052 ++ missing23052_23056
abbrev records23048_23056 : List Blob :=
  records23048_23052 ++ records23052_23056
theorem aligned23048_23056 :
    AlignedValid 12 4 missing23048_23056 records23048_23056 :=
  aligned23048_23052.append aligned23052_23056

def missing23040_23056 : List (BitVec (edgeCount 12)) :=
  missing23040_23048 ++ missing23048_23056
abbrev records23040_23056 : List Blob :=
  records23040_23048 ++ records23048_23056
theorem aligned23040_23056 :
    AlignedValid 12 4 missing23040_23056 records23040_23056 :=
  aligned23040_23048.append aligned23048_23056

def missing23056_23057 : List (BitVec (edgeCount 12)) :=
  [missing23056]
abbrev records23056_23057 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23056]
theorem aligned23056_23057 :
    AlignedValid 12 4 missing23056_23057 records23056_23057 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23056
    maskCheck23056 AlignedValid.nil

def missing23057_23058 : List (BitVec (edgeCount 12)) :=
  [missing23057]
abbrev records23057_23058 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23057]
theorem aligned23057_23058 :
    AlignedValid 12 4 missing23057_23058 records23057_23058 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23057
    maskCheck23057 AlignedValid.nil

def missing23056_23058 : List (BitVec (edgeCount 12)) :=
  missing23056_23057 ++ missing23057_23058
abbrev records23056_23058 : List Blob :=
  records23056_23057 ++ records23057_23058
theorem aligned23056_23058 :
    AlignedValid 12 4 missing23056_23058 records23056_23058 :=
  aligned23056_23057.append aligned23057_23058

def missing23058_23059 : List (BitVec (edgeCount 12)) :=
  [missing23058]
abbrev records23058_23059 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23058]
theorem aligned23058_23059 :
    AlignedValid 12 4 missing23058_23059 records23058_23059 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23058
    maskCheck23058 AlignedValid.nil

def missing23059_23060 : List (BitVec (edgeCount 12)) :=
  [missing23059]
abbrev records23059_23060 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23059]
theorem aligned23059_23060 :
    AlignedValid 12 4 missing23059_23060 records23059_23060 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23059
    maskCheck23059 AlignedValid.nil

def missing23058_23060 : List (BitVec (edgeCount 12)) :=
  missing23058_23059 ++ missing23059_23060
abbrev records23058_23060 : List Blob :=
  records23058_23059 ++ records23059_23060
theorem aligned23058_23060 :
    AlignedValid 12 4 missing23058_23060 records23058_23060 :=
  aligned23058_23059.append aligned23059_23060

def missing23056_23060 : List (BitVec (edgeCount 12)) :=
  missing23056_23058 ++ missing23058_23060
abbrev records23056_23060 : List Blob :=
  records23056_23058 ++ records23058_23060
theorem aligned23056_23060 :
    AlignedValid 12 4 missing23056_23060 records23056_23060 :=
  aligned23056_23058.append aligned23058_23060

def missing23060_23061 : List (BitVec (edgeCount 12)) :=
  [missing23060]
abbrev records23060_23061 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23060]
theorem aligned23060_23061 :
    AlignedValid 12 4 missing23060_23061 records23060_23061 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23060
    maskCheck23060 AlignedValid.nil

def missing23061_23062 : List (BitVec (edgeCount 12)) :=
  [missing23061]
abbrev records23061_23062 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23061]
theorem aligned23061_23062 :
    AlignedValid 12 4 missing23061_23062 records23061_23062 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23061
    maskCheck23061 AlignedValid.nil

def missing23060_23062 : List (BitVec (edgeCount 12)) :=
  missing23060_23061 ++ missing23061_23062
abbrev records23060_23062 : List Blob :=
  records23060_23061 ++ records23061_23062
theorem aligned23060_23062 :
    AlignedValid 12 4 missing23060_23062 records23060_23062 :=
  aligned23060_23061.append aligned23061_23062

def missing23062_23063 : List (BitVec (edgeCount 12)) :=
  [missing23062]
abbrev records23062_23063 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23062]
theorem aligned23062_23063 :
    AlignedValid 12 4 missing23062_23063 records23062_23063 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23062
    maskCheck23062 AlignedValid.nil

def missing23063_23064 : List (BitVec (edgeCount 12)) :=
  [missing23063]
abbrev records23063_23064 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23063]
theorem aligned23063_23064 :
    AlignedValid 12 4 missing23063_23064 records23063_23064 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23063
    maskCheck23063 AlignedValid.nil

def missing23062_23064 : List (BitVec (edgeCount 12)) :=
  missing23062_23063 ++ missing23063_23064
abbrev records23062_23064 : List Blob :=
  records23062_23063 ++ records23063_23064
theorem aligned23062_23064 :
    AlignedValid 12 4 missing23062_23064 records23062_23064 :=
  aligned23062_23063.append aligned23063_23064

def missing23060_23064 : List (BitVec (edgeCount 12)) :=
  missing23060_23062 ++ missing23062_23064
abbrev records23060_23064 : List Blob :=
  records23060_23062 ++ records23062_23064
theorem aligned23060_23064 :
    AlignedValid 12 4 missing23060_23064 records23060_23064 :=
  aligned23060_23062.append aligned23062_23064

def missing23056_23064 : List (BitVec (edgeCount 12)) :=
  missing23056_23060 ++ missing23060_23064
abbrev records23056_23064 : List Blob :=
  records23056_23060 ++ records23060_23064
theorem aligned23056_23064 :
    AlignedValid 12 4 missing23056_23064 records23056_23064 :=
  aligned23056_23060.append aligned23060_23064

def missing23064_23065 : List (BitVec (edgeCount 12)) :=
  [missing23064]
abbrev records23064_23065 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23064]
theorem aligned23064_23065 :
    AlignedValid 12 4 missing23064_23065 records23064_23065 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23064
    maskCheck23064 AlignedValid.nil

def missing23065_23066 : List (BitVec (edgeCount 12)) :=
  [missing23065]
abbrev records23065_23066 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23065]
theorem aligned23065_23066 :
    AlignedValid 12 4 missing23065_23066 records23065_23066 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23065
    maskCheck23065 AlignedValid.nil

def missing23064_23066 : List (BitVec (edgeCount 12)) :=
  missing23064_23065 ++ missing23065_23066
abbrev records23064_23066 : List Blob :=
  records23064_23065 ++ records23065_23066
theorem aligned23064_23066 :
    AlignedValid 12 4 missing23064_23066 records23064_23066 :=
  aligned23064_23065.append aligned23065_23066

def missing23066_23067 : List (BitVec (edgeCount 12)) :=
  [missing23066]
abbrev records23066_23067 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23066]
theorem aligned23066_23067 :
    AlignedValid 12 4 missing23066_23067 records23066_23067 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23066
    maskCheck23066 AlignedValid.nil

def missing23067_23068 : List (BitVec (edgeCount 12)) :=
  [missing23067]
abbrev records23067_23068 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23067]
theorem aligned23067_23068 :
    AlignedValid 12 4 missing23067_23068 records23067_23068 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23067
    maskCheck23067 AlignedValid.nil

def missing23066_23068 : List (BitVec (edgeCount 12)) :=
  missing23066_23067 ++ missing23067_23068
abbrev records23066_23068 : List Blob :=
  records23066_23067 ++ records23067_23068
theorem aligned23066_23068 :
    AlignedValid 12 4 missing23066_23068 records23066_23068 :=
  aligned23066_23067.append aligned23067_23068

def missing23064_23068 : List (BitVec (edgeCount 12)) :=
  missing23064_23066 ++ missing23066_23068
abbrev records23064_23068 : List Blob :=
  records23064_23066 ++ records23066_23068
theorem aligned23064_23068 :
    AlignedValid 12 4 missing23064_23068 records23064_23068 :=
  aligned23064_23066.append aligned23066_23068

def missing23068_23069 : List (BitVec (edgeCount 12)) :=
  [missing23068]
abbrev records23068_23069 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23068]
theorem aligned23068_23069 :
    AlignedValid 12 4 missing23068_23069 records23068_23069 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23068
    maskCheck23068 AlignedValid.nil

def missing23069_23070 : List (BitVec (edgeCount 12)) :=
  [missing23069]
abbrev records23069_23070 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23069]
theorem aligned23069_23070 :
    AlignedValid 12 4 missing23069_23070 records23069_23070 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23069
    maskCheck23069 AlignedValid.nil

def missing23068_23070 : List (BitVec (edgeCount 12)) :=
  missing23068_23069 ++ missing23069_23070
abbrev records23068_23070 : List Blob :=
  records23068_23069 ++ records23069_23070
theorem aligned23068_23070 :
    AlignedValid 12 4 missing23068_23070 records23068_23070 :=
  aligned23068_23069.append aligned23069_23070

def missing23070_23071 : List (BitVec (edgeCount 12)) :=
  [missing23070]
abbrev records23070_23071 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23070]
theorem aligned23070_23071 :
    AlignedValid 12 4 missing23070_23071 records23070_23071 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23070
    maskCheck23070 AlignedValid.nil

def missing23071_23072 : List (BitVec (edgeCount 12)) :=
  [missing23071]
abbrev records23071_23072 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23071]
theorem aligned23071_23072 :
    AlignedValid 12 4 missing23071_23072 records23071_23072 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23071
    maskCheck23071 AlignedValid.nil

def missing23070_23072 : List (BitVec (edgeCount 12)) :=
  missing23070_23071 ++ missing23071_23072
abbrev records23070_23072 : List Blob :=
  records23070_23071 ++ records23071_23072
theorem aligned23070_23072 :
    AlignedValid 12 4 missing23070_23072 records23070_23072 :=
  aligned23070_23071.append aligned23071_23072

def missing23068_23072 : List (BitVec (edgeCount 12)) :=
  missing23068_23070 ++ missing23070_23072
abbrev records23068_23072 : List Blob :=
  records23068_23070 ++ records23070_23072
theorem aligned23068_23072 :
    AlignedValid 12 4 missing23068_23072 records23068_23072 :=
  aligned23068_23070.append aligned23070_23072

def missing23064_23072 : List (BitVec (edgeCount 12)) :=
  missing23064_23068 ++ missing23068_23072
abbrev records23064_23072 : List Blob :=
  records23064_23068 ++ records23068_23072
theorem aligned23064_23072 :
    AlignedValid 12 4 missing23064_23072 records23064_23072 :=
  aligned23064_23068.append aligned23068_23072

def missing23056_23072 : List (BitVec (edgeCount 12)) :=
  missing23056_23064 ++ missing23064_23072
abbrev records23056_23072 : List Blob :=
  records23056_23064 ++ records23064_23072
theorem aligned23056_23072 :
    AlignedValid 12 4 missing23056_23072 records23056_23072 :=
  aligned23056_23064.append aligned23064_23072

def missing23040_23072 : List (BitVec (edgeCount 12)) :=
  missing23040_23056 ++ missing23056_23072
abbrev records23040_23072 : List Blob :=
  records23040_23056 ++ records23056_23072
theorem aligned23040_23072 :
    AlignedValid 12 4 missing23040_23072 records23040_23072 :=
  aligned23040_23056.append aligned23056_23072

def missing23072_23073 : List (BitVec (edgeCount 12)) :=
  [missing23072]
abbrev records23072_23073 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23072]
theorem aligned23072_23073 :
    AlignedValid 12 4 missing23072_23073 records23072_23073 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23072
    maskCheck23072 AlignedValid.nil

def missing23073_23074 : List (BitVec (edgeCount 12)) :=
  [missing23073]
abbrev records23073_23074 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23073]
theorem aligned23073_23074 :
    AlignedValid 12 4 missing23073_23074 records23073_23074 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23073
    maskCheck23073 AlignedValid.nil

def missing23072_23074 : List (BitVec (edgeCount 12)) :=
  missing23072_23073 ++ missing23073_23074
abbrev records23072_23074 : List Blob :=
  records23072_23073 ++ records23073_23074
theorem aligned23072_23074 :
    AlignedValid 12 4 missing23072_23074 records23072_23074 :=
  aligned23072_23073.append aligned23073_23074

def missing23074_23075 : List (BitVec (edgeCount 12)) :=
  [missing23074]
abbrev records23074_23075 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23074]
theorem aligned23074_23075 :
    AlignedValid 12 4 missing23074_23075 records23074_23075 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23074
    maskCheck23074 AlignedValid.nil

def missing23075_23076 : List (BitVec (edgeCount 12)) :=
  [missing23075]
abbrev records23075_23076 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23075]
theorem aligned23075_23076 :
    AlignedValid 12 4 missing23075_23076 records23075_23076 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23075
    maskCheck23075 AlignedValid.nil

def missing23074_23076 : List (BitVec (edgeCount 12)) :=
  missing23074_23075 ++ missing23075_23076
abbrev records23074_23076 : List Blob :=
  records23074_23075 ++ records23075_23076
theorem aligned23074_23076 :
    AlignedValid 12 4 missing23074_23076 records23074_23076 :=
  aligned23074_23075.append aligned23075_23076

def missing23072_23076 : List (BitVec (edgeCount 12)) :=
  missing23072_23074 ++ missing23074_23076
abbrev records23072_23076 : List Blob :=
  records23072_23074 ++ records23074_23076
theorem aligned23072_23076 :
    AlignedValid 12 4 missing23072_23076 records23072_23076 :=
  aligned23072_23074.append aligned23074_23076

def missing23076_23077 : List (BitVec (edgeCount 12)) :=
  [missing23076]
abbrev records23076_23077 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23076]
theorem aligned23076_23077 :
    AlignedValid 12 4 missing23076_23077 records23076_23077 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23076
    maskCheck23076 AlignedValid.nil

def missing23077_23078 : List (BitVec (edgeCount 12)) :=
  [missing23077]
abbrev records23077_23078 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23077]
theorem aligned23077_23078 :
    AlignedValid 12 4 missing23077_23078 records23077_23078 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23077
    maskCheck23077 AlignedValid.nil

def missing23076_23078 : List (BitVec (edgeCount 12)) :=
  missing23076_23077 ++ missing23077_23078
abbrev records23076_23078 : List Blob :=
  records23076_23077 ++ records23077_23078
theorem aligned23076_23078 :
    AlignedValid 12 4 missing23076_23078 records23076_23078 :=
  aligned23076_23077.append aligned23077_23078

def missing23078_23079 : List (BitVec (edgeCount 12)) :=
  [missing23078]
abbrev records23078_23079 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23078]
theorem aligned23078_23079 :
    AlignedValid 12 4 missing23078_23079 records23078_23079 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23078
    maskCheck23078 AlignedValid.nil

def missing23079_23080 : List (BitVec (edgeCount 12)) :=
  [missing23079]
abbrev records23079_23080 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23079]
theorem aligned23079_23080 :
    AlignedValid 12 4 missing23079_23080 records23079_23080 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23079
    maskCheck23079 AlignedValid.nil

def missing23078_23080 : List (BitVec (edgeCount 12)) :=
  missing23078_23079 ++ missing23079_23080
abbrev records23078_23080 : List Blob :=
  records23078_23079 ++ records23079_23080
theorem aligned23078_23080 :
    AlignedValid 12 4 missing23078_23080 records23078_23080 :=
  aligned23078_23079.append aligned23079_23080

def missing23076_23080 : List (BitVec (edgeCount 12)) :=
  missing23076_23078 ++ missing23078_23080
abbrev records23076_23080 : List Blob :=
  records23076_23078 ++ records23078_23080
theorem aligned23076_23080 :
    AlignedValid 12 4 missing23076_23080 records23076_23080 :=
  aligned23076_23078.append aligned23078_23080

def missing23072_23080 : List (BitVec (edgeCount 12)) :=
  missing23072_23076 ++ missing23076_23080
abbrev records23072_23080 : List Blob :=
  records23072_23076 ++ records23076_23080
theorem aligned23072_23080 :
    AlignedValid 12 4 missing23072_23080 records23072_23080 :=
  aligned23072_23076.append aligned23076_23080

def missing23080_23081 : List (BitVec (edgeCount 12)) :=
  [missing23080]
abbrev records23080_23081 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23080]
theorem aligned23080_23081 :
    AlignedValid 12 4 missing23080_23081 records23080_23081 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23080
    maskCheck23080 AlignedValid.nil

def missing23081_23082 : List (BitVec (edgeCount 12)) :=
  [missing23081]
abbrev records23081_23082 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23081]
theorem aligned23081_23082 :
    AlignedValid 12 4 missing23081_23082 records23081_23082 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23081
    maskCheck23081 AlignedValid.nil

def missing23080_23082 : List (BitVec (edgeCount 12)) :=
  missing23080_23081 ++ missing23081_23082
abbrev records23080_23082 : List Blob :=
  records23080_23081 ++ records23081_23082
theorem aligned23080_23082 :
    AlignedValid 12 4 missing23080_23082 records23080_23082 :=
  aligned23080_23081.append aligned23081_23082

def missing23082_23083 : List (BitVec (edgeCount 12)) :=
  [missing23082]
abbrev records23082_23083 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23082]
theorem aligned23082_23083 :
    AlignedValid 12 4 missing23082_23083 records23082_23083 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23082
    maskCheck23082 AlignedValid.nil

def missing23083_23084 : List (BitVec (edgeCount 12)) :=
  [missing23083]
abbrev records23083_23084 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23083]
theorem aligned23083_23084 :
    AlignedValid 12 4 missing23083_23084 records23083_23084 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23083
    maskCheck23083 AlignedValid.nil

def missing23082_23084 : List (BitVec (edgeCount 12)) :=
  missing23082_23083 ++ missing23083_23084
abbrev records23082_23084 : List Blob :=
  records23082_23083 ++ records23083_23084
theorem aligned23082_23084 :
    AlignedValid 12 4 missing23082_23084 records23082_23084 :=
  aligned23082_23083.append aligned23083_23084

def missing23080_23084 : List (BitVec (edgeCount 12)) :=
  missing23080_23082 ++ missing23082_23084
abbrev records23080_23084 : List Blob :=
  records23080_23082 ++ records23082_23084
theorem aligned23080_23084 :
    AlignedValid 12 4 missing23080_23084 records23080_23084 :=
  aligned23080_23082.append aligned23082_23084

def missing23084_23085 : List (BitVec (edgeCount 12)) :=
  [missing23084]
abbrev records23084_23085 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23084]
theorem aligned23084_23085 :
    AlignedValid 12 4 missing23084_23085 records23084_23085 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23084
    maskCheck23084 AlignedValid.nil

def missing23085_23086 : List (BitVec (edgeCount 12)) :=
  [missing23085]
abbrev records23085_23086 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23085]
theorem aligned23085_23086 :
    AlignedValid 12 4 missing23085_23086 records23085_23086 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23085
    maskCheck23085 AlignedValid.nil

def missing23084_23086 : List (BitVec (edgeCount 12)) :=
  missing23084_23085 ++ missing23085_23086
abbrev records23084_23086 : List Blob :=
  records23084_23085 ++ records23085_23086
theorem aligned23084_23086 :
    AlignedValid 12 4 missing23084_23086 records23084_23086 :=
  aligned23084_23085.append aligned23085_23086

def missing23086_23087 : List (BitVec (edgeCount 12)) :=
  [missing23086]
abbrev records23086_23087 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23086]
theorem aligned23086_23087 :
    AlignedValid 12 4 missing23086_23087 records23086_23087 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23086
    maskCheck23086 AlignedValid.nil

def missing23087_23088 : List (BitVec (edgeCount 12)) :=
  [missing23087]
abbrev records23087_23088 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23087]
theorem aligned23087_23088 :
    AlignedValid 12 4 missing23087_23088 records23087_23088 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23087
    maskCheck23087 AlignedValid.nil

def missing23086_23088 : List (BitVec (edgeCount 12)) :=
  missing23086_23087 ++ missing23087_23088
abbrev records23086_23088 : List Blob :=
  records23086_23087 ++ records23087_23088
theorem aligned23086_23088 :
    AlignedValid 12 4 missing23086_23088 records23086_23088 :=
  aligned23086_23087.append aligned23087_23088

def missing23084_23088 : List (BitVec (edgeCount 12)) :=
  missing23084_23086 ++ missing23086_23088
abbrev records23084_23088 : List Blob :=
  records23084_23086 ++ records23086_23088
theorem aligned23084_23088 :
    AlignedValid 12 4 missing23084_23088 records23084_23088 :=
  aligned23084_23086.append aligned23086_23088

def missing23080_23088 : List (BitVec (edgeCount 12)) :=
  missing23080_23084 ++ missing23084_23088
abbrev records23080_23088 : List Blob :=
  records23080_23084 ++ records23084_23088
theorem aligned23080_23088 :
    AlignedValid 12 4 missing23080_23088 records23080_23088 :=
  aligned23080_23084.append aligned23084_23088

def missing23072_23088 : List (BitVec (edgeCount 12)) :=
  missing23072_23080 ++ missing23080_23088
abbrev records23072_23088 : List Blob :=
  records23072_23080 ++ records23080_23088
theorem aligned23072_23088 :
    AlignedValid 12 4 missing23072_23088 records23072_23088 :=
  aligned23072_23080.append aligned23080_23088

def missing23088_23089 : List (BitVec (edgeCount 12)) :=
  [missing23088]
abbrev records23088_23089 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23088]
theorem aligned23088_23089 :
    AlignedValid 12 4 missing23088_23089 records23088_23089 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23088
    maskCheck23088 AlignedValid.nil

def missing23089_23090 : List (BitVec (edgeCount 12)) :=
  [missing23089]
abbrev records23089_23090 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23089]
theorem aligned23089_23090 :
    AlignedValid 12 4 missing23089_23090 records23089_23090 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23089
    maskCheck23089 AlignedValid.nil

def missing23088_23090 : List (BitVec (edgeCount 12)) :=
  missing23088_23089 ++ missing23089_23090
abbrev records23088_23090 : List Blob :=
  records23088_23089 ++ records23089_23090
theorem aligned23088_23090 :
    AlignedValid 12 4 missing23088_23090 records23088_23090 :=
  aligned23088_23089.append aligned23089_23090

def missing23090_23091 : List (BitVec (edgeCount 12)) :=
  [missing23090]
abbrev records23090_23091 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23090]
theorem aligned23090_23091 :
    AlignedValid 12 4 missing23090_23091 records23090_23091 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23090
    maskCheck23090 AlignedValid.nil

def missing23091_23092 : List (BitVec (edgeCount 12)) :=
  [missing23091]
abbrev records23091_23092 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23091]
theorem aligned23091_23092 :
    AlignedValid 12 4 missing23091_23092 records23091_23092 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23091
    maskCheck23091 AlignedValid.nil

def missing23090_23092 : List (BitVec (edgeCount 12)) :=
  missing23090_23091 ++ missing23091_23092
abbrev records23090_23092 : List Blob :=
  records23090_23091 ++ records23091_23092
theorem aligned23090_23092 :
    AlignedValid 12 4 missing23090_23092 records23090_23092 :=
  aligned23090_23091.append aligned23091_23092

def missing23088_23092 : List (BitVec (edgeCount 12)) :=
  missing23088_23090 ++ missing23090_23092
abbrev records23088_23092 : List Blob :=
  records23088_23090 ++ records23090_23092
theorem aligned23088_23092 :
    AlignedValid 12 4 missing23088_23092 records23088_23092 :=
  aligned23088_23090.append aligned23090_23092

def missing23092_23093 : List (BitVec (edgeCount 12)) :=
  [missing23092]
abbrev records23092_23093 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23092]
theorem aligned23092_23093 :
    AlignedValid 12 4 missing23092_23093 records23092_23093 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23092
    maskCheck23092 AlignedValid.nil

def missing23093_23094 : List (BitVec (edgeCount 12)) :=
  [missing23093]
abbrev records23093_23094 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23093]
theorem aligned23093_23094 :
    AlignedValid 12 4 missing23093_23094 records23093_23094 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23093
    maskCheck23093 AlignedValid.nil

def missing23092_23094 : List (BitVec (edgeCount 12)) :=
  missing23092_23093 ++ missing23093_23094
abbrev records23092_23094 : List Blob :=
  records23092_23093 ++ records23093_23094
theorem aligned23092_23094 :
    AlignedValid 12 4 missing23092_23094 records23092_23094 :=
  aligned23092_23093.append aligned23093_23094

def missing23094_23095 : List (BitVec (edgeCount 12)) :=
  [missing23094]
abbrev records23094_23095 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23094]
theorem aligned23094_23095 :
    AlignedValid 12 4 missing23094_23095 records23094_23095 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23094
    maskCheck23094 AlignedValid.nil

def missing23095_23096 : List (BitVec (edgeCount 12)) :=
  [missing23095]
abbrev records23095_23096 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23095]
theorem aligned23095_23096 :
    AlignedValid 12 4 missing23095_23096 records23095_23096 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23095
    maskCheck23095 AlignedValid.nil

def missing23094_23096 : List (BitVec (edgeCount 12)) :=
  missing23094_23095 ++ missing23095_23096
abbrev records23094_23096 : List Blob :=
  records23094_23095 ++ records23095_23096
theorem aligned23094_23096 :
    AlignedValid 12 4 missing23094_23096 records23094_23096 :=
  aligned23094_23095.append aligned23095_23096

def missing23092_23096 : List (BitVec (edgeCount 12)) :=
  missing23092_23094 ++ missing23094_23096
abbrev records23092_23096 : List Blob :=
  records23092_23094 ++ records23094_23096
theorem aligned23092_23096 :
    AlignedValid 12 4 missing23092_23096 records23092_23096 :=
  aligned23092_23094.append aligned23094_23096

def missing23088_23096 : List (BitVec (edgeCount 12)) :=
  missing23088_23092 ++ missing23092_23096
abbrev records23088_23096 : List Blob :=
  records23088_23092 ++ records23092_23096
theorem aligned23088_23096 :
    AlignedValid 12 4 missing23088_23096 records23088_23096 :=
  aligned23088_23092.append aligned23092_23096

def missing23096_23097 : List (BitVec (edgeCount 12)) :=
  [missing23096]
abbrev records23096_23097 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23096]
theorem aligned23096_23097 :
    AlignedValid 12 4 missing23096_23097 records23096_23097 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23096
    maskCheck23096 AlignedValid.nil

def missing23097_23098 : List (BitVec (edgeCount 12)) :=
  [missing23097]
abbrev records23097_23098 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23097]
theorem aligned23097_23098 :
    AlignedValid 12 4 missing23097_23098 records23097_23098 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23097
    maskCheck23097 AlignedValid.nil

def missing23096_23098 : List (BitVec (edgeCount 12)) :=
  missing23096_23097 ++ missing23097_23098
abbrev records23096_23098 : List Blob :=
  records23096_23097 ++ records23097_23098
theorem aligned23096_23098 :
    AlignedValid 12 4 missing23096_23098 records23096_23098 :=
  aligned23096_23097.append aligned23097_23098

def missing23098_23099 : List (BitVec (edgeCount 12)) :=
  [missing23098]
abbrev records23098_23099 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23098]
theorem aligned23098_23099 :
    AlignedValid 12 4 missing23098_23099 records23098_23099 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23098
    maskCheck23098 AlignedValid.nil

def missing23099_23100 : List (BitVec (edgeCount 12)) :=
  [missing23099]
abbrev records23099_23100 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23099]
theorem aligned23099_23100 :
    AlignedValid 12 4 missing23099_23100 records23099_23100 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23099
    maskCheck23099 AlignedValid.nil

def missing23098_23100 : List (BitVec (edgeCount 12)) :=
  missing23098_23099 ++ missing23099_23100
abbrev records23098_23100 : List Blob :=
  records23098_23099 ++ records23099_23100
theorem aligned23098_23100 :
    AlignedValid 12 4 missing23098_23100 records23098_23100 :=
  aligned23098_23099.append aligned23099_23100

def missing23096_23100 : List (BitVec (edgeCount 12)) :=
  missing23096_23098 ++ missing23098_23100
abbrev records23096_23100 : List Blob :=
  records23096_23098 ++ records23098_23100
theorem aligned23096_23100 :
    AlignedValid 12 4 missing23096_23100 records23096_23100 :=
  aligned23096_23098.append aligned23098_23100

def missing23100_23101 : List (BitVec (edgeCount 12)) :=
  [missing23100]
abbrev records23100_23101 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23100]
theorem aligned23100_23101 :
    AlignedValid 12 4 missing23100_23101 records23100_23101 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23100
    maskCheck23100 AlignedValid.nil

def missing23101_23102 : List (BitVec (edgeCount 12)) :=
  [missing23101]
abbrev records23101_23102 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23101]
theorem aligned23101_23102 :
    AlignedValid 12 4 missing23101_23102 records23101_23102 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23101
    maskCheck23101 AlignedValid.nil

def missing23100_23102 : List (BitVec (edgeCount 12)) :=
  missing23100_23101 ++ missing23101_23102
abbrev records23100_23102 : List Blob :=
  records23100_23101 ++ records23101_23102
theorem aligned23100_23102 :
    AlignedValid 12 4 missing23100_23102 records23100_23102 :=
  aligned23100_23101.append aligned23101_23102

def missing23102_23103 : List (BitVec (edgeCount 12)) :=
  [missing23102]
abbrev records23102_23103 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23102]
theorem aligned23102_23103 :
    AlignedValid 12 4 missing23102_23103 records23102_23103 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23102
    maskCheck23102 AlignedValid.nil

def missing23103_23104 : List (BitVec (edgeCount 12)) :=
  [missing23103]
abbrev records23103_23104 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23103]
theorem aligned23103_23104 :
    AlignedValid 12 4 missing23103_23104 records23103_23104 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23103
    maskCheck23103 AlignedValid.nil

def missing23102_23104 : List (BitVec (edgeCount 12)) :=
  missing23102_23103 ++ missing23103_23104
abbrev records23102_23104 : List Blob :=
  records23102_23103 ++ records23103_23104
theorem aligned23102_23104 :
    AlignedValid 12 4 missing23102_23104 records23102_23104 :=
  aligned23102_23103.append aligned23103_23104

def missing23100_23104 : List (BitVec (edgeCount 12)) :=
  missing23100_23102 ++ missing23102_23104
abbrev records23100_23104 : List Blob :=
  records23100_23102 ++ records23102_23104
theorem aligned23100_23104 :
    AlignedValid 12 4 missing23100_23104 records23100_23104 :=
  aligned23100_23102.append aligned23102_23104

def missing23096_23104 : List (BitVec (edgeCount 12)) :=
  missing23096_23100 ++ missing23100_23104
abbrev records23096_23104 : List Blob :=
  records23096_23100 ++ records23100_23104
theorem aligned23096_23104 :
    AlignedValid 12 4 missing23096_23104 records23096_23104 :=
  aligned23096_23100.append aligned23100_23104

def missing23088_23104 : List (BitVec (edgeCount 12)) :=
  missing23088_23096 ++ missing23096_23104
abbrev records23088_23104 : List Blob :=
  records23088_23096 ++ records23096_23104
theorem aligned23088_23104 :
    AlignedValid 12 4 missing23088_23104 records23088_23104 :=
  aligned23088_23096.append aligned23096_23104

def missing23072_23104 : List (BitVec (edgeCount 12)) :=
  missing23072_23088 ++ missing23088_23104
abbrev records23072_23104 : List Blob :=
  records23072_23088 ++ records23088_23104
theorem aligned23072_23104 :
    AlignedValid 12 4 missing23072_23104 records23072_23104 :=
  aligned23072_23088.append aligned23088_23104

def missing23040_23104 : List (BitVec (edgeCount 12)) :=
  missing23040_23072 ++ missing23072_23104
abbrev records23040_23104 : List Blob :=
  records23040_23072 ++ records23072_23104
theorem aligned23040_23104 :
    AlignedValid 12 4 missing23040_23104 records23040_23104 :=
  aligned23040_23072.append aligned23072_23104

def missing23104_23105 : List (BitVec (edgeCount 12)) :=
  [missing23104]
abbrev records23104_23105 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23104]
theorem aligned23104_23105 :
    AlignedValid 12 4 missing23104_23105 records23104_23105 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23104
    maskCheck23104 AlignedValid.nil

def missing23105_23106 : List (BitVec (edgeCount 12)) :=
  [missing23105]
abbrev records23105_23106 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23105]
theorem aligned23105_23106 :
    AlignedValid 12 4 missing23105_23106 records23105_23106 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23105
    maskCheck23105 AlignedValid.nil

def missing23104_23106 : List (BitVec (edgeCount 12)) :=
  missing23104_23105 ++ missing23105_23106
abbrev records23104_23106 : List Blob :=
  records23104_23105 ++ records23105_23106
theorem aligned23104_23106 :
    AlignedValid 12 4 missing23104_23106 records23104_23106 :=
  aligned23104_23105.append aligned23105_23106

def missing23106_23107 : List (BitVec (edgeCount 12)) :=
  [missing23106]
abbrev records23106_23107 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23106]
theorem aligned23106_23107 :
    AlignedValid 12 4 missing23106_23107 records23106_23107 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23106
    maskCheck23106 AlignedValid.nil

def missing23107_23108 : List (BitVec (edgeCount 12)) :=
  [missing23107]
abbrev records23107_23108 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23107]
theorem aligned23107_23108 :
    AlignedValid 12 4 missing23107_23108 records23107_23108 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23107
    maskCheck23107 AlignedValid.nil

def missing23106_23108 : List (BitVec (edgeCount 12)) :=
  missing23106_23107 ++ missing23107_23108
abbrev records23106_23108 : List Blob :=
  records23106_23107 ++ records23107_23108
theorem aligned23106_23108 :
    AlignedValid 12 4 missing23106_23108 records23106_23108 :=
  aligned23106_23107.append aligned23107_23108

def missing23104_23108 : List (BitVec (edgeCount 12)) :=
  missing23104_23106 ++ missing23106_23108
abbrev records23104_23108 : List Blob :=
  records23104_23106 ++ records23106_23108
theorem aligned23104_23108 :
    AlignedValid 12 4 missing23104_23108 records23104_23108 :=
  aligned23104_23106.append aligned23106_23108

def missing23108_23109 : List (BitVec (edgeCount 12)) :=
  [missing23108]
abbrev records23108_23109 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23108]
theorem aligned23108_23109 :
    AlignedValid 12 4 missing23108_23109 records23108_23109 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23108
    maskCheck23108 AlignedValid.nil

def missing23109_23110 : List (BitVec (edgeCount 12)) :=
  [missing23109]
abbrev records23109_23110 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23109]
theorem aligned23109_23110 :
    AlignedValid 12 4 missing23109_23110 records23109_23110 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23109
    maskCheck23109 AlignedValid.nil

def missing23108_23110 : List (BitVec (edgeCount 12)) :=
  missing23108_23109 ++ missing23109_23110
abbrev records23108_23110 : List Blob :=
  records23108_23109 ++ records23109_23110
theorem aligned23108_23110 :
    AlignedValid 12 4 missing23108_23110 records23108_23110 :=
  aligned23108_23109.append aligned23109_23110

def missing23110_23111 : List (BitVec (edgeCount 12)) :=
  [missing23110]
abbrev records23110_23111 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23110]
theorem aligned23110_23111 :
    AlignedValid 12 4 missing23110_23111 records23110_23111 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23110
    maskCheck23110 AlignedValid.nil

def missing23111_23112 : List (BitVec (edgeCount 12)) :=
  [missing23111]
abbrev records23111_23112 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23111]
theorem aligned23111_23112 :
    AlignedValid 12 4 missing23111_23112 records23111_23112 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23111
    maskCheck23111 AlignedValid.nil

def missing23110_23112 : List (BitVec (edgeCount 12)) :=
  missing23110_23111 ++ missing23111_23112
abbrev records23110_23112 : List Blob :=
  records23110_23111 ++ records23111_23112
theorem aligned23110_23112 :
    AlignedValid 12 4 missing23110_23112 records23110_23112 :=
  aligned23110_23111.append aligned23111_23112

def missing23108_23112 : List (BitVec (edgeCount 12)) :=
  missing23108_23110 ++ missing23110_23112
abbrev records23108_23112 : List Blob :=
  records23108_23110 ++ records23110_23112
theorem aligned23108_23112 :
    AlignedValid 12 4 missing23108_23112 records23108_23112 :=
  aligned23108_23110.append aligned23110_23112

def missing23104_23112 : List (BitVec (edgeCount 12)) :=
  missing23104_23108 ++ missing23108_23112
abbrev records23104_23112 : List Blob :=
  records23104_23108 ++ records23108_23112
theorem aligned23104_23112 :
    AlignedValid 12 4 missing23104_23112 records23104_23112 :=
  aligned23104_23108.append aligned23108_23112

def missing23112_23113 : List (BitVec (edgeCount 12)) :=
  [missing23112]
abbrev records23112_23113 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23112]
theorem aligned23112_23113 :
    AlignedValid 12 4 missing23112_23113 records23112_23113 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23112
    maskCheck23112 AlignedValid.nil

def missing23113_23114 : List (BitVec (edgeCount 12)) :=
  [missing23113]
abbrev records23113_23114 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23113]
theorem aligned23113_23114 :
    AlignedValid 12 4 missing23113_23114 records23113_23114 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23113
    maskCheck23113 AlignedValid.nil

def missing23112_23114 : List (BitVec (edgeCount 12)) :=
  missing23112_23113 ++ missing23113_23114
abbrev records23112_23114 : List Blob :=
  records23112_23113 ++ records23113_23114
theorem aligned23112_23114 :
    AlignedValid 12 4 missing23112_23114 records23112_23114 :=
  aligned23112_23113.append aligned23113_23114

def missing23114_23115 : List (BitVec (edgeCount 12)) :=
  [missing23114]
abbrev records23114_23115 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23114]
theorem aligned23114_23115 :
    AlignedValid 12 4 missing23114_23115 records23114_23115 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23114
    maskCheck23114 AlignedValid.nil

def missing23115_23116 : List (BitVec (edgeCount 12)) :=
  [missing23115]
abbrev records23115_23116 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23115]
theorem aligned23115_23116 :
    AlignedValid 12 4 missing23115_23116 records23115_23116 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23115
    maskCheck23115 AlignedValid.nil

def missing23114_23116 : List (BitVec (edgeCount 12)) :=
  missing23114_23115 ++ missing23115_23116
abbrev records23114_23116 : List Blob :=
  records23114_23115 ++ records23115_23116
theorem aligned23114_23116 :
    AlignedValid 12 4 missing23114_23116 records23114_23116 :=
  aligned23114_23115.append aligned23115_23116

def missing23112_23116 : List (BitVec (edgeCount 12)) :=
  missing23112_23114 ++ missing23114_23116
abbrev records23112_23116 : List Blob :=
  records23112_23114 ++ records23114_23116
theorem aligned23112_23116 :
    AlignedValid 12 4 missing23112_23116 records23112_23116 :=
  aligned23112_23114.append aligned23114_23116

def missing23116_23117 : List (BitVec (edgeCount 12)) :=
  [missing23116]
abbrev records23116_23117 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23116]
theorem aligned23116_23117 :
    AlignedValid 12 4 missing23116_23117 records23116_23117 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23116
    maskCheck23116 AlignedValid.nil

def missing23117_23118 : List (BitVec (edgeCount 12)) :=
  [missing23117]
abbrev records23117_23118 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23117]
theorem aligned23117_23118 :
    AlignedValid 12 4 missing23117_23118 records23117_23118 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23117
    maskCheck23117 AlignedValid.nil

def missing23116_23118 : List (BitVec (edgeCount 12)) :=
  missing23116_23117 ++ missing23117_23118
abbrev records23116_23118 : List Blob :=
  records23116_23117 ++ records23117_23118
theorem aligned23116_23118 :
    AlignedValid 12 4 missing23116_23118 records23116_23118 :=
  aligned23116_23117.append aligned23117_23118

def missing23118_23119 : List (BitVec (edgeCount 12)) :=
  [missing23118]
abbrev records23118_23119 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23118]
theorem aligned23118_23119 :
    AlignedValid 12 4 missing23118_23119 records23118_23119 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23118
    maskCheck23118 AlignedValid.nil

def missing23119_23120 : List (BitVec (edgeCount 12)) :=
  [missing23119]
abbrev records23119_23120 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23119]
theorem aligned23119_23120 :
    AlignedValid 12 4 missing23119_23120 records23119_23120 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23119
    maskCheck23119 AlignedValid.nil

def missing23118_23120 : List (BitVec (edgeCount 12)) :=
  missing23118_23119 ++ missing23119_23120
abbrev records23118_23120 : List Blob :=
  records23118_23119 ++ records23119_23120
theorem aligned23118_23120 :
    AlignedValid 12 4 missing23118_23120 records23118_23120 :=
  aligned23118_23119.append aligned23119_23120

def missing23116_23120 : List (BitVec (edgeCount 12)) :=
  missing23116_23118 ++ missing23118_23120
abbrev records23116_23120 : List Blob :=
  records23116_23118 ++ records23118_23120
theorem aligned23116_23120 :
    AlignedValid 12 4 missing23116_23120 records23116_23120 :=
  aligned23116_23118.append aligned23118_23120

def missing23112_23120 : List (BitVec (edgeCount 12)) :=
  missing23112_23116 ++ missing23116_23120
abbrev records23112_23120 : List Blob :=
  records23112_23116 ++ records23116_23120
theorem aligned23112_23120 :
    AlignedValid 12 4 missing23112_23120 records23112_23120 :=
  aligned23112_23116.append aligned23116_23120

def missing23104_23120 : List (BitVec (edgeCount 12)) :=
  missing23104_23112 ++ missing23112_23120
abbrev records23104_23120 : List Blob :=
  records23104_23112 ++ records23112_23120
theorem aligned23104_23120 :
    AlignedValid 12 4 missing23104_23120 records23104_23120 :=
  aligned23104_23112.append aligned23112_23120

def missing23120_23121 : List (BitVec (edgeCount 12)) :=
  [missing23120]
abbrev records23120_23121 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23120]
theorem aligned23120_23121 :
    AlignedValid 12 4 missing23120_23121 records23120_23121 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23120
    maskCheck23120 AlignedValid.nil

def missing23121_23122 : List (BitVec (edgeCount 12)) :=
  [missing23121]
abbrev records23121_23122 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23121]
theorem aligned23121_23122 :
    AlignedValid 12 4 missing23121_23122 records23121_23122 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23121
    maskCheck23121 AlignedValid.nil

def missing23120_23122 : List (BitVec (edgeCount 12)) :=
  missing23120_23121 ++ missing23121_23122
abbrev records23120_23122 : List Blob :=
  records23120_23121 ++ records23121_23122
theorem aligned23120_23122 :
    AlignedValid 12 4 missing23120_23122 records23120_23122 :=
  aligned23120_23121.append aligned23121_23122

def missing23122_23123 : List (BitVec (edgeCount 12)) :=
  [missing23122]
abbrev records23122_23123 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23122]
theorem aligned23122_23123 :
    AlignedValid 12 4 missing23122_23123 records23122_23123 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23122
    maskCheck23122 AlignedValid.nil

def missing23123_23124 : List (BitVec (edgeCount 12)) :=
  [missing23123]
abbrev records23123_23124 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23123]
theorem aligned23123_23124 :
    AlignedValid 12 4 missing23123_23124 records23123_23124 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23123
    maskCheck23123 AlignedValid.nil

def missing23122_23124 : List (BitVec (edgeCount 12)) :=
  missing23122_23123 ++ missing23123_23124
abbrev records23122_23124 : List Blob :=
  records23122_23123 ++ records23123_23124
theorem aligned23122_23124 :
    AlignedValid 12 4 missing23122_23124 records23122_23124 :=
  aligned23122_23123.append aligned23123_23124

def missing23120_23124 : List (BitVec (edgeCount 12)) :=
  missing23120_23122 ++ missing23122_23124
abbrev records23120_23124 : List Blob :=
  records23120_23122 ++ records23122_23124
theorem aligned23120_23124 :
    AlignedValid 12 4 missing23120_23124 records23120_23124 :=
  aligned23120_23122.append aligned23122_23124

def missing23124_23125 : List (BitVec (edgeCount 12)) :=
  [missing23124]
abbrev records23124_23125 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23124]
theorem aligned23124_23125 :
    AlignedValid 12 4 missing23124_23125 records23124_23125 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23124
    maskCheck23124 AlignedValid.nil

def missing23125_23126 : List (BitVec (edgeCount 12)) :=
  [missing23125]
abbrev records23125_23126 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23125]
theorem aligned23125_23126 :
    AlignedValid 12 4 missing23125_23126 records23125_23126 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23125
    maskCheck23125 AlignedValid.nil

def missing23124_23126 : List (BitVec (edgeCount 12)) :=
  missing23124_23125 ++ missing23125_23126
abbrev records23124_23126 : List Blob :=
  records23124_23125 ++ records23125_23126
theorem aligned23124_23126 :
    AlignedValid 12 4 missing23124_23126 records23124_23126 :=
  aligned23124_23125.append aligned23125_23126

def missing23126_23127 : List (BitVec (edgeCount 12)) :=
  [missing23126]
abbrev records23126_23127 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23126]
theorem aligned23126_23127 :
    AlignedValid 12 4 missing23126_23127 records23126_23127 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23126
    maskCheck23126 AlignedValid.nil

def missing23127_23128 : List (BitVec (edgeCount 12)) :=
  [missing23127]
abbrev records23127_23128 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23127]
theorem aligned23127_23128 :
    AlignedValid 12 4 missing23127_23128 records23127_23128 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23127
    maskCheck23127 AlignedValid.nil

def missing23126_23128 : List (BitVec (edgeCount 12)) :=
  missing23126_23127 ++ missing23127_23128
abbrev records23126_23128 : List Blob :=
  records23126_23127 ++ records23127_23128
theorem aligned23126_23128 :
    AlignedValid 12 4 missing23126_23128 records23126_23128 :=
  aligned23126_23127.append aligned23127_23128

def missing23124_23128 : List (BitVec (edgeCount 12)) :=
  missing23124_23126 ++ missing23126_23128
abbrev records23124_23128 : List Blob :=
  records23124_23126 ++ records23126_23128
theorem aligned23124_23128 :
    AlignedValid 12 4 missing23124_23128 records23124_23128 :=
  aligned23124_23126.append aligned23126_23128

def missing23120_23128 : List (BitVec (edgeCount 12)) :=
  missing23120_23124 ++ missing23124_23128
abbrev records23120_23128 : List Blob :=
  records23120_23124 ++ records23124_23128
theorem aligned23120_23128 :
    AlignedValid 12 4 missing23120_23128 records23120_23128 :=
  aligned23120_23124.append aligned23124_23128

def missing23128_23129 : List (BitVec (edgeCount 12)) :=
  [missing23128]
abbrev records23128_23129 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23128]
theorem aligned23128_23129 :
    AlignedValid 12 4 missing23128_23129 records23128_23129 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23128
    maskCheck23128 AlignedValid.nil

def missing23129_23130 : List (BitVec (edgeCount 12)) :=
  [missing23129]
abbrev records23129_23130 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23129]
theorem aligned23129_23130 :
    AlignedValid 12 4 missing23129_23130 records23129_23130 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23129
    maskCheck23129 AlignedValid.nil

def missing23128_23130 : List (BitVec (edgeCount 12)) :=
  missing23128_23129 ++ missing23129_23130
abbrev records23128_23130 : List Blob :=
  records23128_23129 ++ records23129_23130
theorem aligned23128_23130 :
    AlignedValid 12 4 missing23128_23130 records23128_23130 :=
  aligned23128_23129.append aligned23129_23130

def missing23130_23131 : List (BitVec (edgeCount 12)) :=
  [missing23130]
abbrev records23130_23131 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23130]
theorem aligned23130_23131 :
    AlignedValid 12 4 missing23130_23131 records23130_23131 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23130
    maskCheck23130 AlignedValid.nil

def missing23131_23132 : List (BitVec (edgeCount 12)) :=
  [missing23131]
abbrev records23131_23132 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23131]
theorem aligned23131_23132 :
    AlignedValid 12 4 missing23131_23132 records23131_23132 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23131
    maskCheck23131 AlignedValid.nil

def missing23130_23132 : List (BitVec (edgeCount 12)) :=
  missing23130_23131 ++ missing23131_23132
abbrev records23130_23132 : List Blob :=
  records23130_23131 ++ records23131_23132
theorem aligned23130_23132 :
    AlignedValid 12 4 missing23130_23132 records23130_23132 :=
  aligned23130_23131.append aligned23131_23132

def missing23128_23132 : List (BitVec (edgeCount 12)) :=
  missing23128_23130 ++ missing23130_23132
abbrev records23128_23132 : List Blob :=
  records23128_23130 ++ records23130_23132
theorem aligned23128_23132 :
    AlignedValid 12 4 missing23128_23132 records23128_23132 :=
  aligned23128_23130.append aligned23130_23132

def missing23132_23133 : List (BitVec (edgeCount 12)) :=
  [missing23132]
abbrev records23132_23133 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23132]
theorem aligned23132_23133 :
    AlignedValid 12 4 missing23132_23133 records23132_23133 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23132
    maskCheck23132 AlignedValid.nil

def missing23133_23134 : List (BitVec (edgeCount 12)) :=
  [missing23133]
abbrev records23133_23134 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23133]
theorem aligned23133_23134 :
    AlignedValid 12 4 missing23133_23134 records23133_23134 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23133
    maskCheck23133 AlignedValid.nil

def missing23132_23134 : List (BitVec (edgeCount 12)) :=
  missing23132_23133 ++ missing23133_23134
abbrev records23132_23134 : List Blob :=
  records23132_23133 ++ records23133_23134
theorem aligned23132_23134 :
    AlignedValid 12 4 missing23132_23134 records23132_23134 :=
  aligned23132_23133.append aligned23133_23134

def missing23134_23135 : List (BitVec (edgeCount 12)) :=
  [missing23134]
abbrev records23134_23135 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23134]
theorem aligned23134_23135 :
    AlignedValid 12 4 missing23134_23135 records23134_23135 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23134
    maskCheck23134 AlignedValid.nil

def missing23135_23136 : List (BitVec (edgeCount 12)) :=
  [missing23135]
abbrev records23135_23136 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23135]
theorem aligned23135_23136 :
    AlignedValid 12 4 missing23135_23136 records23135_23136 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23135
    maskCheck23135 AlignedValid.nil

def missing23134_23136 : List (BitVec (edgeCount 12)) :=
  missing23134_23135 ++ missing23135_23136
abbrev records23134_23136 : List Blob :=
  records23134_23135 ++ records23135_23136
theorem aligned23134_23136 :
    AlignedValid 12 4 missing23134_23136 records23134_23136 :=
  aligned23134_23135.append aligned23135_23136

def missing23132_23136 : List (BitVec (edgeCount 12)) :=
  missing23132_23134 ++ missing23134_23136
abbrev records23132_23136 : List Blob :=
  records23132_23134 ++ records23134_23136
theorem aligned23132_23136 :
    AlignedValid 12 4 missing23132_23136 records23132_23136 :=
  aligned23132_23134.append aligned23134_23136

def missing23128_23136 : List (BitVec (edgeCount 12)) :=
  missing23128_23132 ++ missing23132_23136
abbrev records23128_23136 : List Blob :=
  records23128_23132 ++ records23132_23136
theorem aligned23128_23136 :
    AlignedValid 12 4 missing23128_23136 records23128_23136 :=
  aligned23128_23132.append aligned23132_23136

def missing23120_23136 : List (BitVec (edgeCount 12)) :=
  missing23120_23128 ++ missing23128_23136
abbrev records23120_23136 : List Blob :=
  records23120_23128 ++ records23128_23136
theorem aligned23120_23136 :
    AlignedValid 12 4 missing23120_23136 records23120_23136 :=
  aligned23120_23128.append aligned23128_23136

def missing23104_23136 : List (BitVec (edgeCount 12)) :=
  missing23104_23120 ++ missing23120_23136
abbrev records23104_23136 : List Blob :=
  records23104_23120 ++ records23120_23136
theorem aligned23104_23136 :
    AlignedValid 12 4 missing23104_23136 records23104_23136 :=
  aligned23104_23120.append aligned23120_23136

def missing23136_23137 : List (BitVec (edgeCount 12)) :=
  [missing23136]
abbrev records23136_23137 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23136]
theorem aligned23136_23137 :
    AlignedValid 12 4 missing23136_23137 records23136_23137 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23136
    maskCheck23136 AlignedValid.nil

def missing23137_23138 : List (BitVec (edgeCount 12)) :=
  [missing23137]
abbrev records23137_23138 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23137]
theorem aligned23137_23138 :
    AlignedValid 12 4 missing23137_23138 records23137_23138 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23137
    maskCheck23137 AlignedValid.nil

def missing23136_23138 : List (BitVec (edgeCount 12)) :=
  missing23136_23137 ++ missing23137_23138
abbrev records23136_23138 : List Blob :=
  records23136_23137 ++ records23137_23138
theorem aligned23136_23138 :
    AlignedValid 12 4 missing23136_23138 records23136_23138 :=
  aligned23136_23137.append aligned23137_23138

def missing23138_23139 : List (BitVec (edgeCount 12)) :=
  [missing23138]
abbrev records23138_23139 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23138]
theorem aligned23138_23139 :
    AlignedValid 12 4 missing23138_23139 records23138_23139 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23138
    maskCheck23138 AlignedValid.nil

def missing23139_23140 : List (BitVec (edgeCount 12)) :=
  [missing23139]
abbrev records23139_23140 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23139]
theorem aligned23139_23140 :
    AlignedValid 12 4 missing23139_23140 records23139_23140 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23139
    maskCheck23139 AlignedValid.nil

def missing23138_23140 : List (BitVec (edgeCount 12)) :=
  missing23138_23139 ++ missing23139_23140
abbrev records23138_23140 : List Blob :=
  records23138_23139 ++ records23139_23140
theorem aligned23138_23140 :
    AlignedValid 12 4 missing23138_23140 records23138_23140 :=
  aligned23138_23139.append aligned23139_23140

def missing23136_23140 : List (BitVec (edgeCount 12)) :=
  missing23136_23138 ++ missing23138_23140
abbrev records23136_23140 : List Blob :=
  records23136_23138 ++ records23138_23140
theorem aligned23136_23140 :
    AlignedValid 12 4 missing23136_23140 records23136_23140 :=
  aligned23136_23138.append aligned23138_23140

def missing23140_23141 : List (BitVec (edgeCount 12)) :=
  [missing23140]
abbrev records23140_23141 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23140]
theorem aligned23140_23141 :
    AlignedValid 12 4 missing23140_23141 records23140_23141 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23140
    maskCheck23140 AlignedValid.nil

def missing23141_23142 : List (BitVec (edgeCount 12)) :=
  [missing23141]
abbrev records23141_23142 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23141]
theorem aligned23141_23142 :
    AlignedValid 12 4 missing23141_23142 records23141_23142 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23141
    maskCheck23141 AlignedValid.nil

def missing23140_23142 : List (BitVec (edgeCount 12)) :=
  missing23140_23141 ++ missing23141_23142
abbrev records23140_23142 : List Blob :=
  records23140_23141 ++ records23141_23142
theorem aligned23140_23142 :
    AlignedValid 12 4 missing23140_23142 records23140_23142 :=
  aligned23140_23141.append aligned23141_23142

def missing23142_23143 : List (BitVec (edgeCount 12)) :=
  [missing23142]
abbrev records23142_23143 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23142]
theorem aligned23142_23143 :
    AlignedValid 12 4 missing23142_23143 records23142_23143 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23142
    maskCheck23142 AlignedValid.nil

def missing23143_23144 : List (BitVec (edgeCount 12)) :=
  [missing23143]
abbrev records23143_23144 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23143]
theorem aligned23143_23144 :
    AlignedValid 12 4 missing23143_23144 records23143_23144 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23143
    maskCheck23143 AlignedValid.nil

def missing23142_23144 : List (BitVec (edgeCount 12)) :=
  missing23142_23143 ++ missing23143_23144
abbrev records23142_23144 : List Blob :=
  records23142_23143 ++ records23143_23144
theorem aligned23142_23144 :
    AlignedValid 12 4 missing23142_23144 records23142_23144 :=
  aligned23142_23143.append aligned23143_23144

def missing23140_23144 : List (BitVec (edgeCount 12)) :=
  missing23140_23142 ++ missing23142_23144
abbrev records23140_23144 : List Blob :=
  records23140_23142 ++ records23142_23144
theorem aligned23140_23144 :
    AlignedValid 12 4 missing23140_23144 records23140_23144 :=
  aligned23140_23142.append aligned23142_23144

def missing23136_23144 : List (BitVec (edgeCount 12)) :=
  missing23136_23140 ++ missing23140_23144
abbrev records23136_23144 : List Blob :=
  records23136_23140 ++ records23140_23144
theorem aligned23136_23144 :
    AlignedValid 12 4 missing23136_23144 records23136_23144 :=
  aligned23136_23140.append aligned23140_23144

def missing23144_23145 : List (BitVec (edgeCount 12)) :=
  [missing23144]
abbrev records23144_23145 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23144]
theorem aligned23144_23145 :
    AlignedValid 12 4 missing23144_23145 records23144_23145 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23144
    maskCheck23144 AlignedValid.nil

def missing23145_23146 : List (BitVec (edgeCount 12)) :=
  [missing23145]
abbrev records23145_23146 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23145]
theorem aligned23145_23146 :
    AlignedValid 12 4 missing23145_23146 records23145_23146 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23145
    maskCheck23145 AlignedValid.nil

def missing23144_23146 : List (BitVec (edgeCount 12)) :=
  missing23144_23145 ++ missing23145_23146
abbrev records23144_23146 : List Blob :=
  records23144_23145 ++ records23145_23146
theorem aligned23144_23146 :
    AlignedValid 12 4 missing23144_23146 records23144_23146 :=
  aligned23144_23145.append aligned23145_23146

def missing23146_23147 : List (BitVec (edgeCount 12)) :=
  [missing23146]
abbrev records23146_23147 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23146]
theorem aligned23146_23147 :
    AlignedValid 12 4 missing23146_23147 records23146_23147 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23146
    maskCheck23146 AlignedValid.nil

def missing23147_23148 : List (BitVec (edgeCount 12)) :=
  [missing23147]
abbrev records23147_23148 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23147]
theorem aligned23147_23148 :
    AlignedValid 12 4 missing23147_23148 records23147_23148 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23147
    maskCheck23147 AlignedValid.nil

def missing23146_23148 : List (BitVec (edgeCount 12)) :=
  missing23146_23147 ++ missing23147_23148
abbrev records23146_23148 : List Blob :=
  records23146_23147 ++ records23147_23148
theorem aligned23146_23148 :
    AlignedValid 12 4 missing23146_23148 records23146_23148 :=
  aligned23146_23147.append aligned23147_23148

def missing23144_23148 : List (BitVec (edgeCount 12)) :=
  missing23144_23146 ++ missing23146_23148
abbrev records23144_23148 : List Blob :=
  records23144_23146 ++ records23146_23148
theorem aligned23144_23148 :
    AlignedValid 12 4 missing23144_23148 records23144_23148 :=
  aligned23144_23146.append aligned23146_23148

def missing23148_23149 : List (BitVec (edgeCount 12)) :=
  [missing23148]
abbrev records23148_23149 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23148]
theorem aligned23148_23149 :
    AlignedValid 12 4 missing23148_23149 records23148_23149 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23148
    maskCheck23148 AlignedValid.nil

def missing23149_23150 : List (BitVec (edgeCount 12)) :=
  [missing23149]
abbrev records23149_23150 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23149]
theorem aligned23149_23150 :
    AlignedValid 12 4 missing23149_23150 records23149_23150 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23149
    maskCheck23149 AlignedValid.nil

def missing23148_23150 : List (BitVec (edgeCount 12)) :=
  missing23148_23149 ++ missing23149_23150
abbrev records23148_23150 : List Blob :=
  records23148_23149 ++ records23149_23150
theorem aligned23148_23150 :
    AlignedValid 12 4 missing23148_23150 records23148_23150 :=
  aligned23148_23149.append aligned23149_23150

def missing23150_23151 : List (BitVec (edgeCount 12)) :=
  [missing23150]
abbrev records23150_23151 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23150]
theorem aligned23150_23151 :
    AlignedValid 12 4 missing23150_23151 records23150_23151 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23150
    maskCheck23150 AlignedValid.nil

def missing23151_23152 : List (BitVec (edgeCount 12)) :=
  [missing23151]
abbrev records23151_23152 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23151]
theorem aligned23151_23152 :
    AlignedValid 12 4 missing23151_23152 records23151_23152 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23151
    maskCheck23151 AlignedValid.nil

def missing23150_23152 : List (BitVec (edgeCount 12)) :=
  missing23150_23151 ++ missing23151_23152
abbrev records23150_23152 : List Blob :=
  records23150_23151 ++ records23151_23152
theorem aligned23150_23152 :
    AlignedValid 12 4 missing23150_23152 records23150_23152 :=
  aligned23150_23151.append aligned23151_23152

def missing23148_23152 : List (BitVec (edgeCount 12)) :=
  missing23148_23150 ++ missing23150_23152
abbrev records23148_23152 : List Blob :=
  records23148_23150 ++ records23150_23152
theorem aligned23148_23152 :
    AlignedValid 12 4 missing23148_23152 records23148_23152 :=
  aligned23148_23150.append aligned23150_23152

def missing23144_23152 : List (BitVec (edgeCount 12)) :=
  missing23144_23148 ++ missing23148_23152
abbrev records23144_23152 : List Blob :=
  records23144_23148 ++ records23148_23152
theorem aligned23144_23152 :
    AlignedValid 12 4 missing23144_23152 records23144_23152 :=
  aligned23144_23148.append aligned23148_23152

def missing23136_23152 : List (BitVec (edgeCount 12)) :=
  missing23136_23144 ++ missing23144_23152
abbrev records23136_23152 : List Blob :=
  records23136_23144 ++ records23144_23152
theorem aligned23136_23152 :
    AlignedValid 12 4 missing23136_23152 records23136_23152 :=
  aligned23136_23144.append aligned23144_23152

def missing23152_23153 : List (BitVec (edgeCount 12)) :=
  [missing23152]
abbrev records23152_23153 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23152]
theorem aligned23152_23153 :
    AlignedValid 12 4 missing23152_23153 records23152_23153 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23152
    maskCheck23152 AlignedValid.nil

def missing23153_23154 : List (BitVec (edgeCount 12)) :=
  [missing23153]
abbrev records23153_23154 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23153]
theorem aligned23153_23154 :
    AlignedValid 12 4 missing23153_23154 records23153_23154 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23153
    maskCheck23153 AlignedValid.nil

def missing23152_23154 : List (BitVec (edgeCount 12)) :=
  missing23152_23153 ++ missing23153_23154
abbrev records23152_23154 : List Blob :=
  records23152_23153 ++ records23153_23154
theorem aligned23152_23154 :
    AlignedValid 12 4 missing23152_23154 records23152_23154 :=
  aligned23152_23153.append aligned23153_23154

def missing23154_23155 : List (BitVec (edgeCount 12)) :=
  [missing23154]
abbrev records23154_23155 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23154]
theorem aligned23154_23155 :
    AlignedValid 12 4 missing23154_23155 records23154_23155 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23154
    maskCheck23154 AlignedValid.nil

def missing23155_23156 : List (BitVec (edgeCount 12)) :=
  [missing23155]
abbrev records23155_23156 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23155]
theorem aligned23155_23156 :
    AlignedValid 12 4 missing23155_23156 records23155_23156 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23155
    maskCheck23155 AlignedValid.nil

def missing23154_23156 : List (BitVec (edgeCount 12)) :=
  missing23154_23155 ++ missing23155_23156
abbrev records23154_23156 : List Blob :=
  records23154_23155 ++ records23155_23156
theorem aligned23154_23156 :
    AlignedValid 12 4 missing23154_23156 records23154_23156 :=
  aligned23154_23155.append aligned23155_23156

def missing23152_23156 : List (BitVec (edgeCount 12)) :=
  missing23152_23154 ++ missing23154_23156
abbrev records23152_23156 : List Blob :=
  records23152_23154 ++ records23154_23156
theorem aligned23152_23156 :
    AlignedValid 12 4 missing23152_23156 records23152_23156 :=
  aligned23152_23154.append aligned23154_23156

def missing23156_23157 : List (BitVec (edgeCount 12)) :=
  [missing23156]
abbrev records23156_23157 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23156]
theorem aligned23156_23157 :
    AlignedValid 12 4 missing23156_23157 records23156_23157 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23156
    maskCheck23156 AlignedValid.nil

def missing23157_23158 : List (BitVec (edgeCount 12)) :=
  [missing23157]
abbrev records23157_23158 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23157]
theorem aligned23157_23158 :
    AlignedValid 12 4 missing23157_23158 records23157_23158 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23157
    maskCheck23157 AlignedValid.nil

def missing23156_23158 : List (BitVec (edgeCount 12)) :=
  missing23156_23157 ++ missing23157_23158
abbrev records23156_23158 : List Blob :=
  records23156_23157 ++ records23157_23158
theorem aligned23156_23158 :
    AlignedValid 12 4 missing23156_23158 records23156_23158 :=
  aligned23156_23157.append aligned23157_23158

def missing23158_23159 : List (BitVec (edgeCount 12)) :=
  [missing23158]
abbrev records23158_23159 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23158]
theorem aligned23158_23159 :
    AlignedValid 12 4 missing23158_23159 records23158_23159 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23158
    maskCheck23158 AlignedValid.nil

def missing23159_23160 : List (BitVec (edgeCount 12)) :=
  [missing23159]
abbrev records23159_23160 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23159]
theorem aligned23159_23160 :
    AlignedValid 12 4 missing23159_23160 records23159_23160 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23159
    maskCheck23159 AlignedValid.nil

def missing23158_23160 : List (BitVec (edgeCount 12)) :=
  missing23158_23159 ++ missing23159_23160
abbrev records23158_23160 : List Blob :=
  records23158_23159 ++ records23159_23160
theorem aligned23158_23160 :
    AlignedValid 12 4 missing23158_23160 records23158_23160 :=
  aligned23158_23159.append aligned23159_23160

def missing23156_23160 : List (BitVec (edgeCount 12)) :=
  missing23156_23158 ++ missing23158_23160
abbrev records23156_23160 : List Blob :=
  records23156_23158 ++ records23158_23160
theorem aligned23156_23160 :
    AlignedValid 12 4 missing23156_23160 records23156_23160 :=
  aligned23156_23158.append aligned23158_23160

def missing23152_23160 : List (BitVec (edgeCount 12)) :=
  missing23152_23156 ++ missing23156_23160
abbrev records23152_23160 : List Blob :=
  records23152_23156 ++ records23156_23160
theorem aligned23152_23160 :
    AlignedValid 12 4 missing23152_23160 records23152_23160 :=
  aligned23152_23156.append aligned23156_23160

def missing23160_23161 : List (BitVec (edgeCount 12)) :=
  [missing23160]
abbrev records23160_23161 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23160]
theorem aligned23160_23161 :
    AlignedValid 12 4 missing23160_23161 records23160_23161 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23160
    maskCheck23160 AlignedValid.nil

def missing23161_23162 : List (BitVec (edgeCount 12)) :=
  [missing23161]
abbrev records23161_23162 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23161]
theorem aligned23161_23162 :
    AlignedValid 12 4 missing23161_23162 records23161_23162 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23161
    maskCheck23161 AlignedValid.nil

def missing23160_23162 : List (BitVec (edgeCount 12)) :=
  missing23160_23161 ++ missing23161_23162
abbrev records23160_23162 : List Blob :=
  records23160_23161 ++ records23161_23162
theorem aligned23160_23162 :
    AlignedValid 12 4 missing23160_23162 records23160_23162 :=
  aligned23160_23161.append aligned23161_23162

def missing23162_23163 : List (BitVec (edgeCount 12)) :=
  [missing23162]
abbrev records23162_23163 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23162]
theorem aligned23162_23163 :
    AlignedValid 12 4 missing23162_23163 records23162_23163 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23162
    maskCheck23162 AlignedValid.nil

def missing23163_23164 : List (BitVec (edgeCount 12)) :=
  [missing23163]
abbrev records23163_23164 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23163]
theorem aligned23163_23164 :
    AlignedValid 12 4 missing23163_23164 records23163_23164 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23163
    maskCheck23163 AlignedValid.nil

def missing23162_23164 : List (BitVec (edgeCount 12)) :=
  missing23162_23163 ++ missing23163_23164
abbrev records23162_23164 : List Blob :=
  records23162_23163 ++ records23163_23164
theorem aligned23162_23164 :
    AlignedValid 12 4 missing23162_23164 records23162_23164 :=
  aligned23162_23163.append aligned23163_23164

def missing23160_23164 : List (BitVec (edgeCount 12)) :=
  missing23160_23162 ++ missing23162_23164
abbrev records23160_23164 : List Blob :=
  records23160_23162 ++ records23162_23164
theorem aligned23160_23164 :
    AlignedValid 12 4 missing23160_23164 records23160_23164 :=
  aligned23160_23162.append aligned23162_23164

def missing23164_23165 : List (BitVec (edgeCount 12)) :=
  [missing23164]
abbrev records23164_23165 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23164]
theorem aligned23164_23165 :
    AlignedValid 12 4 missing23164_23165 records23164_23165 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23164
    maskCheck23164 AlignedValid.nil

def missing23165_23166 : List (BitVec (edgeCount 12)) :=
  [missing23165]
abbrev records23165_23166 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23165]
theorem aligned23165_23166 :
    AlignedValid 12 4 missing23165_23166 records23165_23166 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23165
    maskCheck23165 AlignedValid.nil

def missing23164_23166 : List (BitVec (edgeCount 12)) :=
  missing23164_23165 ++ missing23165_23166
abbrev records23164_23166 : List Blob :=
  records23164_23165 ++ records23165_23166
theorem aligned23164_23166 :
    AlignedValid 12 4 missing23164_23166 records23164_23166 :=
  aligned23164_23165.append aligned23165_23166

def missing23166_23167 : List (BitVec (edgeCount 12)) :=
  [missing23166]
abbrev records23166_23167 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23166]
theorem aligned23166_23167 :
    AlignedValid 12 4 missing23166_23167 records23166_23167 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23166
    maskCheck23166 AlignedValid.nil

def missing23167_23168 : List (BitVec (edgeCount 12)) :=
  [missing23167]
abbrev records23167_23168 : List Blob :=
  [StrongPackedBucketN12A4Shard180.record23167]
theorem aligned23167_23168 :
    AlignedValid 12 4 missing23167_23168 records23167_23168 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard180.check23167
    maskCheck23167 AlignedValid.nil

def missing23166_23168 : List (BitVec (edgeCount 12)) :=
  missing23166_23167 ++ missing23167_23168
abbrev records23166_23168 : List Blob :=
  records23166_23167 ++ records23167_23168
theorem aligned23166_23168 :
    AlignedValid 12 4 missing23166_23168 records23166_23168 :=
  aligned23166_23167.append aligned23167_23168

def missing23164_23168 : List (BitVec (edgeCount 12)) :=
  missing23164_23166 ++ missing23166_23168
abbrev records23164_23168 : List Blob :=
  records23164_23166 ++ records23166_23168
theorem aligned23164_23168 :
    AlignedValid 12 4 missing23164_23168 records23164_23168 :=
  aligned23164_23166.append aligned23166_23168

def missing23160_23168 : List (BitVec (edgeCount 12)) :=
  missing23160_23164 ++ missing23164_23168
abbrev records23160_23168 : List Blob :=
  records23160_23164 ++ records23164_23168
theorem aligned23160_23168 :
    AlignedValid 12 4 missing23160_23168 records23160_23168 :=
  aligned23160_23164.append aligned23164_23168

def missing23152_23168 : List (BitVec (edgeCount 12)) :=
  missing23152_23160 ++ missing23160_23168
abbrev records23152_23168 : List Blob :=
  records23152_23160 ++ records23160_23168
theorem aligned23152_23168 :
    AlignedValid 12 4 missing23152_23168 records23152_23168 :=
  aligned23152_23160.append aligned23160_23168

def missing23136_23168 : List (BitVec (edgeCount 12)) :=
  missing23136_23152 ++ missing23152_23168
abbrev records23136_23168 : List Blob :=
  records23136_23152 ++ records23152_23168
theorem aligned23136_23168 :
    AlignedValid 12 4 missing23136_23168 records23136_23168 :=
  aligned23136_23152.append aligned23152_23168

def missing23104_23168 : List (BitVec (edgeCount 12)) :=
  missing23104_23136 ++ missing23136_23168
abbrev records23104_23168 : List Blob :=
  records23104_23136 ++ records23136_23168
theorem aligned23104_23168 :
    AlignedValid 12 4 missing23104_23168 records23104_23168 :=
  aligned23104_23136.append aligned23136_23168

def missing23040_23168 : List (BitVec (edgeCount 12)) :=
  missing23040_23104 ++ missing23104_23168
abbrev records23040_23168 : List Blob :=
  records23040_23104 ++ records23104_23168
theorem aligned23040_23168 :
    AlignedValid 12 4 missing23040_23168 records23040_23168 :=
  aligned23040_23104.append aligned23104_23168

abbrev missing : List (BitVec (edgeCount 12)) := missing23040_23168
abbrev records : List Blob := records23040_23168
theorem aligned : AlignedValid 12 4 missing records := aligned23040_23168

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard180
