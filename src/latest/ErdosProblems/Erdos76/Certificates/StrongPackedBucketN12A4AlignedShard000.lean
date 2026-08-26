/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard000

/-! Decode-only alignment checks for n=12, a=4, records 0--127. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard000

open PackedBucketCertificate

def missing0 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 73750982682191331328
theorem maskCheck0 :
    checkMaskFor missing0 StrongPackedBucketN12A4Shard000.record0 = true := by
  decide

def missing1 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36857564903516405760
theorem maskCheck1 :
    checkMaskFor missing1 StrongPackedBucketN12A4Shard000.record1 = true := by
  decide

def missing2 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55304308977225957376
theorem maskCheck2 :
    checkMaskFor missing2 StrongPackedBucketN12A4Shard000.record2 = true := by
  decide

def missing3 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 73678995456897581056
theorem maskCheck3 :
    checkMaskFor missing3 StrongPackedBucketN12A4Shard000.record3 = true := by
  decide

def missing4 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18410961567295209472
theorem maskCheck4 :
    checkMaskFor missing4 StrongPackedBucketN12A4Shard000.record4 = true := by
  decide

def missing5 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36713590452928905216
theorem maskCheck5 :
    checkMaskFor missing5 StrongPackedBucketN12A4Shard000.record5 = true := by
  decide

def missing6 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46081077677859536896
theorem maskCheck6 :
    checkMaskFor missing6 StrongPackedBucketN12A4Shard000.record6 = true := by
  decide

def missing7 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55160334526638456832
theorem maskCheck7 :
    checkMaskFor missing7 StrongPackedBucketN12A4Shard000.record7 = true := by
  decide

def missing8 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 73535021006310080512
theorem maskCheck8 :
    checkMaskFor missing8 StrongPackedBucketN12A4Shard000.record8 = true := by
  decide

def missing9 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9187871005417144320
theorem maskCheck9 :
    checkMaskFor missing9 StrongPackedBucketN12A4Shard000.record9 = true := by
  decide

def missing10 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18123012666120208384
theorem maskCheck10 :
    checkMaskFor missing10 StrongPackedBucketN12A4Shard000.record10 = true := by
  decide

def missing11 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36425641551753904128
theorem maskCheck11 :
    checkMaskFor missing11 StrongPackedBucketN12A4Shard000.record11 = true := by
  decide

def missing12 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41469673134408859648
theorem maskCheck12 :
    checkMaskFor missing12 StrongPackedBucketN12A4Shard000.record12 = true := by
  decide

def missing13 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45793128776684535808
theorem maskCheck13 :
    checkMaskFor missing13 StrongPackedBucketN12A4Shard000.record13 = true := by
  decide

def missing14 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 54872385625463455744
theorem maskCheck14 :
    checkMaskFor missing14 StrongPackedBucketN12A4Shard000.record14 = true := by
  decide

def missing15 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 73247072105135079424
theorem maskCheck15 :
    checkMaskFor missing15 StrongPackedBucketN12A4Shard000.record15 = true := by
  decide

def missing16 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4576747936943177728
theorem maskCheck16 :
    checkMaskFor missing16 StrongPackedBucketN12A4Shard000.record16 = true := by
  decide

def missing17 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8611973203067142144
theorem maskCheck17 :
    checkMaskFor missing17 StrongPackedBucketN12A4Shard000.record17 = true := by
  decide

def missing18 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17547114863770206208
theorem maskCheck18 :
    checkMaskFor missing18 StrongPackedBucketN12A4Shard000.record18 = true := by
  decide

def missing19 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 35849743749403901952
theorem maskCheck19 :
    checkMaskFor missing19 StrongPackedBucketN12A4Shard000.record19 = true := by
  decide

def missing20 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39164393075148587008
theorem maskCheck20 :
    checkMaskFor missing20 StrongPackedBucketN12A4Shard000.record20 = true := by
  decide

def missing21 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40893775332058857472
theorem maskCheck21 :
    checkMaskFor missing21 StrongPackedBucketN12A4Shard000.record21 = true := by
  decide

def missing22 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45217230974334533632
theorem maskCheck22 :
    checkMaskFor missing22 StrongPackedBucketN12A4Shard000.record22 = true := by
  decide

def missing23 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 54296487823113453568
theorem maskCheck23 :
    checkMaskFor missing23 StrongPackedBucketN12A4Shard000.record23 = true := by
  decide

def missing24 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 72671174302785077248
theorem maskCheck24 :
    checkMaskFor missing24 StrongPackedBucketN12A4Shard000.record24 = true := by
  decide

def missing25 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2272030827636326400
theorem maskCheck25 :
    checkMaskFor missing25 StrongPackedBucketN12A4Shard000.record25 = true := by
  decide

def missing26 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3424952332243173376
theorem maskCheck26 :
    checkMaskFor missing26 StrongPackedBucketN12A4Shard000.record26 = true := by
  decide

def missing27 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 7460177598367137792
theorem maskCheck27 :
    checkMaskFor missing27 StrongPackedBucketN12A4Shard000.record27 = true := by
  decide

def missing28 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16395319259070201856
theorem maskCheck28 :
    checkMaskFor missing28 StrongPackedBucketN12A4Shard000.record28 = true := by
  decide

def missing29 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 34697948144703897600
theorem maskCheck29 :
    checkMaskFor missing29 StrongPackedBucketN12A4Shard000.record29 = true := by
  decide

def missing30 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36857529787863793664
theorem maskCheck30 :
    checkMaskFor missing30 StrongPackedBucketN12A4Shard000.record30 = true := by
  decide

def missing31 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64527645898428121088
theorem maskCheck31 :
    checkMaskFor missing31 StrongPackedBucketN12A4Shard000.record31 = true := by
  decide

def missing32 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18410820898526330880
theorem maskCheck32 :
    checkMaskFor missing32 StrongPackedBucketN12A4Shard000.record32 = true := by
  decide

def missing33 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27634192935381106688
theorem maskCheck33 :
    checkMaskFor missing33 StrongPackedBucketN12A4Shard000.record33 = true := by
  decide

def missing34 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36785507378197954560
theorem maskCheck34 :
    checkMaskFor missing34 StrongPackedBucketN12A4Shard000.record34 = true := by
  decide

def missing35 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36821536175216918528
theorem maskCheck35 :
    checkMaskFor missing35 StrongPackedBucketN12A4Shard000.record35 = true := by
  decide

def missing36 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46080937009090658304
theorem maskCheck36 :
    checkMaskFor missing36 StrongPackedBucketN12A4Shard000.record36 = true := by
  decide

def missing37 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55232251451907506176
theorem maskCheck37 :
    checkMaskFor missing37 StrongPackedBucketN12A4Shard000.record37 = true := by
  decide

def missing38 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59915995064372822016
theorem maskCheck38 :
    checkMaskFor missing38 StrongPackedBucketN12A4Shard000.record38 = true := by
  decide

def missing39 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18410926451642597376
theorem maskCheck39 :
    checkMaskFor missing39 StrongPackedBucketN12A4Shard000.record39 = true := by
  decide

def missing40 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27634298488497373184
theorem maskCheck40 :
    checkMaskFor missing40 StrongPackedBucketN12A4Shard000.record40 = true := by
  decide

def missing41 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36713555337276293120
theorem maskCheck41 :
    checkMaskFor missing41 StrongPackedBucketN12A4Shard000.record41 = true := by
  decide

def missing42 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46081042562206924800
theorem maskCheck42 :
    checkMaskFor missing42 StrongPackedBucketN12A4Shard000.record42 = true := by
  decide

def missing43 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55160299410985844736
theorem maskCheck43 :
    checkMaskFor missing43 StrongPackedBucketN12A4Shard000.record43 = true := by
  decide

def missing44 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55268385802042736640
theorem maskCheck44 :
    checkMaskFor missing44 StrongPackedBucketN12A4Shard000.record44 = true := by
  decide

def missing45 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59916100617489088512
theorem maskCheck45 :
    checkMaskFor missing45 StrongPackedBucketN12A4Shard000.record45 = true := by
  decide

def missing46 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64383671447840620544
theorem maskCheck46 :
    checkMaskFor missing46 StrongPackedBucketN12A4Shard000.record46 = true := by
  decide

def missing47 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 73534985890657468416
theorem maskCheck47 :
    checkMaskFor missing47 StrongPackedBucketN12A4Shard000.record47 = true := by
  decide

def missing48 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18428764928291635200
theorem maskCheck48 :
    checkMaskFor missing48 StrongPackedBucketN12A4Shard000.record48 = true := by
  decide

def missing49 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27652136965146411008
theorem maskCheck49 :
    checkMaskFor missing49 StrongPackedBucketN12A4Shard000.record49 = true := by
  decide

def missing50 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59933939094138126336
theorem maskCheck50 :
    checkMaskFor missing50 StrongPackedBucketN12A4Shard000.record50 = true := by
  decide

def missing51 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9187589599159910400
theorem maskCheck51 :
    checkMaskFor missing51 StrongPackedBucketN12A4Shard000.record51 = true := by
  decide

def missing52 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18266846447938830336
theorem maskCheck52 :
    checkMaskFor missing52 StrongPackedBucketN12A4Shard000.record52 = true := by
  decide

def missing53 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18374932838995722240
theorem maskCheck53 :
    checkMaskFor missing53 StrongPackedBucketN12A4Shard000.record53 = true := by
  decide

def missing54 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23022647654442074112
theorem maskCheck54 :
    checkMaskFor missing54 StrongPackedBucketN12A4Shard000.record54 = true := by
  decide

def missing55 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27490218484793606144
theorem maskCheck55 :
    checkMaskFor missing55 StrongPackedBucketN12A4Shard000.record55 = true := by
  decide

def missing56 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27598304875850498048
theorem maskCheck56 :
    checkMaskFor missing56 StrongPackedBucketN12A4Shard000.record56 = true := by
  decide

def missing57 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36641532927610454016
theorem maskCheck57 :
    checkMaskFor missing57 StrongPackedBucketN12A4Shard000.record57 = true := by
  decide

def missing58 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36677561724629417984
theorem maskCheck58 :
    checkMaskFor missing58 StrongPackedBucketN12A4Shard000.record58 = true := by
  decide

def missing59 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41469391728151625728
theorem maskCheck59 :
    checkMaskFor missing59 StrongPackedBucketN12A4Shard000.record59 = true := by
  decide

def missing60 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45936962558503157760
theorem maskCheck60 :
    checkMaskFor missing60 StrongPackedBucketN12A4Shard000.record60 = true := by
  decide

def missing61 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46045048949560049664
theorem maskCheck61 :
    checkMaskFor missing61 StrongPackedBucketN12A4Shard000.record61 = true := by
  decide

def missing62 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55088277001320005632
theorem maskCheck62 :
    checkMaskFor missing62 StrongPackedBucketN12A4Shard000.record62 = true := by
  decide

def missing63 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55124305798338969600
theorem maskCheck63 :
    checkMaskFor missing63 StrongPackedBucketN12A4Shard000.record63 = true := by
  decide

def missing64 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57610292792647483392
theorem maskCheck64 :
    checkMaskFor missing64 StrongPackedBucketN12A4Shard000.record64 = true := by
  decide

def missing65 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59772020613785321472
theorem maskCheck65 :
    checkMaskFor missing65 StrongPackedBucketN12A4Shard000.record65 = true := by
  decide

def missing66 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59880107004842213376
theorem maskCheck66 :
    checkMaskFor missing66 StrongPackedBucketN12A4Shard000.record66 = true := by
  decide

def missing67 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64311649038174781440
theorem maskCheck67 :
    checkMaskFor missing67 StrongPackedBucketN12A4Shard000.record67 = true := by
  decide

def missing68 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64347677835193745408
theorem maskCheck68 :
    checkMaskFor missing68 StrongPackedBucketN12A4Shard000.record68 = true := by
  decide

def missing69 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 73498992278010593280
theorem maskCheck69 :
    checkMaskFor missing69 StrongPackedBucketN12A4Shard000.record69 = true := by
  decide

def missing70 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9187835889764532224
theorem maskCheck70 :
    checkMaskFor missing70 StrongPackedBucketN12A4Shard000.record70 = true := by
  decide

def missing71 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18122977550467596288
theorem maskCheck71 :
    checkMaskFor missing71 StrongPackedBucketN12A4Shard000.record71 = true := by
  decide

def missing72 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18375179129600344064
theorem maskCheck72 :
    checkMaskFor missing72 StrongPackedBucketN12A4Shard000.record72 = true := by
  decide

def missing73 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23022893945046695936
theorem maskCheck73 :
    checkMaskFor missing73 StrongPackedBucketN12A4Shard000.record73 = true := by
  decide

def missing74 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27346349587322372096
theorem maskCheck74 :
    checkMaskFor missing74 StrongPackedBucketN12A4Shard000.record74 = true := by
  decide

def missing75 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36425606436101292032
theorem maskCheck75 :
    checkMaskFor missing75 StrongPackedBucketN12A4Shard000.record75 = true := by
  decide

def missing76 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41469638018756247552
theorem maskCheck76 :
    checkMaskFor missing76 StrongPackedBucketN12A4Shard000.record76 = true := by
  decide

def missing77 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45793093661031923712
theorem maskCheck77 :
    checkMaskFor missing77 StrongPackedBucketN12A4Shard000.record77 = true := by
  decide

def missing78 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46045295240164671488
theorem maskCheck78 :
    checkMaskFor missing78 StrongPackedBucketN12A4Shard000.record78 = true := by
  decide

def missing79 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 54872350509810843648
theorem maskCheck79 :
    checkMaskFor missing79 StrongPackedBucketN12A4Shard000.record79 = true := by
  decide

def missing80 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 54980436900867735552
theorem maskCheck80 :
    checkMaskFor missing80 StrongPackedBucketN12A4Shard000.record80 = true := by
  decide

def missing81 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57610539083252105216
theorem maskCheck81 :
    checkMaskFor missing81 StrongPackedBucketN12A4Shard000.record81 = true := by
  decide

def missing82 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59628151716314087424
theorem maskCheck82 :
    checkMaskFor missing82 StrongPackedBucketN12A4Shard000.record82 = true := by
  decide

def missing83 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64095722546665619456
theorem maskCheck83 :
    checkMaskFor missing83 StrongPackedBucketN12A4Shard000.record83 = true := by
  decide

def missing84 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 73247036989482467328
theorem maskCheck84 :
    checkMaskFor missing84 StrongPackedBucketN12A4Shard000.record84 = true := by
  decide

def missing85 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9205463260181037056
theorem maskCheck85 :
    checkMaskFor missing85 StrongPackedBucketN12A4Shard000.record85 = true := by
  decide

def missing86 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18356777702997884928
theorem maskCheck86 :
    checkMaskFor missing86 StrongPackedBucketN12A4Shard000.record86 = true := by
  decide

def missing87 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18392806500016848896
theorem maskCheck87 :
    checkMaskFor missing87 StrongPackedBucketN12A4Shard000.record87 = true := by
  decide

def missing88 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23040521315463200768
theorem maskCheck88 :
    checkMaskFor missing88 StrongPackedBucketN12A4Shard000.record88 = true := by
  decide

def missing89 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27580149739852660736
theorem maskCheck89 :
    checkMaskFor missing89 StrongPackedBucketN12A4Shard000.record89 = true := by
  decide

def missing90 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41487265389172752384
theorem maskCheck90 :
    checkMaskFor missing90 StrongPackedBucketN12A4Shard000.record90 = true := by
  decide

def missing91 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46026893813562212352
theorem maskCheck91 :
    checkMaskFor missing91 StrongPackedBucketN12A4Shard000.record91 = true := by
  decide

def missing92 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46062922610581176320
theorem maskCheck92 :
    checkMaskFor missing92 StrongPackedBucketN12A4Shard000.record92 = true := by
  decide

def missing93 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 55214237053398024192
theorem maskCheck93 :
    checkMaskFor missing93 StrongPackedBucketN12A4Shard000.record93 = true := by
  decide

def missing94 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57628166453668610048
theorem maskCheck94 :
    checkMaskFor missing94 StrongPackedBucketN12A4Shard000.record94 = true := by
  decide

def missing95 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59861951868844376064
theorem maskCheck95 :
    checkMaskFor missing95 StrongPackedBucketN12A4Shard000.record95 = true := by
  decide

def missing96 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4576185055709233152
theorem maskCheck96 :
    checkMaskFor missing96 StrongPackedBucketN12A4Shard000.record96 = true := by
  decide

def missing97 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8899640697984909312
theorem maskCheck97 :
    checkMaskFor missing97 StrongPackedBucketN12A4Shard000.record97 = true := by
  decide

def missing98 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9151842277117657088
theorem maskCheck98 :
    checkMaskFor missing98 StrongPackedBucketN12A4Shard000.record98 = true := by
  decide

def missing99 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17978897546763829248
theorem maskCheck99 :
    checkMaskFor missing99 StrongPackedBucketN12A4Shard000.record99 = true := by
  decide

def missing100 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18086983937820721152
theorem maskCheck100 :
    checkMaskFor missing100 StrongPackedBucketN12A4Shard000.record100 = true := by
  decide

def missing101 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20717086120205090816
theorem maskCheck101 :
    checkMaskFor missing101 StrongPackedBucketN12A4Shard000.record101 = true := by
  decide

def missing102 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22734698753267073024
theorem maskCheck102 :
    checkMaskFor missing102 StrongPackedBucketN12A4Shard000.record102 = true := by
  decide

def missing103 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 22986900332399820800
theorem maskCheck103 :
    checkMaskFor missing103 StrongPackedBucketN12A4Shard000.record103 = true := by
  decide

def missing104 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27202269583618605056
theorem maskCheck104 :
    checkMaskFor missing104 StrongPackedBucketN12A4Shard000.record104 = true := by
  decide

def missing105 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27310355974675496960
theorem maskCheck105 :
    checkMaskFor missing105 StrongPackedBucketN12A4Shard000.record105 = true := by
  decide

def missing106 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36353584026435452928
theorem maskCheck106 :
    checkMaskFor missing106 StrongPackedBucketN12A4Shard000.record106 = true := by
  decide

def missing107 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 36389612823454416896
theorem maskCheck107 :
    checkMaskFor missing107 StrongPackedBucketN12A4Shard000.record107 = true := by
  decide

def missing108 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39163830193914642432
theorem maskCheck108 :
    checkMaskFor missing108 StrongPackedBucketN12A4Shard000.record108 = true := by
  decide

def missing109 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41181442826976624640
theorem maskCheck109 :
    checkMaskFor missing109 StrongPackedBucketN12A4Shard000.record109 = true := by
  decide

def missing110 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41433644406109372416
theorem maskCheck110 :
    checkMaskFor missing110 StrongPackedBucketN12A4Shard000.record110 = true := by
  decide

def missing111 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45649013657328156672
theorem maskCheck111 :
    checkMaskFor missing111 StrongPackedBucketN12A4Shard000.record111 = true := by
  decide

def missing112 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 45757100048385048576
theorem maskCheck112 :
    checkMaskFor missing112 StrongPackedBucketN12A4Shard000.record112 = true := by
  decide

def missing113 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 54800328100145004544
theorem maskCheck113 :
    checkMaskFor missing113 StrongPackedBucketN12A4Shard000.record113 = true := by
  decide

def missing114 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 54836356897163968512
theorem maskCheck114 :
    checkMaskFor missing114 StrongPackedBucketN12A4Shard000.record114 = true := by
  decide

def missing115 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 56457652763017347072
theorem maskCheck115 :
    checkMaskFor missing115 StrongPackedBucketN12A4Shard000.record115 = true := by
  decide

def missing116 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57322343891472482304
theorem maskCheck116 :
    checkMaskFor missing116 StrongPackedBucketN12A4Shard000.record116 = true := by
  decide

def missing117 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 57574545470605230080
theorem maskCheck117 :
    checkMaskFor missing117 StrongPackedBucketN12A4Shard000.record117 = true := by
  decide

def missing118 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59484071712610320384
theorem maskCheck118 :
    checkMaskFor missing118 StrongPackedBucketN12A4Shard000.record118 = true := by
  decide

def missing119 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 59592158103667212288
theorem maskCheck119 :
    checkMaskFor missing119 StrongPackedBucketN12A4Shard000.record119 = true := by
  decide

def missing120 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64023700136999780352
theorem maskCheck120 :
    checkMaskFor missing120 StrongPackedBucketN12A4Shard000.record120 = true := by
  decide

def missing121 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64059728934018744320
theorem maskCheck121 :
    checkMaskFor missing121 StrongPackedBucketN12A4Shard000.record121 = true := by
  decide

def missing122 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 73211043376835592192
theorem maskCheck122 :
    checkMaskFor missing122 StrongPackedBucketN12A4Shard000.record122 = true := by
  decide

def missing123 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4576712821290565632
theorem maskCheck123 :
    checkMaskFor missing123 StrongPackedBucketN12A4Shard000.record123 = true := by
  decide

def missing124 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 8611938087414530048
theorem maskCheck124 :
    checkMaskFor missing124 StrongPackedBucketN12A4Shard000.record124 = true := by
  decide

def missing125 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9152370042698989568
theorem maskCheck125 :
    checkMaskFor missing125 StrongPackedBucketN12A4Shard000.record125 = true := by
  decide

def missing126 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17547079748117594112
theorem maskCheck126 :
    checkMaskFor missing126 StrongPackedBucketN12A4Shard000.record126 = true := by
  decide

def missing127 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 17799281327250341888
theorem maskCheck127 :
    checkMaskFor missing127 StrongPackedBucketN12A4Shard000.record127 = true := by
  decide

def missing0_1 : List (BitVec (edgeCount 12)) :=
  [missing0]
abbrev records0_1 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record0]
theorem aligned0_1 :
    AlignedValid 12 4 missing0_1 records0_1 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check0
    maskCheck0 AlignedValid.nil

def missing1_2 : List (BitVec (edgeCount 12)) :=
  [missing1]
abbrev records1_2 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record1]
theorem aligned1_2 :
    AlignedValid 12 4 missing1_2 records1_2 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check1
    maskCheck1 AlignedValid.nil

def missing0_2 : List (BitVec (edgeCount 12)) :=
  missing0_1 ++ missing1_2
abbrev records0_2 : List Blob :=
  records0_1 ++ records1_2
theorem aligned0_2 :
    AlignedValid 12 4 missing0_2 records0_2 :=
  aligned0_1.append aligned1_2

def missing2_3 : List (BitVec (edgeCount 12)) :=
  [missing2]
abbrev records2_3 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record2]
theorem aligned2_3 :
    AlignedValid 12 4 missing2_3 records2_3 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check2
    maskCheck2 AlignedValid.nil

def missing3_4 : List (BitVec (edgeCount 12)) :=
  [missing3]
abbrev records3_4 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record3]
theorem aligned3_4 :
    AlignedValid 12 4 missing3_4 records3_4 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check3
    maskCheck3 AlignedValid.nil

def missing2_4 : List (BitVec (edgeCount 12)) :=
  missing2_3 ++ missing3_4
abbrev records2_4 : List Blob :=
  records2_3 ++ records3_4
theorem aligned2_4 :
    AlignedValid 12 4 missing2_4 records2_4 :=
  aligned2_3.append aligned3_4

def missing0_4 : List (BitVec (edgeCount 12)) :=
  missing0_2 ++ missing2_4
abbrev records0_4 : List Blob :=
  records0_2 ++ records2_4
theorem aligned0_4 :
    AlignedValid 12 4 missing0_4 records0_4 :=
  aligned0_2.append aligned2_4

def missing4_5 : List (BitVec (edgeCount 12)) :=
  [missing4]
abbrev records4_5 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record4]
theorem aligned4_5 :
    AlignedValid 12 4 missing4_5 records4_5 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check4
    maskCheck4 AlignedValid.nil

def missing5_6 : List (BitVec (edgeCount 12)) :=
  [missing5]
abbrev records5_6 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record5]
theorem aligned5_6 :
    AlignedValid 12 4 missing5_6 records5_6 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check5
    maskCheck5 AlignedValid.nil

def missing4_6 : List (BitVec (edgeCount 12)) :=
  missing4_5 ++ missing5_6
abbrev records4_6 : List Blob :=
  records4_5 ++ records5_6
theorem aligned4_6 :
    AlignedValid 12 4 missing4_6 records4_6 :=
  aligned4_5.append aligned5_6

def missing6_7 : List (BitVec (edgeCount 12)) :=
  [missing6]
abbrev records6_7 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record6]
theorem aligned6_7 :
    AlignedValid 12 4 missing6_7 records6_7 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check6
    maskCheck6 AlignedValid.nil

def missing7_8 : List (BitVec (edgeCount 12)) :=
  [missing7]
abbrev records7_8 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record7]
theorem aligned7_8 :
    AlignedValid 12 4 missing7_8 records7_8 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check7
    maskCheck7 AlignedValid.nil

def missing6_8 : List (BitVec (edgeCount 12)) :=
  missing6_7 ++ missing7_8
abbrev records6_8 : List Blob :=
  records6_7 ++ records7_8
theorem aligned6_8 :
    AlignedValid 12 4 missing6_8 records6_8 :=
  aligned6_7.append aligned7_8

def missing4_8 : List (BitVec (edgeCount 12)) :=
  missing4_6 ++ missing6_8
abbrev records4_8 : List Blob :=
  records4_6 ++ records6_8
theorem aligned4_8 :
    AlignedValid 12 4 missing4_8 records4_8 :=
  aligned4_6.append aligned6_8

def missing0_8 : List (BitVec (edgeCount 12)) :=
  missing0_4 ++ missing4_8
abbrev records0_8 : List Blob :=
  records0_4 ++ records4_8
theorem aligned0_8 :
    AlignedValid 12 4 missing0_8 records0_8 :=
  aligned0_4.append aligned4_8

def missing8_9 : List (BitVec (edgeCount 12)) :=
  [missing8]
abbrev records8_9 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record8]
theorem aligned8_9 :
    AlignedValid 12 4 missing8_9 records8_9 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check8
    maskCheck8 AlignedValid.nil

def missing9_10 : List (BitVec (edgeCount 12)) :=
  [missing9]
abbrev records9_10 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record9]
theorem aligned9_10 :
    AlignedValid 12 4 missing9_10 records9_10 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check9
    maskCheck9 AlignedValid.nil

def missing8_10 : List (BitVec (edgeCount 12)) :=
  missing8_9 ++ missing9_10
abbrev records8_10 : List Blob :=
  records8_9 ++ records9_10
theorem aligned8_10 :
    AlignedValid 12 4 missing8_10 records8_10 :=
  aligned8_9.append aligned9_10

def missing10_11 : List (BitVec (edgeCount 12)) :=
  [missing10]
abbrev records10_11 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record10]
theorem aligned10_11 :
    AlignedValid 12 4 missing10_11 records10_11 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check10
    maskCheck10 AlignedValid.nil

def missing11_12 : List (BitVec (edgeCount 12)) :=
  [missing11]
abbrev records11_12 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record11]
theorem aligned11_12 :
    AlignedValid 12 4 missing11_12 records11_12 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check11
    maskCheck11 AlignedValid.nil

def missing10_12 : List (BitVec (edgeCount 12)) :=
  missing10_11 ++ missing11_12
abbrev records10_12 : List Blob :=
  records10_11 ++ records11_12
theorem aligned10_12 :
    AlignedValid 12 4 missing10_12 records10_12 :=
  aligned10_11.append aligned11_12

def missing8_12 : List (BitVec (edgeCount 12)) :=
  missing8_10 ++ missing10_12
abbrev records8_12 : List Blob :=
  records8_10 ++ records10_12
theorem aligned8_12 :
    AlignedValid 12 4 missing8_12 records8_12 :=
  aligned8_10.append aligned10_12

def missing12_13 : List (BitVec (edgeCount 12)) :=
  [missing12]
abbrev records12_13 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record12]
theorem aligned12_13 :
    AlignedValid 12 4 missing12_13 records12_13 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check12
    maskCheck12 AlignedValid.nil

def missing13_14 : List (BitVec (edgeCount 12)) :=
  [missing13]
abbrev records13_14 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record13]
theorem aligned13_14 :
    AlignedValid 12 4 missing13_14 records13_14 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check13
    maskCheck13 AlignedValid.nil

def missing12_14 : List (BitVec (edgeCount 12)) :=
  missing12_13 ++ missing13_14
abbrev records12_14 : List Blob :=
  records12_13 ++ records13_14
theorem aligned12_14 :
    AlignedValid 12 4 missing12_14 records12_14 :=
  aligned12_13.append aligned13_14

def missing14_15 : List (BitVec (edgeCount 12)) :=
  [missing14]
abbrev records14_15 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record14]
theorem aligned14_15 :
    AlignedValid 12 4 missing14_15 records14_15 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check14
    maskCheck14 AlignedValid.nil

def missing15_16 : List (BitVec (edgeCount 12)) :=
  [missing15]
abbrev records15_16 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record15]
theorem aligned15_16 :
    AlignedValid 12 4 missing15_16 records15_16 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check15
    maskCheck15 AlignedValid.nil

def missing14_16 : List (BitVec (edgeCount 12)) :=
  missing14_15 ++ missing15_16
abbrev records14_16 : List Blob :=
  records14_15 ++ records15_16
theorem aligned14_16 :
    AlignedValid 12 4 missing14_16 records14_16 :=
  aligned14_15.append aligned15_16

def missing12_16 : List (BitVec (edgeCount 12)) :=
  missing12_14 ++ missing14_16
abbrev records12_16 : List Blob :=
  records12_14 ++ records14_16
theorem aligned12_16 :
    AlignedValid 12 4 missing12_16 records12_16 :=
  aligned12_14.append aligned14_16

def missing8_16 : List (BitVec (edgeCount 12)) :=
  missing8_12 ++ missing12_16
abbrev records8_16 : List Blob :=
  records8_12 ++ records12_16
theorem aligned8_16 :
    AlignedValid 12 4 missing8_16 records8_16 :=
  aligned8_12.append aligned12_16

def missing0_16 : List (BitVec (edgeCount 12)) :=
  missing0_8 ++ missing8_16
abbrev records0_16 : List Blob :=
  records0_8 ++ records8_16
theorem aligned0_16 :
    AlignedValid 12 4 missing0_16 records0_16 :=
  aligned0_8.append aligned8_16

def missing16_17 : List (BitVec (edgeCount 12)) :=
  [missing16]
abbrev records16_17 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record16]
theorem aligned16_17 :
    AlignedValid 12 4 missing16_17 records16_17 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check16
    maskCheck16 AlignedValid.nil

def missing17_18 : List (BitVec (edgeCount 12)) :=
  [missing17]
abbrev records17_18 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record17]
theorem aligned17_18 :
    AlignedValid 12 4 missing17_18 records17_18 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check17
    maskCheck17 AlignedValid.nil

def missing16_18 : List (BitVec (edgeCount 12)) :=
  missing16_17 ++ missing17_18
abbrev records16_18 : List Blob :=
  records16_17 ++ records17_18
theorem aligned16_18 :
    AlignedValid 12 4 missing16_18 records16_18 :=
  aligned16_17.append aligned17_18

def missing18_19 : List (BitVec (edgeCount 12)) :=
  [missing18]
abbrev records18_19 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record18]
theorem aligned18_19 :
    AlignedValid 12 4 missing18_19 records18_19 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check18
    maskCheck18 AlignedValid.nil

def missing19_20 : List (BitVec (edgeCount 12)) :=
  [missing19]
abbrev records19_20 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record19]
theorem aligned19_20 :
    AlignedValid 12 4 missing19_20 records19_20 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check19
    maskCheck19 AlignedValid.nil

def missing18_20 : List (BitVec (edgeCount 12)) :=
  missing18_19 ++ missing19_20
abbrev records18_20 : List Blob :=
  records18_19 ++ records19_20
theorem aligned18_20 :
    AlignedValid 12 4 missing18_20 records18_20 :=
  aligned18_19.append aligned19_20

def missing16_20 : List (BitVec (edgeCount 12)) :=
  missing16_18 ++ missing18_20
abbrev records16_20 : List Blob :=
  records16_18 ++ records18_20
theorem aligned16_20 :
    AlignedValid 12 4 missing16_20 records16_20 :=
  aligned16_18.append aligned18_20

def missing20_21 : List (BitVec (edgeCount 12)) :=
  [missing20]
abbrev records20_21 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record20]
theorem aligned20_21 :
    AlignedValid 12 4 missing20_21 records20_21 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check20
    maskCheck20 AlignedValid.nil

def missing21_22 : List (BitVec (edgeCount 12)) :=
  [missing21]
abbrev records21_22 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record21]
theorem aligned21_22 :
    AlignedValid 12 4 missing21_22 records21_22 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check21
    maskCheck21 AlignedValid.nil

def missing20_22 : List (BitVec (edgeCount 12)) :=
  missing20_21 ++ missing21_22
abbrev records20_22 : List Blob :=
  records20_21 ++ records21_22
theorem aligned20_22 :
    AlignedValid 12 4 missing20_22 records20_22 :=
  aligned20_21.append aligned21_22

def missing22_23 : List (BitVec (edgeCount 12)) :=
  [missing22]
abbrev records22_23 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record22]
theorem aligned22_23 :
    AlignedValid 12 4 missing22_23 records22_23 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check22
    maskCheck22 AlignedValid.nil

def missing23_24 : List (BitVec (edgeCount 12)) :=
  [missing23]
abbrev records23_24 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record23]
theorem aligned23_24 :
    AlignedValid 12 4 missing23_24 records23_24 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check23
    maskCheck23 AlignedValid.nil

def missing22_24 : List (BitVec (edgeCount 12)) :=
  missing22_23 ++ missing23_24
abbrev records22_24 : List Blob :=
  records22_23 ++ records23_24
theorem aligned22_24 :
    AlignedValid 12 4 missing22_24 records22_24 :=
  aligned22_23.append aligned23_24

def missing20_24 : List (BitVec (edgeCount 12)) :=
  missing20_22 ++ missing22_24
abbrev records20_24 : List Blob :=
  records20_22 ++ records22_24
theorem aligned20_24 :
    AlignedValid 12 4 missing20_24 records20_24 :=
  aligned20_22.append aligned22_24

def missing16_24 : List (BitVec (edgeCount 12)) :=
  missing16_20 ++ missing20_24
abbrev records16_24 : List Blob :=
  records16_20 ++ records20_24
theorem aligned16_24 :
    AlignedValid 12 4 missing16_24 records16_24 :=
  aligned16_20.append aligned20_24

def missing24_25 : List (BitVec (edgeCount 12)) :=
  [missing24]
abbrev records24_25 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record24]
theorem aligned24_25 :
    AlignedValid 12 4 missing24_25 records24_25 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check24
    maskCheck24 AlignedValid.nil

def missing25_26 : List (BitVec (edgeCount 12)) :=
  [missing25]
abbrev records25_26 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record25]
theorem aligned25_26 :
    AlignedValid 12 4 missing25_26 records25_26 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check25
    maskCheck25 AlignedValid.nil

def missing24_26 : List (BitVec (edgeCount 12)) :=
  missing24_25 ++ missing25_26
abbrev records24_26 : List Blob :=
  records24_25 ++ records25_26
theorem aligned24_26 :
    AlignedValid 12 4 missing24_26 records24_26 :=
  aligned24_25.append aligned25_26

def missing26_27 : List (BitVec (edgeCount 12)) :=
  [missing26]
abbrev records26_27 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record26]
theorem aligned26_27 :
    AlignedValid 12 4 missing26_27 records26_27 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check26
    maskCheck26 AlignedValid.nil

def missing27_28 : List (BitVec (edgeCount 12)) :=
  [missing27]
abbrev records27_28 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record27]
theorem aligned27_28 :
    AlignedValid 12 4 missing27_28 records27_28 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check27
    maskCheck27 AlignedValid.nil

def missing26_28 : List (BitVec (edgeCount 12)) :=
  missing26_27 ++ missing27_28
abbrev records26_28 : List Blob :=
  records26_27 ++ records27_28
theorem aligned26_28 :
    AlignedValid 12 4 missing26_28 records26_28 :=
  aligned26_27.append aligned27_28

def missing24_28 : List (BitVec (edgeCount 12)) :=
  missing24_26 ++ missing26_28
abbrev records24_28 : List Blob :=
  records24_26 ++ records26_28
theorem aligned24_28 :
    AlignedValid 12 4 missing24_28 records24_28 :=
  aligned24_26.append aligned26_28

def missing28_29 : List (BitVec (edgeCount 12)) :=
  [missing28]
abbrev records28_29 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record28]
theorem aligned28_29 :
    AlignedValid 12 4 missing28_29 records28_29 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check28
    maskCheck28 AlignedValid.nil

def missing29_30 : List (BitVec (edgeCount 12)) :=
  [missing29]
abbrev records29_30 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record29]
theorem aligned29_30 :
    AlignedValid 12 4 missing29_30 records29_30 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check29
    maskCheck29 AlignedValid.nil

def missing28_30 : List (BitVec (edgeCount 12)) :=
  missing28_29 ++ missing29_30
abbrev records28_30 : List Blob :=
  records28_29 ++ records29_30
theorem aligned28_30 :
    AlignedValid 12 4 missing28_30 records28_30 :=
  aligned28_29.append aligned29_30

def missing30_31 : List (BitVec (edgeCount 12)) :=
  [missing30]
abbrev records30_31 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record30]
theorem aligned30_31 :
    AlignedValid 12 4 missing30_31 records30_31 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check30
    maskCheck30 AlignedValid.nil

def missing31_32 : List (BitVec (edgeCount 12)) :=
  [missing31]
abbrev records31_32 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record31]
theorem aligned31_32 :
    AlignedValid 12 4 missing31_32 records31_32 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check31
    maskCheck31 AlignedValid.nil

def missing30_32 : List (BitVec (edgeCount 12)) :=
  missing30_31 ++ missing31_32
abbrev records30_32 : List Blob :=
  records30_31 ++ records31_32
theorem aligned30_32 :
    AlignedValid 12 4 missing30_32 records30_32 :=
  aligned30_31.append aligned31_32

def missing28_32 : List (BitVec (edgeCount 12)) :=
  missing28_30 ++ missing30_32
abbrev records28_32 : List Blob :=
  records28_30 ++ records30_32
theorem aligned28_32 :
    AlignedValid 12 4 missing28_32 records28_32 :=
  aligned28_30.append aligned30_32

def missing24_32 : List (BitVec (edgeCount 12)) :=
  missing24_28 ++ missing28_32
abbrev records24_32 : List Blob :=
  records24_28 ++ records28_32
theorem aligned24_32 :
    AlignedValid 12 4 missing24_32 records24_32 :=
  aligned24_28.append aligned28_32

def missing16_32 : List (BitVec (edgeCount 12)) :=
  missing16_24 ++ missing24_32
abbrev records16_32 : List Blob :=
  records16_24 ++ records24_32
theorem aligned16_32 :
    AlignedValid 12 4 missing16_32 records16_32 :=
  aligned16_24.append aligned24_32

def missing0_32 : List (BitVec (edgeCount 12)) :=
  missing0_16 ++ missing16_32
abbrev records0_32 : List Blob :=
  records0_16 ++ records16_32
theorem aligned0_32 :
    AlignedValid 12 4 missing0_32 records0_32 :=
  aligned0_16.append aligned16_32

def missing32_33 : List (BitVec (edgeCount 12)) :=
  [missing32]
abbrev records32_33 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record32]
theorem aligned32_33 :
    AlignedValid 12 4 missing32_33 records32_33 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check32
    maskCheck32 AlignedValid.nil

def missing33_34 : List (BitVec (edgeCount 12)) :=
  [missing33]
abbrev records33_34 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record33]
theorem aligned33_34 :
    AlignedValid 12 4 missing33_34 records33_34 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check33
    maskCheck33 AlignedValid.nil

def missing32_34 : List (BitVec (edgeCount 12)) :=
  missing32_33 ++ missing33_34
abbrev records32_34 : List Blob :=
  records32_33 ++ records33_34
theorem aligned32_34 :
    AlignedValid 12 4 missing32_34 records32_34 :=
  aligned32_33.append aligned33_34

def missing34_35 : List (BitVec (edgeCount 12)) :=
  [missing34]
abbrev records34_35 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record34]
theorem aligned34_35 :
    AlignedValid 12 4 missing34_35 records34_35 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check34
    maskCheck34 AlignedValid.nil

def missing35_36 : List (BitVec (edgeCount 12)) :=
  [missing35]
abbrev records35_36 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record35]
theorem aligned35_36 :
    AlignedValid 12 4 missing35_36 records35_36 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check35
    maskCheck35 AlignedValid.nil

def missing34_36 : List (BitVec (edgeCount 12)) :=
  missing34_35 ++ missing35_36
abbrev records34_36 : List Blob :=
  records34_35 ++ records35_36
theorem aligned34_36 :
    AlignedValid 12 4 missing34_36 records34_36 :=
  aligned34_35.append aligned35_36

def missing32_36 : List (BitVec (edgeCount 12)) :=
  missing32_34 ++ missing34_36
abbrev records32_36 : List Blob :=
  records32_34 ++ records34_36
theorem aligned32_36 :
    AlignedValid 12 4 missing32_36 records32_36 :=
  aligned32_34.append aligned34_36

def missing36_37 : List (BitVec (edgeCount 12)) :=
  [missing36]
abbrev records36_37 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record36]
theorem aligned36_37 :
    AlignedValid 12 4 missing36_37 records36_37 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check36
    maskCheck36 AlignedValid.nil

def missing37_38 : List (BitVec (edgeCount 12)) :=
  [missing37]
abbrev records37_38 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record37]
theorem aligned37_38 :
    AlignedValid 12 4 missing37_38 records37_38 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check37
    maskCheck37 AlignedValid.nil

def missing36_38 : List (BitVec (edgeCount 12)) :=
  missing36_37 ++ missing37_38
abbrev records36_38 : List Blob :=
  records36_37 ++ records37_38
theorem aligned36_38 :
    AlignedValid 12 4 missing36_38 records36_38 :=
  aligned36_37.append aligned37_38

def missing38_39 : List (BitVec (edgeCount 12)) :=
  [missing38]
abbrev records38_39 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record38]
theorem aligned38_39 :
    AlignedValid 12 4 missing38_39 records38_39 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check38
    maskCheck38 AlignedValid.nil

def missing39_40 : List (BitVec (edgeCount 12)) :=
  [missing39]
abbrev records39_40 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record39]
theorem aligned39_40 :
    AlignedValid 12 4 missing39_40 records39_40 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check39
    maskCheck39 AlignedValid.nil

def missing38_40 : List (BitVec (edgeCount 12)) :=
  missing38_39 ++ missing39_40
abbrev records38_40 : List Blob :=
  records38_39 ++ records39_40
theorem aligned38_40 :
    AlignedValid 12 4 missing38_40 records38_40 :=
  aligned38_39.append aligned39_40

def missing36_40 : List (BitVec (edgeCount 12)) :=
  missing36_38 ++ missing38_40
abbrev records36_40 : List Blob :=
  records36_38 ++ records38_40
theorem aligned36_40 :
    AlignedValid 12 4 missing36_40 records36_40 :=
  aligned36_38.append aligned38_40

def missing32_40 : List (BitVec (edgeCount 12)) :=
  missing32_36 ++ missing36_40
abbrev records32_40 : List Blob :=
  records32_36 ++ records36_40
theorem aligned32_40 :
    AlignedValid 12 4 missing32_40 records32_40 :=
  aligned32_36.append aligned36_40

def missing40_41 : List (BitVec (edgeCount 12)) :=
  [missing40]
abbrev records40_41 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record40]
theorem aligned40_41 :
    AlignedValid 12 4 missing40_41 records40_41 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check40
    maskCheck40 AlignedValid.nil

def missing41_42 : List (BitVec (edgeCount 12)) :=
  [missing41]
abbrev records41_42 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record41]
theorem aligned41_42 :
    AlignedValid 12 4 missing41_42 records41_42 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check41
    maskCheck41 AlignedValid.nil

def missing40_42 : List (BitVec (edgeCount 12)) :=
  missing40_41 ++ missing41_42
abbrev records40_42 : List Blob :=
  records40_41 ++ records41_42
theorem aligned40_42 :
    AlignedValid 12 4 missing40_42 records40_42 :=
  aligned40_41.append aligned41_42

def missing42_43 : List (BitVec (edgeCount 12)) :=
  [missing42]
abbrev records42_43 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record42]
theorem aligned42_43 :
    AlignedValid 12 4 missing42_43 records42_43 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check42
    maskCheck42 AlignedValid.nil

def missing43_44 : List (BitVec (edgeCount 12)) :=
  [missing43]
abbrev records43_44 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record43]
theorem aligned43_44 :
    AlignedValid 12 4 missing43_44 records43_44 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check43
    maskCheck43 AlignedValid.nil

def missing42_44 : List (BitVec (edgeCount 12)) :=
  missing42_43 ++ missing43_44
abbrev records42_44 : List Blob :=
  records42_43 ++ records43_44
theorem aligned42_44 :
    AlignedValid 12 4 missing42_44 records42_44 :=
  aligned42_43.append aligned43_44

def missing40_44 : List (BitVec (edgeCount 12)) :=
  missing40_42 ++ missing42_44
abbrev records40_44 : List Blob :=
  records40_42 ++ records42_44
theorem aligned40_44 :
    AlignedValid 12 4 missing40_44 records40_44 :=
  aligned40_42.append aligned42_44

def missing44_45 : List (BitVec (edgeCount 12)) :=
  [missing44]
abbrev records44_45 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record44]
theorem aligned44_45 :
    AlignedValid 12 4 missing44_45 records44_45 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check44
    maskCheck44 AlignedValid.nil

def missing45_46 : List (BitVec (edgeCount 12)) :=
  [missing45]
abbrev records45_46 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record45]
theorem aligned45_46 :
    AlignedValid 12 4 missing45_46 records45_46 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check45
    maskCheck45 AlignedValid.nil

def missing44_46 : List (BitVec (edgeCount 12)) :=
  missing44_45 ++ missing45_46
abbrev records44_46 : List Blob :=
  records44_45 ++ records45_46
theorem aligned44_46 :
    AlignedValid 12 4 missing44_46 records44_46 :=
  aligned44_45.append aligned45_46

def missing46_47 : List (BitVec (edgeCount 12)) :=
  [missing46]
abbrev records46_47 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record46]
theorem aligned46_47 :
    AlignedValid 12 4 missing46_47 records46_47 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check46
    maskCheck46 AlignedValid.nil

def missing47_48 : List (BitVec (edgeCount 12)) :=
  [missing47]
abbrev records47_48 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record47]
theorem aligned47_48 :
    AlignedValid 12 4 missing47_48 records47_48 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check47
    maskCheck47 AlignedValid.nil

def missing46_48 : List (BitVec (edgeCount 12)) :=
  missing46_47 ++ missing47_48
abbrev records46_48 : List Blob :=
  records46_47 ++ records47_48
theorem aligned46_48 :
    AlignedValid 12 4 missing46_48 records46_48 :=
  aligned46_47.append aligned47_48

def missing44_48 : List (BitVec (edgeCount 12)) :=
  missing44_46 ++ missing46_48
abbrev records44_48 : List Blob :=
  records44_46 ++ records46_48
theorem aligned44_48 :
    AlignedValid 12 4 missing44_48 records44_48 :=
  aligned44_46.append aligned46_48

def missing40_48 : List (BitVec (edgeCount 12)) :=
  missing40_44 ++ missing44_48
abbrev records40_48 : List Blob :=
  records40_44 ++ records44_48
theorem aligned40_48 :
    AlignedValid 12 4 missing40_48 records40_48 :=
  aligned40_44.append aligned44_48

def missing32_48 : List (BitVec (edgeCount 12)) :=
  missing32_40 ++ missing40_48
abbrev records32_48 : List Blob :=
  records32_40 ++ records40_48
theorem aligned32_48 :
    AlignedValid 12 4 missing32_48 records32_48 :=
  aligned32_40.append aligned40_48

def missing48_49 : List (BitVec (edgeCount 12)) :=
  [missing48]
abbrev records48_49 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record48]
theorem aligned48_49 :
    AlignedValid 12 4 missing48_49 records48_49 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check48
    maskCheck48 AlignedValid.nil

def missing49_50 : List (BitVec (edgeCount 12)) :=
  [missing49]
abbrev records49_50 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record49]
theorem aligned49_50 :
    AlignedValid 12 4 missing49_50 records49_50 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check49
    maskCheck49 AlignedValid.nil

def missing48_50 : List (BitVec (edgeCount 12)) :=
  missing48_49 ++ missing49_50
abbrev records48_50 : List Blob :=
  records48_49 ++ records49_50
theorem aligned48_50 :
    AlignedValid 12 4 missing48_50 records48_50 :=
  aligned48_49.append aligned49_50

def missing50_51 : List (BitVec (edgeCount 12)) :=
  [missing50]
abbrev records50_51 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record50]
theorem aligned50_51 :
    AlignedValid 12 4 missing50_51 records50_51 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check50
    maskCheck50 AlignedValid.nil

def missing51_52 : List (BitVec (edgeCount 12)) :=
  [missing51]
abbrev records51_52 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record51]
theorem aligned51_52 :
    AlignedValid 12 4 missing51_52 records51_52 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check51
    maskCheck51 AlignedValid.nil

def missing50_52 : List (BitVec (edgeCount 12)) :=
  missing50_51 ++ missing51_52
abbrev records50_52 : List Blob :=
  records50_51 ++ records51_52
theorem aligned50_52 :
    AlignedValid 12 4 missing50_52 records50_52 :=
  aligned50_51.append aligned51_52

def missing48_52 : List (BitVec (edgeCount 12)) :=
  missing48_50 ++ missing50_52
abbrev records48_52 : List Blob :=
  records48_50 ++ records50_52
theorem aligned48_52 :
    AlignedValid 12 4 missing48_52 records48_52 :=
  aligned48_50.append aligned50_52

def missing52_53 : List (BitVec (edgeCount 12)) :=
  [missing52]
abbrev records52_53 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record52]
theorem aligned52_53 :
    AlignedValid 12 4 missing52_53 records52_53 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check52
    maskCheck52 AlignedValid.nil

def missing53_54 : List (BitVec (edgeCount 12)) :=
  [missing53]
abbrev records53_54 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record53]
theorem aligned53_54 :
    AlignedValid 12 4 missing53_54 records53_54 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check53
    maskCheck53 AlignedValid.nil

def missing52_54 : List (BitVec (edgeCount 12)) :=
  missing52_53 ++ missing53_54
abbrev records52_54 : List Blob :=
  records52_53 ++ records53_54
theorem aligned52_54 :
    AlignedValid 12 4 missing52_54 records52_54 :=
  aligned52_53.append aligned53_54

def missing54_55 : List (BitVec (edgeCount 12)) :=
  [missing54]
abbrev records54_55 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record54]
theorem aligned54_55 :
    AlignedValid 12 4 missing54_55 records54_55 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check54
    maskCheck54 AlignedValid.nil

def missing55_56 : List (BitVec (edgeCount 12)) :=
  [missing55]
abbrev records55_56 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record55]
theorem aligned55_56 :
    AlignedValid 12 4 missing55_56 records55_56 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check55
    maskCheck55 AlignedValid.nil

def missing54_56 : List (BitVec (edgeCount 12)) :=
  missing54_55 ++ missing55_56
abbrev records54_56 : List Blob :=
  records54_55 ++ records55_56
theorem aligned54_56 :
    AlignedValid 12 4 missing54_56 records54_56 :=
  aligned54_55.append aligned55_56

def missing52_56 : List (BitVec (edgeCount 12)) :=
  missing52_54 ++ missing54_56
abbrev records52_56 : List Blob :=
  records52_54 ++ records54_56
theorem aligned52_56 :
    AlignedValid 12 4 missing52_56 records52_56 :=
  aligned52_54.append aligned54_56

def missing48_56 : List (BitVec (edgeCount 12)) :=
  missing48_52 ++ missing52_56
abbrev records48_56 : List Blob :=
  records48_52 ++ records52_56
theorem aligned48_56 :
    AlignedValid 12 4 missing48_56 records48_56 :=
  aligned48_52.append aligned52_56

def missing56_57 : List (BitVec (edgeCount 12)) :=
  [missing56]
abbrev records56_57 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record56]
theorem aligned56_57 :
    AlignedValid 12 4 missing56_57 records56_57 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check56
    maskCheck56 AlignedValid.nil

def missing57_58 : List (BitVec (edgeCount 12)) :=
  [missing57]
abbrev records57_58 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record57]
theorem aligned57_58 :
    AlignedValid 12 4 missing57_58 records57_58 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check57
    maskCheck57 AlignedValid.nil

def missing56_58 : List (BitVec (edgeCount 12)) :=
  missing56_57 ++ missing57_58
abbrev records56_58 : List Blob :=
  records56_57 ++ records57_58
theorem aligned56_58 :
    AlignedValid 12 4 missing56_58 records56_58 :=
  aligned56_57.append aligned57_58

def missing58_59 : List (BitVec (edgeCount 12)) :=
  [missing58]
abbrev records58_59 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record58]
theorem aligned58_59 :
    AlignedValid 12 4 missing58_59 records58_59 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check58
    maskCheck58 AlignedValid.nil

def missing59_60 : List (BitVec (edgeCount 12)) :=
  [missing59]
abbrev records59_60 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record59]
theorem aligned59_60 :
    AlignedValid 12 4 missing59_60 records59_60 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check59
    maskCheck59 AlignedValid.nil

def missing58_60 : List (BitVec (edgeCount 12)) :=
  missing58_59 ++ missing59_60
abbrev records58_60 : List Blob :=
  records58_59 ++ records59_60
theorem aligned58_60 :
    AlignedValid 12 4 missing58_60 records58_60 :=
  aligned58_59.append aligned59_60

def missing56_60 : List (BitVec (edgeCount 12)) :=
  missing56_58 ++ missing58_60
abbrev records56_60 : List Blob :=
  records56_58 ++ records58_60
theorem aligned56_60 :
    AlignedValid 12 4 missing56_60 records56_60 :=
  aligned56_58.append aligned58_60

def missing60_61 : List (BitVec (edgeCount 12)) :=
  [missing60]
abbrev records60_61 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record60]
theorem aligned60_61 :
    AlignedValid 12 4 missing60_61 records60_61 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check60
    maskCheck60 AlignedValid.nil

def missing61_62 : List (BitVec (edgeCount 12)) :=
  [missing61]
abbrev records61_62 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record61]
theorem aligned61_62 :
    AlignedValid 12 4 missing61_62 records61_62 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check61
    maskCheck61 AlignedValid.nil

def missing60_62 : List (BitVec (edgeCount 12)) :=
  missing60_61 ++ missing61_62
abbrev records60_62 : List Blob :=
  records60_61 ++ records61_62
theorem aligned60_62 :
    AlignedValid 12 4 missing60_62 records60_62 :=
  aligned60_61.append aligned61_62

def missing62_63 : List (BitVec (edgeCount 12)) :=
  [missing62]
abbrev records62_63 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record62]
theorem aligned62_63 :
    AlignedValid 12 4 missing62_63 records62_63 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check62
    maskCheck62 AlignedValid.nil

def missing63_64 : List (BitVec (edgeCount 12)) :=
  [missing63]
abbrev records63_64 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record63]
theorem aligned63_64 :
    AlignedValid 12 4 missing63_64 records63_64 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check63
    maskCheck63 AlignedValid.nil

def missing62_64 : List (BitVec (edgeCount 12)) :=
  missing62_63 ++ missing63_64
abbrev records62_64 : List Blob :=
  records62_63 ++ records63_64
theorem aligned62_64 :
    AlignedValid 12 4 missing62_64 records62_64 :=
  aligned62_63.append aligned63_64

def missing60_64 : List (BitVec (edgeCount 12)) :=
  missing60_62 ++ missing62_64
abbrev records60_64 : List Blob :=
  records60_62 ++ records62_64
theorem aligned60_64 :
    AlignedValid 12 4 missing60_64 records60_64 :=
  aligned60_62.append aligned62_64

def missing56_64 : List (BitVec (edgeCount 12)) :=
  missing56_60 ++ missing60_64
abbrev records56_64 : List Blob :=
  records56_60 ++ records60_64
theorem aligned56_64 :
    AlignedValid 12 4 missing56_64 records56_64 :=
  aligned56_60.append aligned60_64

def missing48_64 : List (BitVec (edgeCount 12)) :=
  missing48_56 ++ missing56_64
abbrev records48_64 : List Blob :=
  records48_56 ++ records56_64
theorem aligned48_64 :
    AlignedValid 12 4 missing48_64 records48_64 :=
  aligned48_56.append aligned56_64

def missing32_64 : List (BitVec (edgeCount 12)) :=
  missing32_48 ++ missing48_64
abbrev records32_64 : List Blob :=
  records32_48 ++ records48_64
theorem aligned32_64 :
    AlignedValid 12 4 missing32_64 records32_64 :=
  aligned32_48.append aligned48_64

def missing0_64 : List (BitVec (edgeCount 12)) :=
  missing0_32 ++ missing32_64
abbrev records0_64 : List Blob :=
  records0_32 ++ records32_64
theorem aligned0_64 :
    AlignedValid 12 4 missing0_64 records0_64 :=
  aligned0_32.append aligned32_64

def missing64_65 : List (BitVec (edgeCount 12)) :=
  [missing64]
abbrev records64_65 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record64]
theorem aligned64_65 :
    AlignedValid 12 4 missing64_65 records64_65 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check64
    maskCheck64 AlignedValid.nil

def missing65_66 : List (BitVec (edgeCount 12)) :=
  [missing65]
abbrev records65_66 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record65]
theorem aligned65_66 :
    AlignedValid 12 4 missing65_66 records65_66 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check65
    maskCheck65 AlignedValid.nil

def missing64_66 : List (BitVec (edgeCount 12)) :=
  missing64_65 ++ missing65_66
abbrev records64_66 : List Blob :=
  records64_65 ++ records65_66
theorem aligned64_66 :
    AlignedValid 12 4 missing64_66 records64_66 :=
  aligned64_65.append aligned65_66

def missing66_67 : List (BitVec (edgeCount 12)) :=
  [missing66]
abbrev records66_67 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record66]
theorem aligned66_67 :
    AlignedValid 12 4 missing66_67 records66_67 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check66
    maskCheck66 AlignedValid.nil

def missing67_68 : List (BitVec (edgeCount 12)) :=
  [missing67]
abbrev records67_68 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record67]
theorem aligned67_68 :
    AlignedValid 12 4 missing67_68 records67_68 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check67
    maskCheck67 AlignedValid.nil

def missing66_68 : List (BitVec (edgeCount 12)) :=
  missing66_67 ++ missing67_68
abbrev records66_68 : List Blob :=
  records66_67 ++ records67_68
theorem aligned66_68 :
    AlignedValid 12 4 missing66_68 records66_68 :=
  aligned66_67.append aligned67_68

def missing64_68 : List (BitVec (edgeCount 12)) :=
  missing64_66 ++ missing66_68
abbrev records64_68 : List Blob :=
  records64_66 ++ records66_68
theorem aligned64_68 :
    AlignedValid 12 4 missing64_68 records64_68 :=
  aligned64_66.append aligned66_68

def missing68_69 : List (BitVec (edgeCount 12)) :=
  [missing68]
abbrev records68_69 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record68]
theorem aligned68_69 :
    AlignedValid 12 4 missing68_69 records68_69 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check68
    maskCheck68 AlignedValid.nil

def missing69_70 : List (BitVec (edgeCount 12)) :=
  [missing69]
abbrev records69_70 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record69]
theorem aligned69_70 :
    AlignedValid 12 4 missing69_70 records69_70 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check69
    maskCheck69 AlignedValid.nil

def missing68_70 : List (BitVec (edgeCount 12)) :=
  missing68_69 ++ missing69_70
abbrev records68_70 : List Blob :=
  records68_69 ++ records69_70
theorem aligned68_70 :
    AlignedValid 12 4 missing68_70 records68_70 :=
  aligned68_69.append aligned69_70

def missing70_71 : List (BitVec (edgeCount 12)) :=
  [missing70]
abbrev records70_71 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record70]
theorem aligned70_71 :
    AlignedValid 12 4 missing70_71 records70_71 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check70
    maskCheck70 AlignedValid.nil

def missing71_72 : List (BitVec (edgeCount 12)) :=
  [missing71]
abbrev records71_72 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record71]
theorem aligned71_72 :
    AlignedValid 12 4 missing71_72 records71_72 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check71
    maskCheck71 AlignedValid.nil

def missing70_72 : List (BitVec (edgeCount 12)) :=
  missing70_71 ++ missing71_72
abbrev records70_72 : List Blob :=
  records70_71 ++ records71_72
theorem aligned70_72 :
    AlignedValid 12 4 missing70_72 records70_72 :=
  aligned70_71.append aligned71_72

def missing68_72 : List (BitVec (edgeCount 12)) :=
  missing68_70 ++ missing70_72
abbrev records68_72 : List Blob :=
  records68_70 ++ records70_72
theorem aligned68_72 :
    AlignedValid 12 4 missing68_72 records68_72 :=
  aligned68_70.append aligned70_72

def missing64_72 : List (BitVec (edgeCount 12)) :=
  missing64_68 ++ missing68_72
abbrev records64_72 : List Blob :=
  records64_68 ++ records68_72
theorem aligned64_72 :
    AlignedValid 12 4 missing64_72 records64_72 :=
  aligned64_68.append aligned68_72

def missing72_73 : List (BitVec (edgeCount 12)) :=
  [missing72]
abbrev records72_73 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record72]
theorem aligned72_73 :
    AlignedValid 12 4 missing72_73 records72_73 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check72
    maskCheck72 AlignedValid.nil

def missing73_74 : List (BitVec (edgeCount 12)) :=
  [missing73]
abbrev records73_74 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record73]
theorem aligned73_74 :
    AlignedValid 12 4 missing73_74 records73_74 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check73
    maskCheck73 AlignedValid.nil

def missing72_74 : List (BitVec (edgeCount 12)) :=
  missing72_73 ++ missing73_74
abbrev records72_74 : List Blob :=
  records72_73 ++ records73_74
theorem aligned72_74 :
    AlignedValid 12 4 missing72_74 records72_74 :=
  aligned72_73.append aligned73_74

def missing74_75 : List (BitVec (edgeCount 12)) :=
  [missing74]
abbrev records74_75 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record74]
theorem aligned74_75 :
    AlignedValid 12 4 missing74_75 records74_75 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check74
    maskCheck74 AlignedValid.nil

def missing75_76 : List (BitVec (edgeCount 12)) :=
  [missing75]
abbrev records75_76 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record75]
theorem aligned75_76 :
    AlignedValid 12 4 missing75_76 records75_76 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check75
    maskCheck75 AlignedValid.nil

def missing74_76 : List (BitVec (edgeCount 12)) :=
  missing74_75 ++ missing75_76
abbrev records74_76 : List Blob :=
  records74_75 ++ records75_76
theorem aligned74_76 :
    AlignedValid 12 4 missing74_76 records74_76 :=
  aligned74_75.append aligned75_76

def missing72_76 : List (BitVec (edgeCount 12)) :=
  missing72_74 ++ missing74_76
abbrev records72_76 : List Blob :=
  records72_74 ++ records74_76
theorem aligned72_76 :
    AlignedValid 12 4 missing72_76 records72_76 :=
  aligned72_74.append aligned74_76

def missing76_77 : List (BitVec (edgeCount 12)) :=
  [missing76]
abbrev records76_77 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record76]
theorem aligned76_77 :
    AlignedValid 12 4 missing76_77 records76_77 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check76
    maskCheck76 AlignedValid.nil

def missing77_78 : List (BitVec (edgeCount 12)) :=
  [missing77]
abbrev records77_78 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record77]
theorem aligned77_78 :
    AlignedValid 12 4 missing77_78 records77_78 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check77
    maskCheck77 AlignedValid.nil

def missing76_78 : List (BitVec (edgeCount 12)) :=
  missing76_77 ++ missing77_78
abbrev records76_78 : List Blob :=
  records76_77 ++ records77_78
theorem aligned76_78 :
    AlignedValid 12 4 missing76_78 records76_78 :=
  aligned76_77.append aligned77_78

def missing78_79 : List (BitVec (edgeCount 12)) :=
  [missing78]
abbrev records78_79 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record78]
theorem aligned78_79 :
    AlignedValid 12 4 missing78_79 records78_79 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check78
    maskCheck78 AlignedValid.nil

def missing79_80 : List (BitVec (edgeCount 12)) :=
  [missing79]
abbrev records79_80 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record79]
theorem aligned79_80 :
    AlignedValid 12 4 missing79_80 records79_80 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check79
    maskCheck79 AlignedValid.nil

def missing78_80 : List (BitVec (edgeCount 12)) :=
  missing78_79 ++ missing79_80
abbrev records78_80 : List Blob :=
  records78_79 ++ records79_80
theorem aligned78_80 :
    AlignedValid 12 4 missing78_80 records78_80 :=
  aligned78_79.append aligned79_80

def missing76_80 : List (BitVec (edgeCount 12)) :=
  missing76_78 ++ missing78_80
abbrev records76_80 : List Blob :=
  records76_78 ++ records78_80
theorem aligned76_80 :
    AlignedValid 12 4 missing76_80 records76_80 :=
  aligned76_78.append aligned78_80

def missing72_80 : List (BitVec (edgeCount 12)) :=
  missing72_76 ++ missing76_80
abbrev records72_80 : List Blob :=
  records72_76 ++ records76_80
theorem aligned72_80 :
    AlignedValid 12 4 missing72_80 records72_80 :=
  aligned72_76.append aligned76_80

def missing64_80 : List (BitVec (edgeCount 12)) :=
  missing64_72 ++ missing72_80
abbrev records64_80 : List Blob :=
  records64_72 ++ records72_80
theorem aligned64_80 :
    AlignedValid 12 4 missing64_80 records64_80 :=
  aligned64_72.append aligned72_80

def missing80_81 : List (BitVec (edgeCount 12)) :=
  [missing80]
abbrev records80_81 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record80]
theorem aligned80_81 :
    AlignedValid 12 4 missing80_81 records80_81 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check80
    maskCheck80 AlignedValid.nil

def missing81_82 : List (BitVec (edgeCount 12)) :=
  [missing81]
abbrev records81_82 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record81]
theorem aligned81_82 :
    AlignedValid 12 4 missing81_82 records81_82 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check81
    maskCheck81 AlignedValid.nil

def missing80_82 : List (BitVec (edgeCount 12)) :=
  missing80_81 ++ missing81_82
abbrev records80_82 : List Blob :=
  records80_81 ++ records81_82
theorem aligned80_82 :
    AlignedValid 12 4 missing80_82 records80_82 :=
  aligned80_81.append aligned81_82

def missing82_83 : List (BitVec (edgeCount 12)) :=
  [missing82]
abbrev records82_83 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record82]
theorem aligned82_83 :
    AlignedValid 12 4 missing82_83 records82_83 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check82
    maskCheck82 AlignedValid.nil

def missing83_84 : List (BitVec (edgeCount 12)) :=
  [missing83]
abbrev records83_84 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record83]
theorem aligned83_84 :
    AlignedValid 12 4 missing83_84 records83_84 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check83
    maskCheck83 AlignedValid.nil

def missing82_84 : List (BitVec (edgeCount 12)) :=
  missing82_83 ++ missing83_84
abbrev records82_84 : List Blob :=
  records82_83 ++ records83_84
theorem aligned82_84 :
    AlignedValid 12 4 missing82_84 records82_84 :=
  aligned82_83.append aligned83_84

def missing80_84 : List (BitVec (edgeCount 12)) :=
  missing80_82 ++ missing82_84
abbrev records80_84 : List Blob :=
  records80_82 ++ records82_84
theorem aligned80_84 :
    AlignedValid 12 4 missing80_84 records80_84 :=
  aligned80_82.append aligned82_84

def missing84_85 : List (BitVec (edgeCount 12)) :=
  [missing84]
abbrev records84_85 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record84]
theorem aligned84_85 :
    AlignedValid 12 4 missing84_85 records84_85 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check84
    maskCheck84 AlignedValid.nil

def missing85_86 : List (BitVec (edgeCount 12)) :=
  [missing85]
abbrev records85_86 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record85]
theorem aligned85_86 :
    AlignedValid 12 4 missing85_86 records85_86 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check85
    maskCheck85 AlignedValid.nil

def missing84_86 : List (BitVec (edgeCount 12)) :=
  missing84_85 ++ missing85_86
abbrev records84_86 : List Blob :=
  records84_85 ++ records85_86
theorem aligned84_86 :
    AlignedValid 12 4 missing84_86 records84_86 :=
  aligned84_85.append aligned85_86

def missing86_87 : List (BitVec (edgeCount 12)) :=
  [missing86]
abbrev records86_87 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record86]
theorem aligned86_87 :
    AlignedValid 12 4 missing86_87 records86_87 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check86
    maskCheck86 AlignedValid.nil

def missing87_88 : List (BitVec (edgeCount 12)) :=
  [missing87]
abbrev records87_88 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record87]
theorem aligned87_88 :
    AlignedValid 12 4 missing87_88 records87_88 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check87
    maskCheck87 AlignedValid.nil

def missing86_88 : List (BitVec (edgeCount 12)) :=
  missing86_87 ++ missing87_88
abbrev records86_88 : List Blob :=
  records86_87 ++ records87_88
theorem aligned86_88 :
    AlignedValid 12 4 missing86_88 records86_88 :=
  aligned86_87.append aligned87_88

def missing84_88 : List (BitVec (edgeCount 12)) :=
  missing84_86 ++ missing86_88
abbrev records84_88 : List Blob :=
  records84_86 ++ records86_88
theorem aligned84_88 :
    AlignedValid 12 4 missing84_88 records84_88 :=
  aligned84_86.append aligned86_88

def missing80_88 : List (BitVec (edgeCount 12)) :=
  missing80_84 ++ missing84_88
abbrev records80_88 : List Blob :=
  records80_84 ++ records84_88
theorem aligned80_88 :
    AlignedValid 12 4 missing80_88 records80_88 :=
  aligned80_84.append aligned84_88

def missing88_89 : List (BitVec (edgeCount 12)) :=
  [missing88]
abbrev records88_89 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record88]
theorem aligned88_89 :
    AlignedValid 12 4 missing88_89 records88_89 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check88
    maskCheck88 AlignedValid.nil

def missing89_90 : List (BitVec (edgeCount 12)) :=
  [missing89]
abbrev records89_90 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record89]
theorem aligned89_90 :
    AlignedValid 12 4 missing89_90 records89_90 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check89
    maskCheck89 AlignedValid.nil

def missing88_90 : List (BitVec (edgeCount 12)) :=
  missing88_89 ++ missing89_90
abbrev records88_90 : List Blob :=
  records88_89 ++ records89_90
theorem aligned88_90 :
    AlignedValid 12 4 missing88_90 records88_90 :=
  aligned88_89.append aligned89_90

def missing90_91 : List (BitVec (edgeCount 12)) :=
  [missing90]
abbrev records90_91 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record90]
theorem aligned90_91 :
    AlignedValid 12 4 missing90_91 records90_91 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check90
    maskCheck90 AlignedValid.nil

def missing91_92 : List (BitVec (edgeCount 12)) :=
  [missing91]
abbrev records91_92 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record91]
theorem aligned91_92 :
    AlignedValid 12 4 missing91_92 records91_92 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check91
    maskCheck91 AlignedValid.nil

def missing90_92 : List (BitVec (edgeCount 12)) :=
  missing90_91 ++ missing91_92
abbrev records90_92 : List Blob :=
  records90_91 ++ records91_92
theorem aligned90_92 :
    AlignedValid 12 4 missing90_92 records90_92 :=
  aligned90_91.append aligned91_92

def missing88_92 : List (BitVec (edgeCount 12)) :=
  missing88_90 ++ missing90_92
abbrev records88_92 : List Blob :=
  records88_90 ++ records90_92
theorem aligned88_92 :
    AlignedValid 12 4 missing88_92 records88_92 :=
  aligned88_90.append aligned90_92

def missing92_93 : List (BitVec (edgeCount 12)) :=
  [missing92]
abbrev records92_93 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record92]
theorem aligned92_93 :
    AlignedValid 12 4 missing92_93 records92_93 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check92
    maskCheck92 AlignedValid.nil

def missing93_94 : List (BitVec (edgeCount 12)) :=
  [missing93]
abbrev records93_94 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record93]
theorem aligned93_94 :
    AlignedValid 12 4 missing93_94 records93_94 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check93
    maskCheck93 AlignedValid.nil

def missing92_94 : List (BitVec (edgeCount 12)) :=
  missing92_93 ++ missing93_94
abbrev records92_94 : List Blob :=
  records92_93 ++ records93_94
theorem aligned92_94 :
    AlignedValid 12 4 missing92_94 records92_94 :=
  aligned92_93.append aligned93_94

def missing94_95 : List (BitVec (edgeCount 12)) :=
  [missing94]
abbrev records94_95 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record94]
theorem aligned94_95 :
    AlignedValid 12 4 missing94_95 records94_95 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check94
    maskCheck94 AlignedValid.nil

def missing95_96 : List (BitVec (edgeCount 12)) :=
  [missing95]
abbrev records95_96 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record95]
theorem aligned95_96 :
    AlignedValid 12 4 missing95_96 records95_96 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check95
    maskCheck95 AlignedValid.nil

def missing94_96 : List (BitVec (edgeCount 12)) :=
  missing94_95 ++ missing95_96
abbrev records94_96 : List Blob :=
  records94_95 ++ records95_96
theorem aligned94_96 :
    AlignedValid 12 4 missing94_96 records94_96 :=
  aligned94_95.append aligned95_96

def missing92_96 : List (BitVec (edgeCount 12)) :=
  missing92_94 ++ missing94_96
abbrev records92_96 : List Blob :=
  records92_94 ++ records94_96
theorem aligned92_96 :
    AlignedValid 12 4 missing92_96 records92_96 :=
  aligned92_94.append aligned94_96

def missing88_96 : List (BitVec (edgeCount 12)) :=
  missing88_92 ++ missing92_96
abbrev records88_96 : List Blob :=
  records88_92 ++ records92_96
theorem aligned88_96 :
    AlignedValid 12 4 missing88_96 records88_96 :=
  aligned88_92.append aligned92_96

def missing80_96 : List (BitVec (edgeCount 12)) :=
  missing80_88 ++ missing88_96
abbrev records80_96 : List Blob :=
  records80_88 ++ records88_96
theorem aligned80_96 :
    AlignedValid 12 4 missing80_96 records80_96 :=
  aligned80_88.append aligned88_96

def missing64_96 : List (BitVec (edgeCount 12)) :=
  missing64_80 ++ missing80_96
abbrev records64_96 : List Blob :=
  records64_80 ++ records80_96
theorem aligned64_96 :
    AlignedValid 12 4 missing64_96 records64_96 :=
  aligned64_80.append aligned80_96

def missing96_97 : List (BitVec (edgeCount 12)) :=
  [missing96]
abbrev records96_97 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record96]
theorem aligned96_97 :
    AlignedValid 12 4 missing96_97 records96_97 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check96
    maskCheck96 AlignedValid.nil

def missing97_98 : List (BitVec (edgeCount 12)) :=
  [missing97]
abbrev records97_98 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record97]
theorem aligned97_98 :
    AlignedValid 12 4 missing97_98 records97_98 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check97
    maskCheck97 AlignedValid.nil

def missing96_98 : List (BitVec (edgeCount 12)) :=
  missing96_97 ++ missing97_98
abbrev records96_98 : List Blob :=
  records96_97 ++ records97_98
theorem aligned96_98 :
    AlignedValid 12 4 missing96_98 records96_98 :=
  aligned96_97.append aligned97_98

def missing98_99 : List (BitVec (edgeCount 12)) :=
  [missing98]
abbrev records98_99 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record98]
theorem aligned98_99 :
    AlignedValid 12 4 missing98_99 records98_99 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check98
    maskCheck98 AlignedValid.nil

def missing99_100 : List (BitVec (edgeCount 12)) :=
  [missing99]
abbrev records99_100 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record99]
theorem aligned99_100 :
    AlignedValid 12 4 missing99_100 records99_100 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check99
    maskCheck99 AlignedValid.nil

def missing98_100 : List (BitVec (edgeCount 12)) :=
  missing98_99 ++ missing99_100
abbrev records98_100 : List Blob :=
  records98_99 ++ records99_100
theorem aligned98_100 :
    AlignedValid 12 4 missing98_100 records98_100 :=
  aligned98_99.append aligned99_100

def missing96_100 : List (BitVec (edgeCount 12)) :=
  missing96_98 ++ missing98_100
abbrev records96_100 : List Blob :=
  records96_98 ++ records98_100
theorem aligned96_100 :
    AlignedValid 12 4 missing96_100 records96_100 :=
  aligned96_98.append aligned98_100

def missing100_101 : List (BitVec (edgeCount 12)) :=
  [missing100]
abbrev records100_101 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record100]
theorem aligned100_101 :
    AlignedValid 12 4 missing100_101 records100_101 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check100
    maskCheck100 AlignedValid.nil

def missing101_102 : List (BitVec (edgeCount 12)) :=
  [missing101]
abbrev records101_102 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record101]
theorem aligned101_102 :
    AlignedValid 12 4 missing101_102 records101_102 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check101
    maskCheck101 AlignedValid.nil

def missing100_102 : List (BitVec (edgeCount 12)) :=
  missing100_101 ++ missing101_102
abbrev records100_102 : List Blob :=
  records100_101 ++ records101_102
theorem aligned100_102 :
    AlignedValid 12 4 missing100_102 records100_102 :=
  aligned100_101.append aligned101_102

def missing102_103 : List (BitVec (edgeCount 12)) :=
  [missing102]
abbrev records102_103 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record102]
theorem aligned102_103 :
    AlignedValid 12 4 missing102_103 records102_103 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check102
    maskCheck102 AlignedValid.nil

def missing103_104 : List (BitVec (edgeCount 12)) :=
  [missing103]
abbrev records103_104 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record103]
theorem aligned103_104 :
    AlignedValid 12 4 missing103_104 records103_104 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check103
    maskCheck103 AlignedValid.nil

def missing102_104 : List (BitVec (edgeCount 12)) :=
  missing102_103 ++ missing103_104
abbrev records102_104 : List Blob :=
  records102_103 ++ records103_104
theorem aligned102_104 :
    AlignedValid 12 4 missing102_104 records102_104 :=
  aligned102_103.append aligned103_104

def missing100_104 : List (BitVec (edgeCount 12)) :=
  missing100_102 ++ missing102_104
abbrev records100_104 : List Blob :=
  records100_102 ++ records102_104
theorem aligned100_104 :
    AlignedValid 12 4 missing100_104 records100_104 :=
  aligned100_102.append aligned102_104

def missing96_104 : List (BitVec (edgeCount 12)) :=
  missing96_100 ++ missing100_104
abbrev records96_104 : List Blob :=
  records96_100 ++ records100_104
theorem aligned96_104 :
    AlignedValid 12 4 missing96_104 records96_104 :=
  aligned96_100.append aligned100_104

def missing104_105 : List (BitVec (edgeCount 12)) :=
  [missing104]
abbrev records104_105 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record104]
theorem aligned104_105 :
    AlignedValid 12 4 missing104_105 records104_105 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check104
    maskCheck104 AlignedValid.nil

def missing105_106 : List (BitVec (edgeCount 12)) :=
  [missing105]
abbrev records105_106 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record105]
theorem aligned105_106 :
    AlignedValid 12 4 missing105_106 records105_106 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check105
    maskCheck105 AlignedValid.nil

def missing104_106 : List (BitVec (edgeCount 12)) :=
  missing104_105 ++ missing105_106
abbrev records104_106 : List Blob :=
  records104_105 ++ records105_106
theorem aligned104_106 :
    AlignedValid 12 4 missing104_106 records104_106 :=
  aligned104_105.append aligned105_106

def missing106_107 : List (BitVec (edgeCount 12)) :=
  [missing106]
abbrev records106_107 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record106]
theorem aligned106_107 :
    AlignedValid 12 4 missing106_107 records106_107 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check106
    maskCheck106 AlignedValid.nil

def missing107_108 : List (BitVec (edgeCount 12)) :=
  [missing107]
abbrev records107_108 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record107]
theorem aligned107_108 :
    AlignedValid 12 4 missing107_108 records107_108 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check107
    maskCheck107 AlignedValid.nil

def missing106_108 : List (BitVec (edgeCount 12)) :=
  missing106_107 ++ missing107_108
abbrev records106_108 : List Blob :=
  records106_107 ++ records107_108
theorem aligned106_108 :
    AlignedValid 12 4 missing106_108 records106_108 :=
  aligned106_107.append aligned107_108

def missing104_108 : List (BitVec (edgeCount 12)) :=
  missing104_106 ++ missing106_108
abbrev records104_108 : List Blob :=
  records104_106 ++ records106_108
theorem aligned104_108 :
    AlignedValid 12 4 missing104_108 records104_108 :=
  aligned104_106.append aligned106_108

def missing108_109 : List (BitVec (edgeCount 12)) :=
  [missing108]
abbrev records108_109 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record108]
theorem aligned108_109 :
    AlignedValid 12 4 missing108_109 records108_109 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check108
    maskCheck108 AlignedValid.nil

def missing109_110 : List (BitVec (edgeCount 12)) :=
  [missing109]
abbrev records109_110 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record109]
theorem aligned109_110 :
    AlignedValid 12 4 missing109_110 records109_110 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check109
    maskCheck109 AlignedValid.nil

def missing108_110 : List (BitVec (edgeCount 12)) :=
  missing108_109 ++ missing109_110
abbrev records108_110 : List Blob :=
  records108_109 ++ records109_110
theorem aligned108_110 :
    AlignedValid 12 4 missing108_110 records108_110 :=
  aligned108_109.append aligned109_110

def missing110_111 : List (BitVec (edgeCount 12)) :=
  [missing110]
abbrev records110_111 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record110]
theorem aligned110_111 :
    AlignedValid 12 4 missing110_111 records110_111 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check110
    maskCheck110 AlignedValid.nil

def missing111_112 : List (BitVec (edgeCount 12)) :=
  [missing111]
abbrev records111_112 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record111]
theorem aligned111_112 :
    AlignedValid 12 4 missing111_112 records111_112 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check111
    maskCheck111 AlignedValid.nil

def missing110_112 : List (BitVec (edgeCount 12)) :=
  missing110_111 ++ missing111_112
abbrev records110_112 : List Blob :=
  records110_111 ++ records111_112
theorem aligned110_112 :
    AlignedValid 12 4 missing110_112 records110_112 :=
  aligned110_111.append aligned111_112

def missing108_112 : List (BitVec (edgeCount 12)) :=
  missing108_110 ++ missing110_112
abbrev records108_112 : List Blob :=
  records108_110 ++ records110_112
theorem aligned108_112 :
    AlignedValid 12 4 missing108_112 records108_112 :=
  aligned108_110.append aligned110_112

def missing104_112 : List (BitVec (edgeCount 12)) :=
  missing104_108 ++ missing108_112
abbrev records104_112 : List Blob :=
  records104_108 ++ records108_112
theorem aligned104_112 :
    AlignedValid 12 4 missing104_112 records104_112 :=
  aligned104_108.append aligned108_112

def missing96_112 : List (BitVec (edgeCount 12)) :=
  missing96_104 ++ missing104_112
abbrev records96_112 : List Blob :=
  records96_104 ++ records104_112
theorem aligned96_112 :
    AlignedValid 12 4 missing96_112 records96_112 :=
  aligned96_104.append aligned104_112

def missing112_113 : List (BitVec (edgeCount 12)) :=
  [missing112]
abbrev records112_113 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record112]
theorem aligned112_113 :
    AlignedValid 12 4 missing112_113 records112_113 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check112
    maskCheck112 AlignedValid.nil

def missing113_114 : List (BitVec (edgeCount 12)) :=
  [missing113]
abbrev records113_114 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record113]
theorem aligned113_114 :
    AlignedValid 12 4 missing113_114 records113_114 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check113
    maskCheck113 AlignedValid.nil

def missing112_114 : List (BitVec (edgeCount 12)) :=
  missing112_113 ++ missing113_114
abbrev records112_114 : List Blob :=
  records112_113 ++ records113_114
theorem aligned112_114 :
    AlignedValid 12 4 missing112_114 records112_114 :=
  aligned112_113.append aligned113_114

def missing114_115 : List (BitVec (edgeCount 12)) :=
  [missing114]
abbrev records114_115 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record114]
theorem aligned114_115 :
    AlignedValid 12 4 missing114_115 records114_115 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check114
    maskCheck114 AlignedValid.nil

def missing115_116 : List (BitVec (edgeCount 12)) :=
  [missing115]
abbrev records115_116 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record115]
theorem aligned115_116 :
    AlignedValid 12 4 missing115_116 records115_116 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check115
    maskCheck115 AlignedValid.nil

def missing114_116 : List (BitVec (edgeCount 12)) :=
  missing114_115 ++ missing115_116
abbrev records114_116 : List Blob :=
  records114_115 ++ records115_116
theorem aligned114_116 :
    AlignedValid 12 4 missing114_116 records114_116 :=
  aligned114_115.append aligned115_116

def missing112_116 : List (BitVec (edgeCount 12)) :=
  missing112_114 ++ missing114_116
abbrev records112_116 : List Blob :=
  records112_114 ++ records114_116
theorem aligned112_116 :
    AlignedValid 12 4 missing112_116 records112_116 :=
  aligned112_114.append aligned114_116

def missing116_117 : List (BitVec (edgeCount 12)) :=
  [missing116]
abbrev records116_117 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record116]
theorem aligned116_117 :
    AlignedValid 12 4 missing116_117 records116_117 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check116
    maskCheck116 AlignedValid.nil

def missing117_118 : List (BitVec (edgeCount 12)) :=
  [missing117]
abbrev records117_118 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record117]
theorem aligned117_118 :
    AlignedValid 12 4 missing117_118 records117_118 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check117
    maskCheck117 AlignedValid.nil

def missing116_118 : List (BitVec (edgeCount 12)) :=
  missing116_117 ++ missing117_118
abbrev records116_118 : List Blob :=
  records116_117 ++ records117_118
theorem aligned116_118 :
    AlignedValid 12 4 missing116_118 records116_118 :=
  aligned116_117.append aligned117_118

def missing118_119 : List (BitVec (edgeCount 12)) :=
  [missing118]
abbrev records118_119 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record118]
theorem aligned118_119 :
    AlignedValid 12 4 missing118_119 records118_119 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check118
    maskCheck118 AlignedValid.nil

def missing119_120 : List (BitVec (edgeCount 12)) :=
  [missing119]
abbrev records119_120 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record119]
theorem aligned119_120 :
    AlignedValid 12 4 missing119_120 records119_120 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check119
    maskCheck119 AlignedValid.nil

def missing118_120 : List (BitVec (edgeCount 12)) :=
  missing118_119 ++ missing119_120
abbrev records118_120 : List Blob :=
  records118_119 ++ records119_120
theorem aligned118_120 :
    AlignedValid 12 4 missing118_120 records118_120 :=
  aligned118_119.append aligned119_120

def missing116_120 : List (BitVec (edgeCount 12)) :=
  missing116_118 ++ missing118_120
abbrev records116_120 : List Blob :=
  records116_118 ++ records118_120
theorem aligned116_120 :
    AlignedValid 12 4 missing116_120 records116_120 :=
  aligned116_118.append aligned118_120

def missing112_120 : List (BitVec (edgeCount 12)) :=
  missing112_116 ++ missing116_120
abbrev records112_120 : List Blob :=
  records112_116 ++ records116_120
theorem aligned112_120 :
    AlignedValid 12 4 missing112_120 records112_120 :=
  aligned112_116.append aligned116_120

def missing120_121 : List (BitVec (edgeCount 12)) :=
  [missing120]
abbrev records120_121 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record120]
theorem aligned120_121 :
    AlignedValid 12 4 missing120_121 records120_121 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check120
    maskCheck120 AlignedValid.nil

def missing121_122 : List (BitVec (edgeCount 12)) :=
  [missing121]
abbrev records121_122 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record121]
theorem aligned121_122 :
    AlignedValid 12 4 missing121_122 records121_122 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check121
    maskCheck121 AlignedValid.nil

def missing120_122 : List (BitVec (edgeCount 12)) :=
  missing120_121 ++ missing121_122
abbrev records120_122 : List Blob :=
  records120_121 ++ records121_122
theorem aligned120_122 :
    AlignedValid 12 4 missing120_122 records120_122 :=
  aligned120_121.append aligned121_122

def missing122_123 : List (BitVec (edgeCount 12)) :=
  [missing122]
abbrev records122_123 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record122]
theorem aligned122_123 :
    AlignedValid 12 4 missing122_123 records122_123 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check122
    maskCheck122 AlignedValid.nil

def missing123_124 : List (BitVec (edgeCount 12)) :=
  [missing123]
abbrev records123_124 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record123]
theorem aligned123_124 :
    AlignedValid 12 4 missing123_124 records123_124 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check123
    maskCheck123 AlignedValid.nil

def missing122_124 : List (BitVec (edgeCount 12)) :=
  missing122_123 ++ missing123_124
abbrev records122_124 : List Blob :=
  records122_123 ++ records123_124
theorem aligned122_124 :
    AlignedValid 12 4 missing122_124 records122_124 :=
  aligned122_123.append aligned123_124

def missing120_124 : List (BitVec (edgeCount 12)) :=
  missing120_122 ++ missing122_124
abbrev records120_124 : List Blob :=
  records120_122 ++ records122_124
theorem aligned120_124 :
    AlignedValid 12 4 missing120_124 records120_124 :=
  aligned120_122.append aligned122_124

def missing124_125 : List (BitVec (edgeCount 12)) :=
  [missing124]
abbrev records124_125 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record124]
theorem aligned124_125 :
    AlignedValid 12 4 missing124_125 records124_125 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check124
    maskCheck124 AlignedValid.nil

def missing125_126 : List (BitVec (edgeCount 12)) :=
  [missing125]
abbrev records125_126 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record125]
theorem aligned125_126 :
    AlignedValid 12 4 missing125_126 records125_126 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check125
    maskCheck125 AlignedValid.nil

def missing124_126 : List (BitVec (edgeCount 12)) :=
  missing124_125 ++ missing125_126
abbrev records124_126 : List Blob :=
  records124_125 ++ records125_126
theorem aligned124_126 :
    AlignedValid 12 4 missing124_126 records124_126 :=
  aligned124_125.append aligned125_126

def missing126_127 : List (BitVec (edgeCount 12)) :=
  [missing126]
abbrev records126_127 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record126]
theorem aligned126_127 :
    AlignedValid 12 4 missing126_127 records126_127 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check126
    maskCheck126 AlignedValid.nil

def missing127_128 : List (BitVec (edgeCount 12)) :=
  [missing127]
abbrev records127_128 : List Blob :=
  [StrongPackedBucketN12A4Shard000.record127]
theorem aligned127_128 :
    AlignedValid 12 4 missing127_128 records127_128 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard000.check127
    maskCheck127 AlignedValid.nil

def missing126_128 : List (BitVec (edgeCount 12)) :=
  missing126_127 ++ missing127_128
abbrev records126_128 : List Blob :=
  records126_127 ++ records127_128
theorem aligned126_128 :
    AlignedValid 12 4 missing126_128 records126_128 :=
  aligned126_127.append aligned127_128

def missing124_128 : List (BitVec (edgeCount 12)) :=
  missing124_126 ++ missing126_128
abbrev records124_128 : List Blob :=
  records124_126 ++ records126_128
theorem aligned124_128 :
    AlignedValid 12 4 missing124_128 records124_128 :=
  aligned124_126.append aligned126_128

def missing120_128 : List (BitVec (edgeCount 12)) :=
  missing120_124 ++ missing124_128
abbrev records120_128 : List Blob :=
  records120_124 ++ records124_128
theorem aligned120_128 :
    AlignedValid 12 4 missing120_128 records120_128 :=
  aligned120_124.append aligned124_128

def missing112_128 : List (BitVec (edgeCount 12)) :=
  missing112_120 ++ missing120_128
abbrev records112_128 : List Blob :=
  records112_120 ++ records120_128
theorem aligned112_128 :
    AlignedValid 12 4 missing112_128 records112_128 :=
  aligned112_120.append aligned120_128

def missing96_128 : List (BitVec (edgeCount 12)) :=
  missing96_112 ++ missing112_128
abbrev records96_128 : List Blob :=
  records96_112 ++ records112_128
theorem aligned96_128 :
    AlignedValid 12 4 missing96_128 records96_128 :=
  aligned96_112.append aligned112_128

def missing64_128 : List (BitVec (edgeCount 12)) :=
  missing64_96 ++ missing96_128
abbrev records64_128 : List Blob :=
  records64_96 ++ records96_128
theorem aligned64_128 :
    AlignedValid 12 4 missing64_128 records64_128 :=
  aligned64_96.append aligned96_128

def missing0_128 : List (BitVec (edgeCount 12)) :=
  missing0_64 ++ missing64_128
abbrev records0_128 : List Blob :=
  records0_64 ++ records64_128
theorem aligned0_128 :
    AlignedValid 12 4 missing0_128 records0_128 :=
  aligned0_64.append aligned64_128

abbrev missing : List (BitVec (edgeCount 12)) := missing0_128
abbrev records : List Blob := records0_128
theorem aligned : AlignedValid 12 4 missing records := aligned0_128

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard000
