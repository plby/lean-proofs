/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11Pilot32

/-! Decode-only alignment checks for a=0, records 0--31. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A0AlignedShard000

open PackedBucketCertificate

def missing0 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4468415255281664
theorem maskCheck0 :
    checkMaskFor missing0 StrongPackedBucketN11Pilot32.record0 = true := by
  decide

def missing1 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2216684161073152
theorem maskCheck1 :
    checkMaskFor missing1 StrongPackedBucketN11Pilot32.record1 = true := by
  decide

def missing2 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4433299602669568
theorem maskCheck2 :
    checkMaskFor missing2 StrongPackedBucketN11Pilot32.record2 = true := by
  decide

def missing3 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19105182763712512
theorem maskCheck3 :
    checkMaskFor missing3 StrongPackedBucketN11Pilot32.record3 = true := by
  decide

def missing4 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1090921693184000
theorem maskCheck4 :
    checkMaskFor missing4 StrongPackedBucketN11Pilot32.record4 = true := by
  decide

def missing5 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2146452855848960
theorem maskCheck5 :
    checkMaskFor missing5 StrongPackedBucketN11Pilot32.record5 = true := by
  decide

def missing6 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4363068297445376
theorem maskCheck6 :
    checkMaskFor missing6 StrongPackedBucketN11Pilot32.record6 = true := by
  decide

def missing7 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18542370249244672
theorem maskCheck7 :
    checkMaskFor missing7 StrongPackedBucketN11Pilot32.record7 = true := by
  decide

def missing8 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19034951458488320
theorem maskCheck8 :
    checkMaskFor missing8 StrongPackedBucketN11Pilot32.record8 = true := by
  decide

def missing9 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 20125666993242112
theorem maskCheck9 :
    checkMaskFor missing9 StrongPackedBucketN11Pilot32.record9 = true := by
  decide

def missing10 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 528246617669632
theorem maskCheck10 :
    checkMaskFor missing10 StrongPackedBucketN11Pilot32.record10 = true := by
  decide

def missing11 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 950459082735616
theorem maskCheck11 :
    checkMaskFor missing11 StrongPackedBucketN11Pilot32.record11 = true := by
  decide

def missing12 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2005990245400576
theorem maskCheck12 :
    checkMaskFor missing12 StrongPackedBucketN11Pilot32.record12 = true := by
  decide

def missing13 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4222605686996992
theorem maskCheck13 :
    checkMaskFor missing13 StrongPackedBucketN11Pilot32.record13 = true := by
  decide

def missing14 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18261170150440960
theorem maskCheck14 :
    checkMaskFor missing14 StrongPackedBucketN11Pilot32.record14 = true := by
  decide

def missing15 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18401907638796288
theorem maskCheck15 :
    checkMaskFor missing15 StrongPackedBucketN11Pilot32.record15 = true := by
  decide

def missing16 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18894488848039936
theorem maskCheck16 :
    checkMaskFor missing16 StrongPackedBucketN11Pilot32.record16 = true := by
  decide

def missing17 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19985204382793728
theorem maskCheck17 :
    checkMaskFor missing17 StrongPackedBucketN11Pilot32.record17 = true := by
  decide

def missing18 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1090853242142720
theorem maskCheck18 :
    checkMaskFor missing18 StrongPackedBucketN11Pilot32.record18 = true := by
  decide

def missing19 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2146384404807680
theorem maskCheck19 :
    checkMaskFor missing19 StrongPackedBucketN11Pilot32.record19 = true := by
  decide

def missing20 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4362999846404096
theorem maskCheck20 :
    checkMaskFor missing20 StrongPackedBucketN11Pilot32.record20 = true := by
  decide

def missing21 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9535102543462400
theorem maskCheck21 :
    checkMaskFor missing21 StrongPackedBucketN11Pilot32.record21 = true := by
  decide

def missing22 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 10027683752706048
theorem maskCheck22 :
    checkMaskFor missing22 StrongPackedBucketN11Pilot32.record22 = true := by
  decide

def missing23 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 27268026076233728
theorem maskCheck23 :
    checkMaskFor missing23 StrongPackedBucketN11Pilot32.record23 = true := by
  decide

def missing24 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 527972008198144
theorem maskCheck24 :
    checkMaskFor missing24 StrongPackedBucketN11Pilot32.record24 = true := by
  decide

def missing25 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1020553217441792
theorem maskCheck25 :
    checkMaskFor missing25 StrongPackedBucketN11Pilot32.record25 = true := by
  decide

def missing26 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1055737589530624
theorem maskCheck26 :
    checkMaskFor missing26 StrongPackedBucketN11Pilot32.record26 = true := by
  decide

def missing27 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2111268752195584
theorem maskCheck27 :
    checkMaskFor missing27 StrongPackedBucketN11Pilot32.record27 = true := by
  decide

def missing28 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9253696286228480
theorem maskCheck28 :
    checkMaskFor missing28 StrongPackedBucketN11Pilot32.record28 = true := by
  decide

def missing29 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9464802518761472
theorem maskCheck29 :
    checkMaskFor missing29 StrongPackedBucketN11Pilot32.record29 = true := by
  decide

def missing30 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9499986890850304
theorem maskCheck30 :
    checkMaskFor missing30 StrongPackedBucketN11Pilot32.record30 = true := by
  decide

def missing31 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18260895540969472
theorem maskCheck31 :
    checkMaskFor missing31 StrongPackedBucketN11Pilot32.record31 = true := by
  decide

def missing0_1 : List (BitVec (edgeCount 11)) :=
  [missing0]
abbrev records0_1 : List Blob :=
  [StrongPackedBucketN11Pilot32.record0]
theorem aligned0_1 :
    AlignedValid 11 0 missing0_1 records0_1 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check0
    maskCheck0 AlignedValid.nil

def missing1_2 : List (BitVec (edgeCount 11)) :=
  [missing1]
abbrev records1_2 : List Blob :=
  [StrongPackedBucketN11Pilot32.record1]
theorem aligned1_2 :
    AlignedValid 11 0 missing1_2 records1_2 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check1
    maskCheck1 AlignedValid.nil

def missing0_2 : List (BitVec (edgeCount 11)) :=
  missing0_1 ++ missing1_2
abbrev records0_2 : List Blob :=
  records0_1 ++ records1_2
theorem aligned0_2 :
    AlignedValid 11 0 missing0_2 records0_2 :=
  aligned0_1.append aligned1_2

def missing2_3 : List (BitVec (edgeCount 11)) :=
  [missing2]
abbrev records2_3 : List Blob :=
  [StrongPackedBucketN11Pilot32.record2]
theorem aligned2_3 :
    AlignedValid 11 0 missing2_3 records2_3 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check2
    maskCheck2 AlignedValid.nil

def missing3_4 : List (BitVec (edgeCount 11)) :=
  [missing3]
abbrev records3_4 : List Blob :=
  [StrongPackedBucketN11Pilot32.record3]
theorem aligned3_4 :
    AlignedValid 11 0 missing3_4 records3_4 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check3
    maskCheck3 AlignedValid.nil

def missing2_4 : List (BitVec (edgeCount 11)) :=
  missing2_3 ++ missing3_4
abbrev records2_4 : List Blob :=
  records2_3 ++ records3_4
theorem aligned2_4 :
    AlignedValid 11 0 missing2_4 records2_4 :=
  aligned2_3.append aligned3_4

def missing0_4 : List (BitVec (edgeCount 11)) :=
  missing0_2 ++ missing2_4
abbrev records0_4 : List Blob :=
  records0_2 ++ records2_4
theorem aligned0_4 :
    AlignedValid 11 0 missing0_4 records0_4 :=
  aligned0_2.append aligned2_4

def missing4_5 : List (BitVec (edgeCount 11)) :=
  [missing4]
abbrev records4_5 : List Blob :=
  [StrongPackedBucketN11Pilot32.record4]
theorem aligned4_5 :
    AlignedValid 11 0 missing4_5 records4_5 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check4
    maskCheck4 AlignedValid.nil

def missing5_6 : List (BitVec (edgeCount 11)) :=
  [missing5]
abbrev records5_6 : List Blob :=
  [StrongPackedBucketN11Pilot32.record5]
theorem aligned5_6 :
    AlignedValid 11 0 missing5_6 records5_6 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check5
    maskCheck5 AlignedValid.nil

def missing4_6 : List (BitVec (edgeCount 11)) :=
  missing4_5 ++ missing5_6
abbrev records4_6 : List Blob :=
  records4_5 ++ records5_6
theorem aligned4_6 :
    AlignedValid 11 0 missing4_6 records4_6 :=
  aligned4_5.append aligned5_6

def missing6_7 : List (BitVec (edgeCount 11)) :=
  [missing6]
abbrev records6_7 : List Blob :=
  [StrongPackedBucketN11Pilot32.record6]
theorem aligned6_7 :
    AlignedValid 11 0 missing6_7 records6_7 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check6
    maskCheck6 AlignedValid.nil

def missing7_8 : List (BitVec (edgeCount 11)) :=
  [missing7]
abbrev records7_8 : List Blob :=
  [StrongPackedBucketN11Pilot32.record7]
theorem aligned7_8 :
    AlignedValid 11 0 missing7_8 records7_8 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check7
    maskCheck7 AlignedValid.nil

def missing6_8 : List (BitVec (edgeCount 11)) :=
  missing6_7 ++ missing7_8
abbrev records6_8 : List Blob :=
  records6_7 ++ records7_8
theorem aligned6_8 :
    AlignedValid 11 0 missing6_8 records6_8 :=
  aligned6_7.append aligned7_8

def missing4_8 : List (BitVec (edgeCount 11)) :=
  missing4_6 ++ missing6_8
abbrev records4_8 : List Blob :=
  records4_6 ++ records6_8
theorem aligned4_8 :
    AlignedValid 11 0 missing4_8 records4_8 :=
  aligned4_6.append aligned6_8

def missing0_8 : List (BitVec (edgeCount 11)) :=
  missing0_4 ++ missing4_8
abbrev records0_8 : List Blob :=
  records0_4 ++ records4_8
theorem aligned0_8 :
    AlignedValid 11 0 missing0_8 records0_8 :=
  aligned0_4.append aligned4_8

def missing8_9 : List (BitVec (edgeCount 11)) :=
  [missing8]
abbrev records8_9 : List Blob :=
  [StrongPackedBucketN11Pilot32.record8]
theorem aligned8_9 :
    AlignedValid 11 0 missing8_9 records8_9 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check8
    maskCheck8 AlignedValid.nil

def missing9_10 : List (BitVec (edgeCount 11)) :=
  [missing9]
abbrev records9_10 : List Blob :=
  [StrongPackedBucketN11Pilot32.record9]
theorem aligned9_10 :
    AlignedValid 11 0 missing9_10 records9_10 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check9
    maskCheck9 AlignedValid.nil

def missing8_10 : List (BitVec (edgeCount 11)) :=
  missing8_9 ++ missing9_10
abbrev records8_10 : List Blob :=
  records8_9 ++ records9_10
theorem aligned8_10 :
    AlignedValid 11 0 missing8_10 records8_10 :=
  aligned8_9.append aligned9_10

def missing10_11 : List (BitVec (edgeCount 11)) :=
  [missing10]
abbrev records10_11 : List Blob :=
  [StrongPackedBucketN11Pilot32.record10]
theorem aligned10_11 :
    AlignedValid 11 0 missing10_11 records10_11 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check10
    maskCheck10 AlignedValid.nil

def missing11_12 : List (BitVec (edgeCount 11)) :=
  [missing11]
abbrev records11_12 : List Blob :=
  [StrongPackedBucketN11Pilot32.record11]
theorem aligned11_12 :
    AlignedValid 11 0 missing11_12 records11_12 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check11
    maskCheck11 AlignedValid.nil

def missing10_12 : List (BitVec (edgeCount 11)) :=
  missing10_11 ++ missing11_12
abbrev records10_12 : List Blob :=
  records10_11 ++ records11_12
theorem aligned10_12 :
    AlignedValid 11 0 missing10_12 records10_12 :=
  aligned10_11.append aligned11_12

def missing8_12 : List (BitVec (edgeCount 11)) :=
  missing8_10 ++ missing10_12
abbrev records8_12 : List Blob :=
  records8_10 ++ records10_12
theorem aligned8_12 :
    AlignedValid 11 0 missing8_12 records8_12 :=
  aligned8_10.append aligned10_12

def missing12_13 : List (BitVec (edgeCount 11)) :=
  [missing12]
abbrev records12_13 : List Blob :=
  [StrongPackedBucketN11Pilot32.record12]
theorem aligned12_13 :
    AlignedValid 11 0 missing12_13 records12_13 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check12
    maskCheck12 AlignedValid.nil

def missing13_14 : List (BitVec (edgeCount 11)) :=
  [missing13]
abbrev records13_14 : List Blob :=
  [StrongPackedBucketN11Pilot32.record13]
theorem aligned13_14 :
    AlignedValid 11 0 missing13_14 records13_14 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check13
    maskCheck13 AlignedValid.nil

def missing12_14 : List (BitVec (edgeCount 11)) :=
  missing12_13 ++ missing13_14
abbrev records12_14 : List Blob :=
  records12_13 ++ records13_14
theorem aligned12_14 :
    AlignedValid 11 0 missing12_14 records12_14 :=
  aligned12_13.append aligned13_14

def missing14_15 : List (BitVec (edgeCount 11)) :=
  [missing14]
abbrev records14_15 : List Blob :=
  [StrongPackedBucketN11Pilot32.record14]
theorem aligned14_15 :
    AlignedValid 11 0 missing14_15 records14_15 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check14
    maskCheck14 AlignedValid.nil

def missing15_16 : List (BitVec (edgeCount 11)) :=
  [missing15]
abbrev records15_16 : List Blob :=
  [StrongPackedBucketN11Pilot32.record15]
theorem aligned15_16 :
    AlignedValid 11 0 missing15_16 records15_16 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check15
    maskCheck15 AlignedValid.nil

def missing14_16 : List (BitVec (edgeCount 11)) :=
  missing14_15 ++ missing15_16
abbrev records14_16 : List Blob :=
  records14_15 ++ records15_16
theorem aligned14_16 :
    AlignedValid 11 0 missing14_16 records14_16 :=
  aligned14_15.append aligned15_16

def missing12_16 : List (BitVec (edgeCount 11)) :=
  missing12_14 ++ missing14_16
abbrev records12_16 : List Blob :=
  records12_14 ++ records14_16
theorem aligned12_16 :
    AlignedValid 11 0 missing12_16 records12_16 :=
  aligned12_14.append aligned14_16

def missing8_16 : List (BitVec (edgeCount 11)) :=
  missing8_12 ++ missing12_16
abbrev records8_16 : List Blob :=
  records8_12 ++ records12_16
theorem aligned8_16 :
    AlignedValid 11 0 missing8_16 records8_16 :=
  aligned8_12.append aligned12_16

def missing0_16 : List (BitVec (edgeCount 11)) :=
  missing0_8 ++ missing8_16
abbrev records0_16 : List Blob :=
  records0_8 ++ records8_16
theorem aligned0_16 :
    AlignedValid 11 0 missing0_16 records0_16 :=
  aligned0_8.append aligned8_16

def missing16_17 : List (BitVec (edgeCount 11)) :=
  [missing16]
abbrev records16_17 : List Blob :=
  [StrongPackedBucketN11Pilot32.record16]
theorem aligned16_17 :
    AlignedValid 11 0 missing16_17 records16_17 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check16
    maskCheck16 AlignedValid.nil

def missing17_18 : List (BitVec (edgeCount 11)) :=
  [missing17]
abbrev records17_18 : List Blob :=
  [StrongPackedBucketN11Pilot32.record17]
theorem aligned17_18 :
    AlignedValid 11 0 missing17_18 records17_18 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check17
    maskCheck17 AlignedValid.nil

def missing16_18 : List (BitVec (edgeCount 11)) :=
  missing16_17 ++ missing17_18
abbrev records16_18 : List Blob :=
  records16_17 ++ records17_18
theorem aligned16_18 :
    AlignedValid 11 0 missing16_18 records16_18 :=
  aligned16_17.append aligned17_18

def missing18_19 : List (BitVec (edgeCount 11)) :=
  [missing18]
abbrev records18_19 : List Blob :=
  [StrongPackedBucketN11Pilot32.record18]
theorem aligned18_19 :
    AlignedValid 11 0 missing18_19 records18_19 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check18
    maskCheck18 AlignedValid.nil

def missing19_20 : List (BitVec (edgeCount 11)) :=
  [missing19]
abbrev records19_20 : List Blob :=
  [StrongPackedBucketN11Pilot32.record19]
theorem aligned19_20 :
    AlignedValid 11 0 missing19_20 records19_20 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check19
    maskCheck19 AlignedValid.nil

def missing18_20 : List (BitVec (edgeCount 11)) :=
  missing18_19 ++ missing19_20
abbrev records18_20 : List Blob :=
  records18_19 ++ records19_20
theorem aligned18_20 :
    AlignedValid 11 0 missing18_20 records18_20 :=
  aligned18_19.append aligned19_20

def missing16_20 : List (BitVec (edgeCount 11)) :=
  missing16_18 ++ missing18_20
abbrev records16_20 : List Blob :=
  records16_18 ++ records18_20
theorem aligned16_20 :
    AlignedValid 11 0 missing16_20 records16_20 :=
  aligned16_18.append aligned18_20

def missing20_21 : List (BitVec (edgeCount 11)) :=
  [missing20]
abbrev records20_21 : List Blob :=
  [StrongPackedBucketN11Pilot32.record20]
theorem aligned20_21 :
    AlignedValid 11 0 missing20_21 records20_21 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check20
    maskCheck20 AlignedValid.nil

def missing21_22 : List (BitVec (edgeCount 11)) :=
  [missing21]
abbrev records21_22 : List Blob :=
  [StrongPackedBucketN11Pilot32.record21]
theorem aligned21_22 :
    AlignedValid 11 0 missing21_22 records21_22 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check21
    maskCheck21 AlignedValid.nil

def missing20_22 : List (BitVec (edgeCount 11)) :=
  missing20_21 ++ missing21_22
abbrev records20_22 : List Blob :=
  records20_21 ++ records21_22
theorem aligned20_22 :
    AlignedValid 11 0 missing20_22 records20_22 :=
  aligned20_21.append aligned21_22

def missing22_23 : List (BitVec (edgeCount 11)) :=
  [missing22]
abbrev records22_23 : List Blob :=
  [StrongPackedBucketN11Pilot32.record22]
theorem aligned22_23 :
    AlignedValid 11 0 missing22_23 records22_23 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check22
    maskCheck22 AlignedValid.nil

def missing23_24 : List (BitVec (edgeCount 11)) :=
  [missing23]
abbrev records23_24 : List Blob :=
  [StrongPackedBucketN11Pilot32.record23]
theorem aligned23_24 :
    AlignedValid 11 0 missing23_24 records23_24 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check23
    maskCheck23 AlignedValid.nil

def missing22_24 : List (BitVec (edgeCount 11)) :=
  missing22_23 ++ missing23_24
abbrev records22_24 : List Blob :=
  records22_23 ++ records23_24
theorem aligned22_24 :
    AlignedValid 11 0 missing22_24 records22_24 :=
  aligned22_23.append aligned23_24

def missing20_24 : List (BitVec (edgeCount 11)) :=
  missing20_22 ++ missing22_24
abbrev records20_24 : List Blob :=
  records20_22 ++ records22_24
theorem aligned20_24 :
    AlignedValid 11 0 missing20_24 records20_24 :=
  aligned20_22.append aligned22_24

def missing16_24 : List (BitVec (edgeCount 11)) :=
  missing16_20 ++ missing20_24
abbrev records16_24 : List Blob :=
  records16_20 ++ records20_24
theorem aligned16_24 :
    AlignedValid 11 0 missing16_24 records16_24 :=
  aligned16_20.append aligned20_24

def missing24_25 : List (BitVec (edgeCount 11)) :=
  [missing24]
abbrev records24_25 : List Blob :=
  [StrongPackedBucketN11Pilot32.record24]
theorem aligned24_25 :
    AlignedValid 11 0 missing24_25 records24_25 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check24
    maskCheck24 AlignedValid.nil

def missing25_26 : List (BitVec (edgeCount 11)) :=
  [missing25]
abbrev records25_26 : List Blob :=
  [StrongPackedBucketN11Pilot32.record25]
theorem aligned25_26 :
    AlignedValid 11 0 missing25_26 records25_26 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check25
    maskCheck25 AlignedValid.nil

def missing24_26 : List (BitVec (edgeCount 11)) :=
  missing24_25 ++ missing25_26
abbrev records24_26 : List Blob :=
  records24_25 ++ records25_26
theorem aligned24_26 :
    AlignedValid 11 0 missing24_26 records24_26 :=
  aligned24_25.append aligned25_26

def missing26_27 : List (BitVec (edgeCount 11)) :=
  [missing26]
abbrev records26_27 : List Blob :=
  [StrongPackedBucketN11Pilot32.record26]
theorem aligned26_27 :
    AlignedValid 11 0 missing26_27 records26_27 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check26
    maskCheck26 AlignedValid.nil

def missing27_28 : List (BitVec (edgeCount 11)) :=
  [missing27]
abbrev records27_28 : List Blob :=
  [StrongPackedBucketN11Pilot32.record27]
theorem aligned27_28 :
    AlignedValid 11 0 missing27_28 records27_28 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check27
    maskCheck27 AlignedValid.nil

def missing26_28 : List (BitVec (edgeCount 11)) :=
  missing26_27 ++ missing27_28
abbrev records26_28 : List Blob :=
  records26_27 ++ records27_28
theorem aligned26_28 :
    AlignedValid 11 0 missing26_28 records26_28 :=
  aligned26_27.append aligned27_28

def missing24_28 : List (BitVec (edgeCount 11)) :=
  missing24_26 ++ missing26_28
abbrev records24_28 : List Blob :=
  records24_26 ++ records26_28
theorem aligned24_28 :
    AlignedValid 11 0 missing24_28 records24_28 :=
  aligned24_26.append aligned26_28

def missing28_29 : List (BitVec (edgeCount 11)) :=
  [missing28]
abbrev records28_29 : List Blob :=
  [StrongPackedBucketN11Pilot32.record28]
theorem aligned28_29 :
    AlignedValid 11 0 missing28_29 records28_29 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check28
    maskCheck28 AlignedValid.nil

def missing29_30 : List (BitVec (edgeCount 11)) :=
  [missing29]
abbrev records29_30 : List Blob :=
  [StrongPackedBucketN11Pilot32.record29]
theorem aligned29_30 :
    AlignedValid 11 0 missing29_30 records29_30 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check29
    maskCheck29 AlignedValid.nil

def missing28_30 : List (BitVec (edgeCount 11)) :=
  missing28_29 ++ missing29_30
abbrev records28_30 : List Blob :=
  records28_29 ++ records29_30
theorem aligned28_30 :
    AlignedValid 11 0 missing28_30 records28_30 :=
  aligned28_29.append aligned29_30

def missing30_31 : List (BitVec (edgeCount 11)) :=
  [missing30]
abbrev records30_31 : List Blob :=
  [StrongPackedBucketN11Pilot32.record30]
theorem aligned30_31 :
    AlignedValid 11 0 missing30_31 records30_31 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check30
    maskCheck30 AlignedValid.nil

def missing31_32 : List (BitVec (edgeCount 11)) :=
  [missing31]
abbrev records31_32 : List Blob :=
  [StrongPackedBucketN11Pilot32.record31]
theorem aligned31_32 :
    AlignedValid 11 0 missing31_32 records31_32 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot32.check31
    maskCheck31 AlignedValid.nil

def missing30_32 : List (BitVec (edgeCount 11)) :=
  missing30_31 ++ missing31_32
abbrev records30_32 : List Blob :=
  records30_31 ++ records31_32
theorem aligned30_32 :
    AlignedValid 11 0 missing30_32 records30_32 :=
  aligned30_31.append aligned31_32

def missing28_32 : List (BitVec (edgeCount 11)) :=
  missing28_30 ++ missing30_32
abbrev records28_32 : List Blob :=
  records28_30 ++ records30_32
theorem aligned28_32 :
    AlignedValid 11 0 missing28_32 records28_32 :=
  aligned28_30.append aligned30_32

def missing24_32 : List (BitVec (edgeCount 11)) :=
  missing24_28 ++ missing28_32
abbrev records24_32 : List Blob :=
  records24_28 ++ records28_32
theorem aligned24_32 :
    AlignedValid 11 0 missing24_32 records24_32 :=
  aligned24_28.append aligned28_32

def missing16_32 : List (BitVec (edgeCount 11)) :=
  missing16_24 ++ missing24_32
abbrev records16_32 : List Blob :=
  records16_24 ++ records24_32
theorem aligned16_32 :
    AlignedValid 11 0 missing16_32 records16_32 :=
  aligned16_24.append aligned24_32

def missing0_32 : List (BitVec (edgeCount 11)) :=
  missing0_16 ++ missing16_32
abbrev records0_32 : List Blob :=
  records0_16 ++ records16_32
theorem aligned0_32 :
    AlignedValid 11 0 missing0_32 records0_32 :=
  aligned0_16.append aligned16_32

abbrev missing : List (BitVec (edgeCount 11)) :=
  missing0_32
abbrev records : List Blob := records0_32
theorem aligned : AlignedValid 11 0 missing records :=
  aligned0_32

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A0AlignedShard000

