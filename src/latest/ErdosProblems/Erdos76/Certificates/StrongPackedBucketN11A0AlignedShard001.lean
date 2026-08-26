/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11Pilot172Shard1

/-! Decode-only alignment checks for a=0, records 32--63. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A0AlignedShard001

open PackedBucketCertificate

def missing32 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18472001773502464
theorem maskCheck32 :
    checkMaskFor missing32 StrongPackedBucketN11Pilot172Shard1.record32 = true := by
  decide

def missing33 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 27127357307355136
theorem maskCheck33 :
    checkMaskFor missing33 StrongPackedBucketN11Pilot172Shard1.record33 = true := by
  decide

def missing34 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 528178166628352
theorem maskCheck34 :
    checkMaskFor missing34 StrongPackedBucketN11Pilot172Shard1.record34 = true := by
  decide

def missing35 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 950390631694336
theorem maskCheck35 :
    checkMaskFor missing35 StrongPackedBucketN11Pilot172Shard1.record35 = true := by
  decide

def missing36 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1055943747960832
theorem maskCheck36 :
    checkMaskFor missing36 StrongPackedBucketN11Pilot172Shard1.record36 = true := by
  decide

def missing37 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2005921794359296
theorem maskCheck37 :
    checkMaskFor missing37 StrongPackedBucketN11Pilot172Shard1.record37 = true := by
  decide

def missing38 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2041106166448128
theorem maskCheck38 :
    checkMaskFor missing38 StrongPackedBucketN11Pilot172Shard1.record38 = true := by
  decide

def missing39 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4222537235955712
theorem maskCheck39 :
    checkMaskFor missing39 StrongPackedBucketN11Pilot172Shard1.record39 = true := by
  decide

def missing40 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9253902444658688
theorem maskCheck40 :
    checkMaskFor missing40 StrongPackedBucketN11Pilot172Shard1.record40 = true := by
  decide

def missing41 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9394639933014016
theorem maskCheck41 :
    checkMaskFor missing41 StrongPackedBucketN11Pilot172Shard1.record41 = true := by
  decide

def missing42 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9887221142257664
theorem maskCheck42 :
    checkMaskFor missing42 StrongPackedBucketN11Pilot172Shard1.record42 = true := by
  decide

def missing43 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18261101699399680
theorem maskCheck43 :
    checkMaskFor missing43 StrongPackedBucketN11Pilot172Shard1.record43 = true := by
  decide

def missing44 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18401839187755008
theorem maskCheck44 :
    checkMaskFor missing44 StrongPackedBucketN11Pilot172Shard1.record44 = true := by
  decide

def missing45 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18507392304021504
theorem maskCheck45 :
    checkMaskFor missing45 StrongPackedBucketN11Pilot172Shard1.record45 = true := by
  decide

def missing46 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18894420396998656
theorem maskCheck46 :
    checkMaskFor missing46 StrongPackedBucketN11Pilot172Shard1.record46 = true := by
  decide

def missing47 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 18929604769087488
theorem maskCheck47 :
    checkMaskFor missing47 StrongPackedBucketN11Pilot172Shard1.record47 = true := by
  decide

def missing48 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 19985135931752448
theorem maskCheck48 :
    checkMaskFor missing48 StrongPackedBucketN11Pilot172Shard1.record48 = true := by
  decide

def missing49 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 27127563465785344
theorem maskCheck49 :
    checkMaskFor missing49 StrongPackedBucketN11Pilot172Shard1.record49 = true := by
  decide

def missing50 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 27338669698318336
theorem maskCheck50 :
    checkMaskFor missing50 StrongPackedBucketN11Pilot172Shard1.record50 = true := by
  decide

def missing51 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 545426755289088
theorem maskCheck51 :
    checkMaskFor missing51 StrongPackedBucketN11Pilot172Shard1.record51 = true := by
  decide

def missing52 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1073192336621568
theorem maskCheck52 :
    checkMaskFor missing52 StrongPackedBucketN11Pilot172Shard1.record52 = true := by
  decide

def missing53 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9271151033319424
theorem maskCheck53 :
    checkMaskFor missing53 StrongPackedBucketN11Pilot172Shard1.record53 = true := by
  decide

def missing54 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 27144812054446080
theorem maskCheck54 :
    checkMaskFor missing54 StrongPackedBucketN11Pilot172Shard1.record54 = true := by
  decide

def missing55 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9218786792046592
theorem maskCheck55 :
    checkMaskFor missing55 StrongPackedBucketN11Pilot172Shard1.record55 = true := by
  decide

def missing56 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9359524280401920
theorem maskCheck56 :
    checkMaskFor missing56 StrongPackedBucketN11Pilot172Shard1.record56 = true := by
  decide

def missing57 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 9852105489645568
theorem maskCheck57 :
    checkMaskFor missing57 StrongPackedBucketN11Pilot172Shard1.record57 = true := by
  decide

def missing58 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 247252945731584
theorem maskCheck58 :
    checkMaskFor missing58 StrongPackedBucketN11Pilot172Shard1.record58 = true := by
  decide

def missing59 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 493543550353408
theorem maskCheck59 :
    checkMaskFor missing59 StrongPackedBucketN11Pilot172Shard1.record59 = true := by
  decide

def missing60 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 669465410797568
theorem maskCheck60 :
    checkMaskFor missing60 StrongPackedBucketN11Pilot172Shard1.record60 = true := by
  decide

def missing61 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 775018527064064
theorem maskCheck61 :
    checkMaskFor missing61 StrongPackedBucketN11Pilot172Shard1.record61 = true := by
  decide

def missing62 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1724996573462528
theorem maskCheck62 :
    checkMaskFor missing62 StrongPackedBucketN11Pilot172Shard1.record62 = true := by
  decide

def missing63 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1760180945551360
theorem maskCheck63 :
    checkMaskFor missing63 StrongPackedBucketN11Pilot172Shard1.record63 = true := by
  decide

def missing32_33 : List (BitVec (edgeCount 11)) :=
  [missing32]
abbrev records32_33 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record32]
theorem aligned32_33 :
    AlignedValid 11 0 missing32_33 records32_33 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check32
    maskCheck32 AlignedValid.nil

def missing33_34 : List (BitVec (edgeCount 11)) :=
  [missing33]
abbrev records33_34 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record33]
theorem aligned33_34 :
    AlignedValid 11 0 missing33_34 records33_34 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check33
    maskCheck33 AlignedValid.nil

def missing32_34 : List (BitVec (edgeCount 11)) :=
  missing32_33 ++ missing33_34
abbrev records32_34 : List Blob :=
  records32_33 ++ records33_34
theorem aligned32_34 :
    AlignedValid 11 0 missing32_34 records32_34 :=
  aligned32_33.append aligned33_34

def missing34_35 : List (BitVec (edgeCount 11)) :=
  [missing34]
abbrev records34_35 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record34]
theorem aligned34_35 :
    AlignedValid 11 0 missing34_35 records34_35 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check34
    maskCheck34 AlignedValid.nil

def missing35_36 : List (BitVec (edgeCount 11)) :=
  [missing35]
abbrev records35_36 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record35]
theorem aligned35_36 :
    AlignedValid 11 0 missing35_36 records35_36 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check35
    maskCheck35 AlignedValid.nil

def missing34_36 : List (BitVec (edgeCount 11)) :=
  missing34_35 ++ missing35_36
abbrev records34_36 : List Blob :=
  records34_35 ++ records35_36
theorem aligned34_36 :
    AlignedValid 11 0 missing34_36 records34_36 :=
  aligned34_35.append aligned35_36

def missing32_36 : List (BitVec (edgeCount 11)) :=
  missing32_34 ++ missing34_36
abbrev records32_36 : List Blob :=
  records32_34 ++ records34_36
theorem aligned32_36 :
    AlignedValid 11 0 missing32_36 records32_36 :=
  aligned32_34.append aligned34_36

def missing36_37 : List (BitVec (edgeCount 11)) :=
  [missing36]
abbrev records36_37 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record36]
theorem aligned36_37 :
    AlignedValid 11 0 missing36_37 records36_37 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check36
    maskCheck36 AlignedValid.nil

def missing37_38 : List (BitVec (edgeCount 11)) :=
  [missing37]
abbrev records37_38 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record37]
theorem aligned37_38 :
    AlignedValid 11 0 missing37_38 records37_38 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check37
    maskCheck37 AlignedValid.nil

def missing36_38 : List (BitVec (edgeCount 11)) :=
  missing36_37 ++ missing37_38
abbrev records36_38 : List Blob :=
  records36_37 ++ records37_38
theorem aligned36_38 :
    AlignedValid 11 0 missing36_38 records36_38 :=
  aligned36_37.append aligned37_38

def missing38_39 : List (BitVec (edgeCount 11)) :=
  [missing38]
abbrev records38_39 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record38]
theorem aligned38_39 :
    AlignedValid 11 0 missing38_39 records38_39 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check38
    maskCheck38 AlignedValid.nil

def missing39_40 : List (BitVec (edgeCount 11)) :=
  [missing39]
abbrev records39_40 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record39]
theorem aligned39_40 :
    AlignedValid 11 0 missing39_40 records39_40 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check39
    maskCheck39 AlignedValid.nil

def missing38_40 : List (BitVec (edgeCount 11)) :=
  missing38_39 ++ missing39_40
abbrev records38_40 : List Blob :=
  records38_39 ++ records39_40
theorem aligned38_40 :
    AlignedValid 11 0 missing38_40 records38_40 :=
  aligned38_39.append aligned39_40

def missing36_40 : List (BitVec (edgeCount 11)) :=
  missing36_38 ++ missing38_40
abbrev records36_40 : List Blob :=
  records36_38 ++ records38_40
theorem aligned36_40 :
    AlignedValid 11 0 missing36_40 records36_40 :=
  aligned36_38.append aligned38_40

def missing32_40 : List (BitVec (edgeCount 11)) :=
  missing32_36 ++ missing36_40
abbrev records32_40 : List Blob :=
  records32_36 ++ records36_40
theorem aligned32_40 :
    AlignedValid 11 0 missing32_40 records32_40 :=
  aligned32_36.append aligned36_40

def missing40_41 : List (BitVec (edgeCount 11)) :=
  [missing40]
abbrev records40_41 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record40]
theorem aligned40_41 :
    AlignedValid 11 0 missing40_41 records40_41 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check40
    maskCheck40 AlignedValid.nil

def missing41_42 : List (BitVec (edgeCount 11)) :=
  [missing41]
abbrev records41_42 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record41]
theorem aligned41_42 :
    AlignedValid 11 0 missing41_42 records41_42 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check41
    maskCheck41 AlignedValid.nil

def missing40_42 : List (BitVec (edgeCount 11)) :=
  missing40_41 ++ missing41_42
abbrev records40_42 : List Blob :=
  records40_41 ++ records41_42
theorem aligned40_42 :
    AlignedValid 11 0 missing40_42 records40_42 :=
  aligned40_41.append aligned41_42

def missing42_43 : List (BitVec (edgeCount 11)) :=
  [missing42]
abbrev records42_43 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record42]
theorem aligned42_43 :
    AlignedValid 11 0 missing42_43 records42_43 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check42
    maskCheck42 AlignedValid.nil

def missing43_44 : List (BitVec (edgeCount 11)) :=
  [missing43]
abbrev records43_44 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record43]
theorem aligned43_44 :
    AlignedValid 11 0 missing43_44 records43_44 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check43
    maskCheck43 AlignedValid.nil

def missing42_44 : List (BitVec (edgeCount 11)) :=
  missing42_43 ++ missing43_44
abbrev records42_44 : List Blob :=
  records42_43 ++ records43_44
theorem aligned42_44 :
    AlignedValid 11 0 missing42_44 records42_44 :=
  aligned42_43.append aligned43_44

def missing40_44 : List (BitVec (edgeCount 11)) :=
  missing40_42 ++ missing42_44
abbrev records40_44 : List Blob :=
  records40_42 ++ records42_44
theorem aligned40_44 :
    AlignedValid 11 0 missing40_44 records40_44 :=
  aligned40_42.append aligned42_44

def missing44_45 : List (BitVec (edgeCount 11)) :=
  [missing44]
abbrev records44_45 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record44]
theorem aligned44_45 :
    AlignedValid 11 0 missing44_45 records44_45 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check44
    maskCheck44 AlignedValid.nil

def missing45_46 : List (BitVec (edgeCount 11)) :=
  [missing45]
abbrev records45_46 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record45]
theorem aligned45_46 :
    AlignedValid 11 0 missing45_46 records45_46 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check45
    maskCheck45 AlignedValid.nil

def missing44_46 : List (BitVec (edgeCount 11)) :=
  missing44_45 ++ missing45_46
abbrev records44_46 : List Blob :=
  records44_45 ++ records45_46
theorem aligned44_46 :
    AlignedValid 11 0 missing44_46 records44_46 :=
  aligned44_45.append aligned45_46

def missing46_47 : List (BitVec (edgeCount 11)) :=
  [missing46]
abbrev records46_47 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record46]
theorem aligned46_47 :
    AlignedValid 11 0 missing46_47 records46_47 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check46
    maskCheck46 AlignedValid.nil

def missing47_48 : List (BitVec (edgeCount 11)) :=
  [missing47]
abbrev records47_48 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record47]
theorem aligned47_48 :
    AlignedValid 11 0 missing47_48 records47_48 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check47
    maskCheck47 AlignedValid.nil

def missing46_48 : List (BitVec (edgeCount 11)) :=
  missing46_47 ++ missing47_48
abbrev records46_48 : List Blob :=
  records46_47 ++ records47_48
theorem aligned46_48 :
    AlignedValid 11 0 missing46_48 records46_48 :=
  aligned46_47.append aligned47_48

def missing44_48 : List (BitVec (edgeCount 11)) :=
  missing44_46 ++ missing46_48
abbrev records44_48 : List Blob :=
  records44_46 ++ records46_48
theorem aligned44_48 :
    AlignedValid 11 0 missing44_48 records44_48 :=
  aligned44_46.append aligned46_48

def missing40_48 : List (BitVec (edgeCount 11)) :=
  missing40_44 ++ missing44_48
abbrev records40_48 : List Blob :=
  records40_44 ++ records44_48
theorem aligned40_48 :
    AlignedValid 11 0 missing40_48 records40_48 :=
  aligned40_44.append aligned44_48

def missing32_48 : List (BitVec (edgeCount 11)) :=
  missing32_40 ++ missing40_48
abbrev records32_48 : List Blob :=
  records32_40 ++ records40_48
theorem aligned32_48 :
    AlignedValid 11 0 missing32_48 records32_48 :=
  aligned32_40.append aligned40_48

def missing48_49 : List (BitVec (edgeCount 11)) :=
  [missing48]
abbrev records48_49 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record48]
theorem aligned48_49 :
    AlignedValid 11 0 missing48_49 records48_49 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check48
    maskCheck48 AlignedValid.nil

def missing49_50 : List (BitVec (edgeCount 11)) :=
  [missing49]
abbrev records49_50 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record49]
theorem aligned49_50 :
    AlignedValid 11 0 missing49_50 records49_50 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check49
    maskCheck49 AlignedValid.nil

def missing48_50 : List (BitVec (edgeCount 11)) :=
  missing48_49 ++ missing49_50
abbrev records48_50 : List Blob :=
  records48_49 ++ records49_50
theorem aligned48_50 :
    AlignedValid 11 0 missing48_50 records48_50 :=
  aligned48_49.append aligned49_50

def missing50_51 : List (BitVec (edgeCount 11)) :=
  [missing50]
abbrev records50_51 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record50]
theorem aligned50_51 :
    AlignedValid 11 0 missing50_51 records50_51 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check50
    maskCheck50 AlignedValid.nil

def missing51_52 : List (BitVec (edgeCount 11)) :=
  [missing51]
abbrev records51_52 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record51]
theorem aligned51_52 :
    AlignedValid 11 0 missing51_52 records51_52 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check51
    maskCheck51 AlignedValid.nil

def missing50_52 : List (BitVec (edgeCount 11)) :=
  missing50_51 ++ missing51_52
abbrev records50_52 : List Blob :=
  records50_51 ++ records51_52
theorem aligned50_52 :
    AlignedValid 11 0 missing50_52 records50_52 :=
  aligned50_51.append aligned51_52

def missing48_52 : List (BitVec (edgeCount 11)) :=
  missing48_50 ++ missing50_52
abbrev records48_52 : List Blob :=
  records48_50 ++ records50_52
theorem aligned48_52 :
    AlignedValid 11 0 missing48_52 records48_52 :=
  aligned48_50.append aligned50_52

def missing52_53 : List (BitVec (edgeCount 11)) :=
  [missing52]
abbrev records52_53 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record52]
theorem aligned52_53 :
    AlignedValid 11 0 missing52_53 records52_53 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check52
    maskCheck52 AlignedValid.nil

def missing53_54 : List (BitVec (edgeCount 11)) :=
  [missing53]
abbrev records53_54 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record53]
theorem aligned53_54 :
    AlignedValid 11 0 missing53_54 records53_54 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check53
    maskCheck53 AlignedValid.nil

def missing52_54 : List (BitVec (edgeCount 11)) :=
  missing52_53 ++ missing53_54
abbrev records52_54 : List Blob :=
  records52_53 ++ records53_54
theorem aligned52_54 :
    AlignedValid 11 0 missing52_54 records52_54 :=
  aligned52_53.append aligned53_54

def missing54_55 : List (BitVec (edgeCount 11)) :=
  [missing54]
abbrev records54_55 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record54]
theorem aligned54_55 :
    AlignedValid 11 0 missing54_55 records54_55 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check54
    maskCheck54 AlignedValid.nil

def missing55_56 : List (BitVec (edgeCount 11)) :=
  [missing55]
abbrev records55_56 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record55]
theorem aligned55_56 :
    AlignedValid 11 0 missing55_56 records55_56 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check55
    maskCheck55 AlignedValid.nil

def missing54_56 : List (BitVec (edgeCount 11)) :=
  missing54_55 ++ missing55_56
abbrev records54_56 : List Blob :=
  records54_55 ++ records55_56
theorem aligned54_56 :
    AlignedValid 11 0 missing54_56 records54_56 :=
  aligned54_55.append aligned55_56

def missing52_56 : List (BitVec (edgeCount 11)) :=
  missing52_54 ++ missing54_56
abbrev records52_56 : List Blob :=
  records52_54 ++ records54_56
theorem aligned52_56 :
    AlignedValid 11 0 missing52_56 records52_56 :=
  aligned52_54.append aligned54_56

def missing48_56 : List (BitVec (edgeCount 11)) :=
  missing48_52 ++ missing52_56
abbrev records48_56 : List Blob :=
  records48_52 ++ records52_56
theorem aligned48_56 :
    AlignedValid 11 0 missing48_56 records48_56 :=
  aligned48_52.append aligned52_56

def missing56_57 : List (BitVec (edgeCount 11)) :=
  [missing56]
abbrev records56_57 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record56]
theorem aligned56_57 :
    AlignedValid 11 0 missing56_57 records56_57 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check56
    maskCheck56 AlignedValid.nil

def missing57_58 : List (BitVec (edgeCount 11)) :=
  [missing57]
abbrev records57_58 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record57]
theorem aligned57_58 :
    AlignedValid 11 0 missing57_58 records57_58 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check57
    maskCheck57 AlignedValid.nil

def missing56_58 : List (BitVec (edgeCount 11)) :=
  missing56_57 ++ missing57_58
abbrev records56_58 : List Blob :=
  records56_57 ++ records57_58
theorem aligned56_58 :
    AlignedValid 11 0 missing56_58 records56_58 :=
  aligned56_57.append aligned57_58

def missing58_59 : List (BitVec (edgeCount 11)) :=
  [missing58]
abbrev records58_59 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record58]
theorem aligned58_59 :
    AlignedValid 11 0 missing58_59 records58_59 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check58
    maskCheck58 AlignedValid.nil

def missing59_60 : List (BitVec (edgeCount 11)) :=
  [missing59]
abbrev records59_60 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record59]
theorem aligned59_60 :
    AlignedValid 11 0 missing59_60 records59_60 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check59
    maskCheck59 AlignedValid.nil

def missing58_60 : List (BitVec (edgeCount 11)) :=
  missing58_59 ++ missing59_60
abbrev records58_60 : List Blob :=
  records58_59 ++ records59_60
theorem aligned58_60 :
    AlignedValid 11 0 missing58_60 records58_60 :=
  aligned58_59.append aligned59_60

def missing56_60 : List (BitVec (edgeCount 11)) :=
  missing56_58 ++ missing58_60
abbrev records56_60 : List Blob :=
  records56_58 ++ records58_60
theorem aligned56_60 :
    AlignedValid 11 0 missing56_60 records56_60 :=
  aligned56_58.append aligned58_60

def missing60_61 : List (BitVec (edgeCount 11)) :=
  [missing60]
abbrev records60_61 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record60]
theorem aligned60_61 :
    AlignedValid 11 0 missing60_61 records60_61 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check60
    maskCheck60 AlignedValid.nil

def missing61_62 : List (BitVec (edgeCount 11)) :=
  [missing61]
abbrev records61_62 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record61]
theorem aligned61_62 :
    AlignedValid 11 0 missing61_62 records61_62 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check61
    maskCheck61 AlignedValid.nil

def missing60_62 : List (BitVec (edgeCount 11)) :=
  missing60_61 ++ missing61_62
abbrev records60_62 : List Blob :=
  records60_61 ++ records61_62
theorem aligned60_62 :
    AlignedValid 11 0 missing60_62 records60_62 :=
  aligned60_61.append aligned61_62

def missing62_63 : List (BitVec (edgeCount 11)) :=
  [missing62]
abbrev records62_63 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record62]
theorem aligned62_63 :
    AlignedValid 11 0 missing62_63 records62_63 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check62
    maskCheck62 AlignedValid.nil

def missing63_64 : List (BitVec (edgeCount 11)) :=
  [missing63]
abbrev records63_64 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard1.record63]
theorem aligned63_64 :
    AlignedValid 11 0 missing63_64 records63_64 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard1.check63
    maskCheck63 AlignedValid.nil

def missing62_64 : List (BitVec (edgeCount 11)) :=
  missing62_63 ++ missing63_64
abbrev records62_64 : List Blob :=
  records62_63 ++ records63_64
theorem aligned62_64 :
    AlignedValid 11 0 missing62_64 records62_64 :=
  aligned62_63.append aligned63_64

def missing60_64 : List (BitVec (edgeCount 11)) :=
  missing60_62 ++ missing62_64
abbrev records60_64 : List Blob :=
  records60_62 ++ records62_64
theorem aligned60_64 :
    AlignedValid 11 0 missing60_64 records60_64 :=
  aligned60_62.append aligned62_64

def missing56_64 : List (BitVec (edgeCount 11)) :=
  missing56_60 ++ missing60_64
abbrev records56_64 : List Blob :=
  records56_60 ++ records60_64
theorem aligned56_64 :
    AlignedValid 11 0 missing56_64 records56_64 :=
  aligned56_60.append aligned60_64

def missing48_64 : List (BitVec (edgeCount 11)) :=
  missing48_56 ++ missing56_64
abbrev records48_64 : List Blob :=
  records48_56 ++ records56_64
theorem aligned48_64 :
    AlignedValid 11 0 missing48_64 records48_64 :=
  aligned48_56.append aligned56_64

def missing32_64 : List (BitVec (edgeCount 11)) :=
  missing32_48 ++ missing48_64
abbrev records32_64 : List Blob :=
  records32_48 ++ records48_64
theorem aligned32_64 :
    AlignedValid 11 0 missing32_64 records32_64 :=
  aligned32_48.append aligned48_64

abbrev missing : List (BitVec (edgeCount 11)) :=
  missing32_64
abbrev records : List Blob := records32_64
theorem aligned : AlignedValid 11 0 missing records :=
  aligned32_64

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A0AlignedShard001

