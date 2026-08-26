/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN11Pilot172Shard5

/-! Decode-only alignment checks for a=0, records 160--171. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A0AlignedShard005

open PackedBucketCertificate

def missing160 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 633938250858496
theorem maskCheck160 :
    checkMaskFor missing160 StrongPackedBucketN11Pilot172Shard5.record160 = true := by
  decide

def missing161 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2533894343655424
theorem maskCheck161 :
    checkMaskFor missing161 StrongPackedBucketN11Pilot172Shard5.record161 = true := by
  decide

def missing162 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4574587924807680
theorem maskCheck162 :
    checkMaskFor missing162 StrongPackedBucketN11Pilot172Shard5.record162 = true := by
  decide

def missing163 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 107203461677056
theorem maskCheck163 :
    checkMaskFor missing163 StrongPackedBucketN11Pilot172Shard5.record163 = true := by
  decide

def missing164 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 318309694210048
theorem maskCheck164 :
    checkMaskFor missing164 StrongPackedBucketN11Pilot172Shard5.record164 = true := by
  decide

def missing165 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 846075275542528
theorem maskCheck165 :
    checkMaskFor missing165 StrongPackedBucketN11Pilot172Shard5.record165 = true := by
  decide

def missing166 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1162734624342016
theorem maskCheck166 :
    checkMaskFor missing166 StrongPackedBucketN11Pilot172Shard5.record166 = true := by
  decide

def missing167 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 2288634531184640
theorem maskCheck167 :
    checkMaskFor missing167 StrongPackedBucketN11Pilot172Shard5.record167 = true := by
  decide

def missing168 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 215574076489728
theorem maskCheck168 :
    checkMaskFor missing168 StrongPackedBucketN11Pilot172Shard5.record168 = true := by
  decide

def missing169 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 4578436215504896
theorem maskCheck169 :
    checkMaskFor missing169 StrongPackedBucketN11Pilot172Shard5.record169 = true := by
  decide

def missing170 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 106654783833088
theorem maskCheck170 :
    checkMaskFor missing170 StrongPackedBucketN11Pilot172Shard5.record170 = true := by
  decide

def missing171 : BitVec (edgeCount 11) :=
  BitVec.ofNat (edgeCount 11) 1162185946498048
theorem maskCheck171 :
    checkMaskFor missing171 StrongPackedBucketN11Pilot172Shard5.record171 = true := by
  decide

def missing160_161 : List (BitVec (edgeCount 11)) :=
  [missing160]
abbrev records160_161 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard5.record160]
theorem aligned160_161 :
    AlignedValid 11 0 missing160_161 records160_161 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard5.check160
    maskCheck160 AlignedValid.nil

def missing161_162 : List (BitVec (edgeCount 11)) :=
  [missing161]
abbrev records161_162 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard5.record161]
theorem aligned161_162 :
    AlignedValid 11 0 missing161_162 records161_162 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard5.check161
    maskCheck161 AlignedValid.nil

def missing162_163 : List (BitVec (edgeCount 11)) :=
  [missing162]
abbrev records162_163 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard5.record162]
theorem aligned162_163 :
    AlignedValid 11 0 missing162_163 records162_163 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard5.check162
    maskCheck162 AlignedValid.nil

def missing161_163 : List (BitVec (edgeCount 11)) :=
  missing161_162 ++ missing162_163
abbrev records161_163 : List Blob :=
  records161_162 ++ records162_163
theorem aligned161_163 :
    AlignedValid 11 0 missing161_163 records161_163 :=
  aligned161_162.append aligned162_163

def missing160_163 : List (BitVec (edgeCount 11)) :=
  missing160_161 ++ missing161_163
abbrev records160_163 : List Blob :=
  records160_161 ++ records161_163
theorem aligned160_163 :
    AlignedValid 11 0 missing160_163 records160_163 :=
  aligned160_161.append aligned161_163

def missing163_164 : List (BitVec (edgeCount 11)) :=
  [missing163]
abbrev records163_164 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard5.record163]
theorem aligned163_164 :
    AlignedValid 11 0 missing163_164 records163_164 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard5.check163
    maskCheck163 AlignedValid.nil

def missing164_165 : List (BitVec (edgeCount 11)) :=
  [missing164]
abbrev records164_165 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard5.record164]
theorem aligned164_165 :
    AlignedValid 11 0 missing164_165 records164_165 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard5.check164
    maskCheck164 AlignedValid.nil

def missing165_166 : List (BitVec (edgeCount 11)) :=
  [missing165]
abbrev records165_166 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard5.record165]
theorem aligned165_166 :
    AlignedValid 11 0 missing165_166 records165_166 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard5.check165
    maskCheck165 AlignedValid.nil

def missing164_166 : List (BitVec (edgeCount 11)) :=
  missing164_165 ++ missing165_166
abbrev records164_166 : List Blob :=
  records164_165 ++ records165_166
theorem aligned164_166 :
    AlignedValid 11 0 missing164_166 records164_166 :=
  aligned164_165.append aligned165_166

def missing163_166 : List (BitVec (edgeCount 11)) :=
  missing163_164 ++ missing164_166
abbrev records163_166 : List Blob :=
  records163_164 ++ records164_166
theorem aligned163_166 :
    AlignedValid 11 0 missing163_166 records163_166 :=
  aligned163_164.append aligned164_166

def missing160_166 : List (BitVec (edgeCount 11)) :=
  missing160_163 ++ missing163_166
abbrev records160_166 : List Blob :=
  records160_163 ++ records163_166
theorem aligned160_166 :
    AlignedValid 11 0 missing160_166 records160_166 :=
  aligned160_163.append aligned163_166

def missing166_167 : List (BitVec (edgeCount 11)) :=
  [missing166]
abbrev records166_167 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard5.record166]
theorem aligned166_167 :
    AlignedValid 11 0 missing166_167 records166_167 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard5.check166
    maskCheck166 AlignedValid.nil

def missing167_168 : List (BitVec (edgeCount 11)) :=
  [missing167]
abbrev records167_168 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard5.record167]
theorem aligned167_168 :
    AlignedValid 11 0 missing167_168 records167_168 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard5.check167
    maskCheck167 AlignedValid.nil

def missing168_169 : List (BitVec (edgeCount 11)) :=
  [missing168]
abbrev records168_169 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard5.record168]
theorem aligned168_169 :
    AlignedValid 11 0 missing168_169 records168_169 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard5.check168
    maskCheck168 AlignedValid.nil

def missing167_169 : List (BitVec (edgeCount 11)) :=
  missing167_168 ++ missing168_169
abbrev records167_169 : List Blob :=
  records167_168 ++ records168_169
theorem aligned167_169 :
    AlignedValid 11 0 missing167_169 records167_169 :=
  aligned167_168.append aligned168_169

def missing166_169 : List (BitVec (edgeCount 11)) :=
  missing166_167 ++ missing167_169
abbrev records166_169 : List Blob :=
  records166_167 ++ records167_169
theorem aligned166_169 :
    AlignedValid 11 0 missing166_169 records166_169 :=
  aligned166_167.append aligned167_169

def missing169_170 : List (BitVec (edgeCount 11)) :=
  [missing169]
abbrev records169_170 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard5.record169]
theorem aligned169_170 :
    AlignedValid 11 0 missing169_170 records169_170 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard5.check169
    maskCheck169 AlignedValid.nil

def missing170_171 : List (BitVec (edgeCount 11)) :=
  [missing170]
abbrev records170_171 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard5.record170]
theorem aligned170_171 :
    AlignedValid 11 0 missing170_171 records170_171 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard5.check170
    maskCheck170 AlignedValid.nil

def missing171_172 : List (BitVec (edgeCount 11)) :=
  [missing171]
abbrev records171_172 : List Blob :=
  [StrongPackedBucketN11Pilot172Shard5.record171]
theorem aligned171_172 :
    AlignedValid 11 0 missing171_172 records171_172 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN11Pilot172Shard5.check171
    maskCheck171 AlignedValid.nil

def missing170_172 : List (BitVec (edgeCount 11)) :=
  missing170_171 ++ missing171_172
abbrev records170_172 : List Blob :=
  records170_171 ++ records171_172
theorem aligned170_172 :
    AlignedValid 11 0 missing170_172 records170_172 :=
  aligned170_171.append aligned171_172

def missing169_172 : List (BitVec (edgeCount 11)) :=
  missing169_170 ++ missing170_172
abbrev records169_172 : List Blob :=
  records169_170 ++ records170_172
theorem aligned169_172 :
    AlignedValid 11 0 missing169_172 records169_172 :=
  aligned169_170.append aligned170_172

def missing166_172 : List (BitVec (edgeCount 11)) :=
  missing166_169 ++ missing169_172
abbrev records166_172 : List Blob :=
  records166_169 ++ records169_172
theorem aligned166_172 :
    AlignedValid 11 0 missing166_172 records166_172 :=
  aligned166_169.append aligned169_172

def missing160_172 : List (BitVec (edgeCount 11)) :=
  missing160_166 ++ missing166_172
abbrev records160_172 : List Blob :=
  records160_166 ++ records166_172
theorem aligned160_172 :
    AlignedValid 11 0 missing160_172 records160_172 :=
  aligned160_166.append aligned166_172

abbrev missing : List (BitVec (edgeCount 11)) :=
  missing160_172
abbrev records : List Blob := records160_172
theorem aligned : AlignedValid 11 0 missing records :=
  aligned160_172

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN11A0AlignedShard005

