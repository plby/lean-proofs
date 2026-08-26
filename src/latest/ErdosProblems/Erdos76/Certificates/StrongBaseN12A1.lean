/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Through9
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A1Aligned

/-!
# The `n = 12`, `a = 1` strong almost-complete base

This module joins the checked missing-edge exhaustion through level nine to
the order-aligned packed strong certificates for all 1405 representatives.
-/

namespace Erdos76.CertificateChecker.Certificates.StrongBaseN12A1

open CertificateExhaustion
open CertificateExhaustion.Certificates
open PackedBucketCertificate

private def maskChunk (start count : ℕ) :
    List (BitVec (edgeCount 12)) :=
  List.ofFn (fun i : Fin count ↦
    PackedExhaustionN12.level9.maskAt (start + i))

private lemma maskChunk_add (start left right : ℕ) :
    maskChunk start (left + right) =
      maskChunk start left ++ maskChunk (start + left) right := by
  unfold maskChunk
  simpa only [Nat.add_assoc, Fin.val_castLE, Fin.val_natAdd] using
    (List.ofFn_add (f := fun i : Fin (left + right) ↦
      PackedExhaustionN12.level9.maskAt (start + i)))

/-- The independently generated exhaustion and packing corpora use the same
canonical ordering at level nine. -/
theorem level9_toList_eq_missing :
    PackedExhaustionN12.level9.toArray.toList =
      StrongPackedBucketN12A1Aligned.missing := by
  have h000 : maskChunk 0 32 =
      StrongPackedBucketN12A1AlignedShard000.missing0_32 := by decide
  have h001 : maskChunk 32 32 =
      StrongPackedBucketN12A1AlignedShard000.missing32_64 := by decide
  have h002 : maskChunk 64 32 =
      StrongPackedBucketN12A1AlignedShard000.missing64_96 := by decide
  have h003 : maskChunk 96 32 =
      StrongPackedBucketN12A1AlignedShard000.missing96_128 := by decide
  have h100 : maskChunk 128 32 =
      StrongPackedBucketN12A1AlignedShard001.missing128_160 := by decide
  have h101 : maskChunk 160 32 =
      StrongPackedBucketN12A1AlignedShard001.missing160_192 := by decide
  have h102 : maskChunk 192 32 =
      StrongPackedBucketN12A1AlignedShard001.missing192_224 := by decide
  have h103 : maskChunk 224 32 =
      StrongPackedBucketN12A1AlignedShard001.missing224_256 := by decide
  have h200 : maskChunk 256 32 =
      StrongPackedBucketN12A1AlignedShard002.missing256_288 := by decide
  have h201 : maskChunk 288 32 =
      StrongPackedBucketN12A1AlignedShard002.missing288_320 := by decide
  have h202 : maskChunk 320 32 =
      StrongPackedBucketN12A1AlignedShard002.missing320_352 := by decide
  have h203 : maskChunk 352 32 =
      StrongPackedBucketN12A1AlignedShard002.missing352_384 := by decide
  have h300 : maskChunk 384 32 =
      StrongPackedBucketN12A1AlignedShard003.missing384_416 := by decide
  have h301 : maskChunk 416 32 =
      StrongPackedBucketN12A1AlignedShard003.missing416_448 := by decide
  have h302 : maskChunk 448 32 =
      StrongPackedBucketN12A1AlignedShard003.missing448_480 := by decide
  have h303 : maskChunk 480 32 =
      StrongPackedBucketN12A1AlignedShard003.missing480_512 := by decide
  have h400 : maskChunk 512 32 =
      StrongPackedBucketN12A1AlignedShard004.missing512_544 := by decide
  have h401 : maskChunk 544 32 =
      StrongPackedBucketN12A1AlignedShard004.missing544_576 := by decide
  have h402 : maskChunk 576 32 =
      StrongPackedBucketN12A1AlignedShard004.missing576_608 := by decide
  have h403 : maskChunk 608 32 =
      StrongPackedBucketN12A1AlignedShard004.missing608_640 := by decide
  have h500 : maskChunk 640 32 =
      StrongPackedBucketN12A1AlignedShard005.missing640_672 := by decide
  have h501 : maskChunk 672 32 =
      StrongPackedBucketN12A1AlignedShard005.missing672_704 := by decide
  have h502 : maskChunk 704 32 =
      StrongPackedBucketN12A1AlignedShard005.missing704_736 := by decide
  have h503 : maskChunk 736 32 =
      StrongPackedBucketN12A1AlignedShard005.missing736_768 := by decide
  have h600 : maskChunk 768 32 =
      StrongPackedBucketN12A1AlignedShard006.missing768_800 := by decide
  have h601 : maskChunk 800 32 =
      StrongPackedBucketN12A1AlignedShard006.missing800_832 := by decide
  have h602 : maskChunk 832 32 =
      StrongPackedBucketN12A1AlignedShard006.missing832_864 := by decide
  have h603 : maskChunk 864 32 =
      StrongPackedBucketN12A1AlignedShard006.missing864_896 := by decide
  have h700 : maskChunk 896 32 =
      StrongPackedBucketN12A1AlignedShard007.missing896_928 := by decide
  have h701 : maskChunk 928 32 =
      StrongPackedBucketN12A1AlignedShard007.missing928_960 := by decide
  have h702 : maskChunk 960 32 =
      StrongPackedBucketN12A1AlignedShard007.missing960_992 := by decide
  have h703 : maskChunk 992 32 =
      StrongPackedBucketN12A1AlignedShard007.missing992_1024 := by decide
  have h800 : maskChunk 1024 32 =
      StrongPackedBucketN12A1AlignedShard008.missing1024_1056 := by decide
  have h801 : maskChunk 1056 32 =
      StrongPackedBucketN12A1AlignedShard008.missing1056_1088 := by decide
  have h802 : maskChunk 1088 32 =
      StrongPackedBucketN12A1AlignedShard008.missing1088_1120 := by decide
  have h803 : maskChunk 1120 32 =
      StrongPackedBucketN12A1AlignedShard008.missing1120_1152 := by decide
  have h900 : maskChunk 1152 32 =
      StrongPackedBucketN12A1AlignedShard009.missing1152_1184 := by decide
  have h901 : maskChunk 1184 32 =
      StrongPackedBucketN12A1AlignedShard009.missing1184_1216 := by decide
  have h902 : maskChunk 1216 32 =
      StrongPackedBucketN12A1AlignedShard009.missing1216_1248 := by decide
  have h903 : maskChunk 1248 32 =
      StrongPackedBucketN12A1AlignedShard009.missing1248_1280 := by decide
  have h1000 : maskChunk 1280 31 =
      StrongPackedBucketN12A1AlignedShard010.missing1280_1311 := by decide
  have h1001 : maskChunk 1311 31 =
      StrongPackedBucketN12A1AlignedShard010.missing1311_1342 := by decide
  have h1002 : maskChunk 1342 31 =
      StrongPackedBucketN12A1AlignedShard010.missing1342_1373 := by decide
  have h1003 : maskChunk 1373 32 =
      StrongPackedBucketN12A1AlignedShard010.missing1373_1405 := by decide
  have hs0 : maskChunk 0 128 =
      StrongPackedBucketN12A1AlignedShard000.missing := by
    rw [show 128 = 64 + 64 by omega, maskChunk_add,
      show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add,
      h000, h001, h002, h003]
    rfl
  have hs1 : maskChunk 128 128 =
      StrongPackedBucketN12A1AlignedShard001.missing := by
    rw [show 128 = 64 + 64 by omega, maskChunk_add,
      show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add,
      h100, h101, h102, h103]
    rfl
  have hs2 : maskChunk 256 128 =
      StrongPackedBucketN12A1AlignedShard002.missing := by
    rw [show 128 = 64 + 64 by omega, maskChunk_add,
      show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add,
      h200, h201, h202, h203]
    rfl
  have hs3 : maskChunk 384 128 =
      StrongPackedBucketN12A1AlignedShard003.missing := by
    rw [show 128 = 64 + 64 by omega, maskChunk_add,
      show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add,
      h300, h301, h302, h303]
    rfl
  have hs4 : maskChunk 512 128 =
      StrongPackedBucketN12A1AlignedShard004.missing := by
    rw [show 128 = 64 + 64 by omega, maskChunk_add,
      show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add,
      h400, h401, h402, h403]
    rfl
  have hs5 : maskChunk 640 128 =
      StrongPackedBucketN12A1AlignedShard005.missing := by
    rw [show 128 = 64 + 64 by omega, maskChunk_add,
      show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add,
      h500, h501, h502, h503]
    rfl
  have hs6 : maskChunk 768 128 =
      StrongPackedBucketN12A1AlignedShard006.missing := by
    rw [show 128 = 64 + 64 by omega, maskChunk_add,
      show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add,
      h600, h601, h602, h603]
    rfl
  have hs7 : maskChunk 896 128 =
      StrongPackedBucketN12A1AlignedShard007.missing := by
    rw [show 128 = 64 + 64 by omega, maskChunk_add,
      show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add,
      h700, h701, h702, h703]
    rfl
  have hs8 : maskChunk 1024 128 =
      StrongPackedBucketN12A1AlignedShard008.missing := by
    rw [show 128 = 64 + 64 by omega, maskChunk_add,
      show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add,
      h800, h801, h802, h803]
    rfl
  have hs9 : maskChunk 1152 128 =
      StrongPackedBucketN12A1AlignedShard009.missing := by
    rw [show 128 = 64 + 64 by omega, maskChunk_add,
      show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add,
      h900, h901, h902, h903]
    rfl
  have hs10 : maskChunk 1280 125 =
      StrongPackedBucketN12A1AlignedShard010.missing := by
    rw [show 125 = 62 + 63 by omega, maskChunk_add,
      show 62 = 31 + 31 by omega, maskChunk_add,
      show 63 = 31 + 32 by omega, maskChunk_add,
      h1000, h1001, h1002, h1003]
    rfl
  have h02 : maskChunk 0 256 =
      StrongPackedBucketN12A1Aligned.missing0_2 := by
    rw [show 256 = 128 + 128 by omega, maskChunk_add, hs0, hs1]
    rfl
  have h25 : maskChunk 256 384 =
      StrongPackedBucketN12A1Aligned.missing2_5 := by
    rw [show 384 = 128 + 256 by omega, maskChunk_add,
      show 256 = 128 + 128 by omega, maskChunk_add, hs2, hs3, hs4]
    rfl
  have h05 : maskChunk 0 640 =
      StrongPackedBucketN12A1Aligned.missing0_5 := by
    rw [show 640 = 256 + 384 by omega, maskChunk_add, h02, h25]
    rfl
  have h58 : maskChunk 640 384 =
      StrongPackedBucketN12A1Aligned.missing5_8 := by
    rw [show 384 = 128 + 256 by omega, maskChunk_add,
      show 256 = 128 + 128 by omega, maskChunk_add, hs5, hs6, hs7]
    rfl
  have h811 : maskChunk 1024 381 =
      StrongPackedBucketN12A1Aligned.missing8_11 := by
    rw [show 381 = 128 + 253 by omega, maskChunk_add,
      show 253 = 128 + 125 by omega, maskChunk_add, hs8, hs9, hs10]
    rfl
  have h511 : maskChunk 640 765 =
      StrongPackedBucketN12A1Aligned.missing5_11 := by
    rw [show 765 = 384 + 381 by omega, maskChunk_add, h58, h811]
    rfl
  calc
    PackedExhaustionN12.level9.toArray.toList = maskChunk 0 1405 := by
      simp only [PackedExhaustionN12.level9,
        CertificateExhaustion.Packed.Level.toArray,
        Array.toList_ofFn, maskChunk, Nat.zero_add]
    _ = maskChunk 0 640 ++ maskChunk 640 765 := by
      rw [show 1405 = 640 + 765 by omega, maskChunk_add]
    _ = StrongPackedBucketN12A1Aligned.missing := by
      rw [h05, h511]
      rfl

theorem alignedLevel9 :
    AlignedValid 12 1 PackedExhaustionN12.level9.toArray.toList
      StrongPackedBucketN12A1Aligned.records := by
  rw [level9_toList_eq_missing]
  exact StrongPackedBucketN12A1Aligned.aligned

private lemma compl_edgeSet_ncard_eq_missingEdgeCount
    (G : SimpleGraph (Fin 12)) :
    Gᶜ.edgeSet.ncard = missingEdgeCount G := by
  classical
  exact Set.ncard_eq_toFinset_card' Gᶜ.edgeSet

/-- Every graph on twelve vertices with nine missing edges has the strong
one-defect fractional packing certified by the packed corpus. -/
theorem strongBase (G : SimpleGraph (Fin 12))
    (hmissing : missingEdgeCount G = 9) :
    HasStrongFractionalPacking G 1 := by
  have haligned :
      AlignedValid 12 1 (PackedExhaustionN12Through9.data.level 9).toList
        StrongPackedBucketN12A1Aligned.records := by
    change AlignedValid 12 1 PackedExhaustionN12.level9.toArray.toList
      StrongPackedBucketN12A1Aligned.records
    exact alignedLevel9
  have hcard : Gᶜ.edgeSet.ncard = 9 := by
    calc
      Gᶜ.edgeSet.ncard = missingEdgeCount G :=
        compl_edgeSet_ncard_eq_missingEdgeCount G
      _ = 9 := hmissing
  simpa [Nat.cast_one] using
    alignedValid_level_sound PackingCert.pairIndexValid_12
      PackedExhaustionN12Through9.valid (by decide) haligned G hcard

end Erdos76.CertificateChecker.Certificates.StrongBaseN12A1
