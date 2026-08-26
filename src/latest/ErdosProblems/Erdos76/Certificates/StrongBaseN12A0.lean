/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Through9
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A0Aligned

/-!
# The `n = 12`, `a = 0` strong almost-complete base

This module joins the checked missing-edge exhaustion through level eight to
the order-aligned packed strong certificates for all 485 representatives.
-/

namespace Erdos76.CertificateChecker.Certificates.StrongBaseN12A0

open CertificateExhaustion
open CertificateExhaustion.Certificates
open PackedBucketCertificate

private def maskChunk (start count : ℕ) :
    List (BitVec (edgeCount 12)) :=
  List.ofFn (fun i : Fin count ↦
    PackedExhaustionN12.level8.maskAt (start + i))

private lemma maskChunk_add (start left right : ℕ) :
    maskChunk start (left + right) =
      maskChunk start left ++ maskChunk (start + left) right := by
  unfold maskChunk
  simpa only [Nat.add_assoc, Fin.val_castLE, Fin.val_natAdd] using
    (List.ofFn_add (f := fun i : Fin (left + right) ↦
      PackedExhaustionN12.level8.maskAt (start + i)))

/-- The independently generated exhaustion and packing corpora use the same
canonical ordering at level eight. -/
theorem level8_toList_eq_missing :
    PackedExhaustionN12.level8.toArray.toList =
      StrongPackedBucketN12A0Aligned.missing := by
  have h00 : maskChunk 0 32 =
      StrongPackedBucketN12A0AlignedShard000.missing0_32 := by
    decide
  have h01 : maskChunk 32 32 =
      StrongPackedBucketN12A0AlignedShard000.missing32_64 := by
    decide
  have h02 : maskChunk 64 32 =
      StrongPackedBucketN12A0AlignedShard000.missing64_96 := by
    decide
  have h03 : maskChunk 96 32 =
      StrongPackedBucketN12A0AlignedShard000.missing96_128 := by
    decide
  have h10 : maskChunk 128 32 =
      StrongPackedBucketN12A0AlignedShard001.missing128_160 := by decide
  have h11 : maskChunk 160 32 =
      StrongPackedBucketN12A0AlignedShard001.missing160_192 := by decide
  have h12 : maskChunk 192 32 =
      StrongPackedBucketN12A0AlignedShard001.missing192_224 := by decide
  have h13 : maskChunk 224 32 =
      StrongPackedBucketN12A0AlignedShard001.missing224_256 := by decide
  have h20 : maskChunk 256 32 =
      StrongPackedBucketN12A0AlignedShard002.missing256_288 := by decide
  have h21 : maskChunk 288 32 =
      StrongPackedBucketN12A0AlignedShard002.missing288_320 := by decide
  have h22 : maskChunk 320 32 =
      StrongPackedBucketN12A0AlignedShard002.missing320_352 := by decide
  have h23 : maskChunk 352 32 =
      StrongPackedBucketN12A0AlignedShard002.missing352_384 := by decide
  have h30 : maskChunk 384 25 =
      StrongPackedBucketN12A0AlignedShard003.missing384_409 := by decide
  have h31 : maskChunk 409 25 =
      StrongPackedBucketN12A0AlignedShard003.missing409_434 := by decide
  have h32 : maskChunk 434 25 =
      StrongPackedBucketN12A0AlignedShard003.missing434_459 := by decide
  have h33 : maskChunk 459 26 =
      StrongPackedBucketN12A0AlignedShard003.missing459_485 := by decide
  have hs0 : maskChunk 0 128 =
      StrongPackedBucketN12A0AlignedShard000.missing := by
    calc
      maskChunk 0 128 =
          (maskChunk 0 32 ++ maskChunk 32 32) ++
            (maskChunk 64 32 ++ maskChunk 96 32) := by
        rw [show 128 = 64 + 64 by omega, maskChunk_add,
          show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add]
      _ = StrongPackedBucketN12A0AlignedShard000.missing := by
        rw [h00, h01, h02, h03]
        rfl
  have hs1 : maskChunk 128 128 =
      StrongPackedBucketN12A0AlignedShard001.missing := by
    calc
      maskChunk 128 128 =
          (maskChunk 128 32 ++ maskChunk 160 32) ++
            (maskChunk 192 32 ++ maskChunk 224 32) := by
        rw [show 128 = 64 + 64 by omega, maskChunk_add,
          show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add]
      _ = StrongPackedBucketN12A0AlignedShard001.missing := by
        rw [h10, h11, h12, h13]
        rfl
  have hs2 : maskChunk 256 128 =
      StrongPackedBucketN12A0AlignedShard002.missing := by
    calc
      maskChunk 256 128 =
          (maskChunk 256 32 ++ maskChunk 288 32) ++
            (maskChunk 320 32 ++ maskChunk 352 32) := by
        rw [show 128 = 64 + 64 by omega, maskChunk_add,
          show 64 = 32 + 32 by omega, maskChunk_add, maskChunk_add]
      _ = StrongPackedBucketN12A0AlignedShard002.missing := by
        rw [h20, h21, h22, h23]
        rfl
  have hs3 : maskChunk 384 101 =
      StrongPackedBucketN12A0AlignedShard003.missing := by
    calc
      maskChunk 384 101 =
          (maskChunk 384 25 ++ maskChunk 409 25) ++
            (maskChunk 434 25 ++ maskChunk 459 26) := by
        rw [show 101 = 50 + 51 by omega, maskChunk_add,
          show 50 = 25 + 25 by omega, maskChunk_add,
          show 51 = 25 + 26 by omega, maskChunk_add]
      _ = StrongPackedBucketN12A0AlignedShard003.missing := by
        rw [h30, h31, h32, h33]
        rfl
  calc
    PackedExhaustionN12.level8.toArray.toList = maskChunk 0 485 := by
      simp only [PackedExhaustionN12.level8,
        CertificateExhaustion.Packed.Level.toArray,
        Array.toList_ofFn, maskChunk, Nat.zero_add]
    _ = (maskChunk 0 128 ++ maskChunk 128 128) ++
        (maskChunk 256 128 ++ maskChunk 384 101) := by
      rw [show 485 = 256 + 229 by omega, maskChunk_add,
        show 256 = 128 + 128 by omega, maskChunk_add,
        show 229 = 128 + 101 by omega, maskChunk_add]
    _ = StrongPackedBucketN12A0Aligned.missing := by
      rw [hs0, hs1, hs2, hs3]
      rfl

theorem alignedLevel8 :
    AlignedValid 12 0 PackedExhaustionN12.level8.toArray.toList
      StrongPackedBucketN12A0Aligned.records := by
  rw [level8_toList_eq_missing]
  exact StrongPackedBucketN12A0Aligned.aligned

private lemma compl_edgeSet_ncard_eq_missingEdgeCount
    (G : SimpleGraph (Fin 12)) :
    Gᶜ.edgeSet.ncard = missingEdgeCount G := by
  classical
  exact Set.ncard_eq_toFinset_card' Gᶜ.edgeSet

/-- Every graph on twelve vertices with eight missing edges has the strong
zero-defect fractional packing certified by the packed corpus. -/
theorem strongBase (G : SimpleGraph (Fin 12))
    (hmissing : missingEdgeCount G = 8) :
    HasStrongFractionalPacking G 0 := by
  have haligned :
      AlignedValid 12 0 (PackedExhaustionN12Through9.data.level 8).toList
        StrongPackedBucketN12A0Aligned.records := by
    change AlignedValid 12 0 PackedExhaustionN12.level8.toArray.toList
      StrongPackedBucketN12A0Aligned.records
    exact alignedLevel8
  have hcard : Gᶜ.edgeSet.ncard = 8 := by
    calc
      Gᶜ.edgeSet.ncard = missingEdgeCount G :=
        compl_edgeSet_ncard_eq_missingEdgeCount G
      _ = 8 := hmissing
  simpa [Nat.cast_zero] using
    alignedValid_level_sound PackingCert.pairIndexValid_12
      PackedExhaustionN12Through9.valid (by decide) haligned G hcard

end Erdos76.CertificateChecker.Certificates.StrongBaseN12A0
