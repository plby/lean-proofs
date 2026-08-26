/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Through11
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A3Aligned

/-! The exact `n = 12`, `a = 3` strong almost-complete base. -/
namespace Erdos76.CertificateChecker.Certificates.StrongBaseN12A3

open CertificateExhaustion
open CertificateExhaustion.Certificates
open PackedBucketCertificate

private def maskChunk (start count : ℕ) :
    List (BitVec (edgeCount 12)) :=
  List.ofFn (fun i : Fin count ↦
    PackedExhaustionN12.level11.maskAt (start + i))

private lemma maskChunk_add (start left right : ℕ) :
    maskChunk start (left + right) =
      maskChunk start left ++ maskChunk (start + left) right := by
  unfold maskChunk
  simpa only [Nat.add_assoc, Fin.val_castLE, Fin.val_natAdd] using
    (List.ofFn_add (f := fun i : Fin (left + right) ↦
      PackedExhaustionN12.level11.maskAt (start + i)))

private def nativeMaskList : List (BitVec (edgeCount 12)) :=
  List.ofFn (fun i : Fin PackedExhaustionN12.level11.count ↦
    PackedExhaustionN12.level11.maskAt i)

private theorem level11_to_nativeMaskList :
    PackedExhaustionN12.level11.toArray.toList = nativeMaskList := by
  unfold CertificateExhaustion.Packed.Level.toArray nativeMaskList
  exact Array.toList_ofFn

private theorem level11_count :
    PackedExhaustionN12.level11.count = 12763 := by
  rfl

private theorem nativeMaskList_eq_maskChunk :
    nativeMaskList = maskChunk 0 12763 := by
  unfold nativeMaskList maskChunk
  have hc : PackedExhaustionN12.level11.count = 12763 :=
    level11_count
  cases hc
  have h := List.ofFn_congr rfl
    (fun i : Fin 12763 ↦ PackedExhaustionN12.level11.maskAt i)
  refine h.trans ?_
  apply congrArg
    (fun f : Fin 12763 → BitVec (edgeCount 12) ↦ List.ofFn f)
  funext i
  apply congrArg PackedExhaustionN12.level11.maskAt
  simp only [Fin.val_cast, Nat.zero_add]

private theorem shardMask0 : maskChunk 0 128 =
    StrongPackedBucketN12A3AlignedShard000.missing := by
  have h0_32 : maskChunk 0 32 =
      StrongPackedBucketN12A3AlignedShard000.missing0_32 := by decide
  have h32_64 : maskChunk 32 32 =
      StrongPackedBucketN12A3AlignedShard000.missing32_64 := by decide
  have h64_96 : maskChunk 64 32 =
      StrongPackedBucketN12A3AlignedShard000.missing64_96 := by decide
  have h96_128 : maskChunk 96 32 =
      StrongPackedBucketN12A3AlignedShard000.missing96_128 := by decide
  have h0_64 : maskChunk 0 64 =
      StrongPackedBucketN12A3AlignedShard000.missing0_64 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h0_32, h32_64]
    rfl
  have h64_128 : maskChunk 64 64 =
      StrongPackedBucketN12A3AlignedShard000.missing64_128 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h64_96, h96_128]
    rfl
  have h0_128 : maskChunk 0 128 =
      StrongPackedBucketN12A3AlignedShard000.missing0_128 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h0_64, h64_128]
    rfl
  exact h0_128

private theorem shardMask1 : maskChunk 128 128 =
    StrongPackedBucketN12A3AlignedShard001.missing := by
  have h128_160 : maskChunk 128 32 =
      StrongPackedBucketN12A3AlignedShard001.missing128_160 := by decide
  have h160_192 : maskChunk 160 32 =
      StrongPackedBucketN12A3AlignedShard001.missing160_192 := by decide
  have h192_224 : maskChunk 192 32 =
      StrongPackedBucketN12A3AlignedShard001.missing192_224 := by decide
  have h224_256 : maskChunk 224 32 =
      StrongPackedBucketN12A3AlignedShard001.missing224_256 := by decide
  have h128_192 : maskChunk 128 64 =
      StrongPackedBucketN12A3AlignedShard001.missing128_192 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h128_160, h160_192]
    rfl
  have h192_256 : maskChunk 192 64 =
      StrongPackedBucketN12A3AlignedShard001.missing192_256 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h192_224, h224_256]
    rfl
  have h128_256 : maskChunk 128 128 =
      StrongPackedBucketN12A3AlignedShard001.missing128_256 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h128_192, h192_256]
    rfl
  exact h128_256

private theorem shardMask2 : maskChunk 256 128 =
    StrongPackedBucketN12A3AlignedShard002.missing := by
  have h256_288 : maskChunk 256 32 =
      StrongPackedBucketN12A3AlignedShard002.missing256_288 := by decide
  have h288_320 : maskChunk 288 32 =
      StrongPackedBucketN12A3AlignedShard002.missing288_320 := by decide
  have h320_352 : maskChunk 320 32 =
      StrongPackedBucketN12A3AlignedShard002.missing320_352 := by decide
  have h352_384 : maskChunk 352 32 =
      StrongPackedBucketN12A3AlignedShard002.missing352_384 := by decide
  have h256_320 : maskChunk 256 64 =
      StrongPackedBucketN12A3AlignedShard002.missing256_320 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h256_288, h288_320]
    rfl
  have h320_384 : maskChunk 320 64 =
      StrongPackedBucketN12A3AlignedShard002.missing320_384 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h320_352, h352_384]
    rfl
  have h256_384 : maskChunk 256 128 =
      StrongPackedBucketN12A3AlignedShard002.missing256_384 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h256_320, h320_384]
    rfl
  exact h256_384

private theorem shardMask3 : maskChunk 384 128 =
    StrongPackedBucketN12A3AlignedShard003.missing := by
  have h384_416 : maskChunk 384 32 =
      StrongPackedBucketN12A3AlignedShard003.missing384_416 := by decide
  have h416_448 : maskChunk 416 32 =
      StrongPackedBucketN12A3AlignedShard003.missing416_448 := by decide
  have h448_480 : maskChunk 448 32 =
      StrongPackedBucketN12A3AlignedShard003.missing448_480 := by decide
  have h480_512 : maskChunk 480 32 =
      StrongPackedBucketN12A3AlignedShard003.missing480_512 := by decide
  have h384_448 : maskChunk 384 64 =
      StrongPackedBucketN12A3AlignedShard003.missing384_448 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h384_416, h416_448]
    rfl
  have h448_512 : maskChunk 448 64 =
      StrongPackedBucketN12A3AlignedShard003.missing448_512 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h448_480, h480_512]
    rfl
  have h384_512 : maskChunk 384 128 =
      StrongPackedBucketN12A3AlignedShard003.missing384_512 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h384_448, h448_512]
    rfl
  exact h384_512

private theorem shardMask4 : maskChunk 512 128 =
    StrongPackedBucketN12A3AlignedShard004.missing := by
  have h512_544 : maskChunk 512 32 =
      StrongPackedBucketN12A3AlignedShard004.missing512_544 := by decide
  have h544_576 : maskChunk 544 32 =
      StrongPackedBucketN12A3AlignedShard004.missing544_576 := by decide
  have h576_608 : maskChunk 576 32 =
      StrongPackedBucketN12A3AlignedShard004.missing576_608 := by decide
  have h608_640 : maskChunk 608 32 =
      StrongPackedBucketN12A3AlignedShard004.missing608_640 := by decide
  have h512_576 : maskChunk 512 64 =
      StrongPackedBucketN12A3AlignedShard004.missing512_576 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h512_544, h544_576]
    rfl
  have h576_640 : maskChunk 576 64 =
      StrongPackedBucketN12A3AlignedShard004.missing576_640 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h576_608, h608_640]
    rfl
  have h512_640 : maskChunk 512 128 =
      StrongPackedBucketN12A3AlignedShard004.missing512_640 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h512_576, h576_640]
    rfl
  exact h512_640

private theorem shardMask5 : maskChunk 640 128 =
    StrongPackedBucketN12A3AlignedShard005.missing := by
  have h640_672 : maskChunk 640 32 =
      StrongPackedBucketN12A3AlignedShard005.missing640_672 := by decide
  have h672_704 : maskChunk 672 32 =
      StrongPackedBucketN12A3AlignedShard005.missing672_704 := by decide
  have h704_736 : maskChunk 704 32 =
      StrongPackedBucketN12A3AlignedShard005.missing704_736 := by decide
  have h736_768 : maskChunk 736 32 =
      StrongPackedBucketN12A3AlignedShard005.missing736_768 := by decide
  have h640_704 : maskChunk 640 64 =
      StrongPackedBucketN12A3AlignedShard005.missing640_704 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h640_672, h672_704]
    rfl
  have h704_768 : maskChunk 704 64 =
      StrongPackedBucketN12A3AlignedShard005.missing704_768 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h704_736, h736_768]
    rfl
  have h640_768 : maskChunk 640 128 =
      StrongPackedBucketN12A3AlignedShard005.missing640_768 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h640_704, h704_768]
    rfl
  exact h640_768

private theorem shardMask6 : maskChunk 768 128 =
    StrongPackedBucketN12A3AlignedShard006.missing := by
  have h768_800 : maskChunk 768 32 =
      StrongPackedBucketN12A3AlignedShard006.missing768_800 := by decide
  have h800_832 : maskChunk 800 32 =
      StrongPackedBucketN12A3AlignedShard006.missing800_832 := by decide
  have h832_864 : maskChunk 832 32 =
      StrongPackedBucketN12A3AlignedShard006.missing832_864 := by decide
  have h864_896 : maskChunk 864 32 =
      StrongPackedBucketN12A3AlignedShard006.missing864_896 := by decide
  have h768_832 : maskChunk 768 64 =
      StrongPackedBucketN12A3AlignedShard006.missing768_832 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h768_800, h800_832]
    rfl
  have h832_896 : maskChunk 832 64 =
      StrongPackedBucketN12A3AlignedShard006.missing832_896 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h832_864, h864_896]
    rfl
  have h768_896 : maskChunk 768 128 =
      StrongPackedBucketN12A3AlignedShard006.missing768_896 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h768_832, h832_896]
    rfl
  exact h768_896

private theorem shardMask7 : maskChunk 896 128 =
    StrongPackedBucketN12A3AlignedShard007.missing := by
  have h896_928 : maskChunk 896 32 =
      StrongPackedBucketN12A3AlignedShard007.missing896_928 := by decide
  have h928_960 : maskChunk 928 32 =
      StrongPackedBucketN12A3AlignedShard007.missing928_960 := by decide
  have h960_992 : maskChunk 960 32 =
      StrongPackedBucketN12A3AlignedShard007.missing960_992 := by decide
  have h992_1024 : maskChunk 992 32 =
      StrongPackedBucketN12A3AlignedShard007.missing992_1024 := by decide
  have h896_960 : maskChunk 896 64 =
      StrongPackedBucketN12A3AlignedShard007.missing896_960 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h896_928, h928_960]
    rfl
  have h960_1024 : maskChunk 960 64 =
      StrongPackedBucketN12A3AlignedShard007.missing960_1024 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h960_992, h992_1024]
    rfl
  have h896_1024 : maskChunk 896 128 =
      StrongPackedBucketN12A3AlignedShard007.missing896_1024 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h896_960, h960_1024]
    rfl
  exact h896_1024

private theorem shardMask8 : maskChunk 1024 128 =
    StrongPackedBucketN12A3AlignedShard008.missing := by
  have h1024_1056 : maskChunk 1024 32 =
      StrongPackedBucketN12A3AlignedShard008.missing1024_1056 := by decide
  have h1056_1088 : maskChunk 1056 32 =
      StrongPackedBucketN12A3AlignedShard008.missing1056_1088 := by decide
  have h1088_1120 : maskChunk 1088 32 =
      StrongPackedBucketN12A3AlignedShard008.missing1088_1120 := by decide
  have h1120_1152 : maskChunk 1120 32 =
      StrongPackedBucketN12A3AlignedShard008.missing1120_1152 := by decide
  have h1024_1088 : maskChunk 1024 64 =
      StrongPackedBucketN12A3AlignedShard008.missing1024_1088 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1024_1056, h1056_1088]
    rfl
  have h1088_1152 : maskChunk 1088 64 =
      StrongPackedBucketN12A3AlignedShard008.missing1088_1152 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1088_1120, h1120_1152]
    rfl
  have h1024_1152 : maskChunk 1024 128 =
      StrongPackedBucketN12A3AlignedShard008.missing1024_1152 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1024_1088, h1088_1152]
    rfl
  exact h1024_1152

private theorem shardMask9 : maskChunk 1152 128 =
    StrongPackedBucketN12A3AlignedShard009.missing := by
  have h1152_1184 : maskChunk 1152 32 =
      StrongPackedBucketN12A3AlignedShard009.missing1152_1184 := by decide
  have h1184_1216 : maskChunk 1184 32 =
      StrongPackedBucketN12A3AlignedShard009.missing1184_1216 := by decide
  have h1216_1248 : maskChunk 1216 32 =
      StrongPackedBucketN12A3AlignedShard009.missing1216_1248 := by decide
  have h1248_1280 : maskChunk 1248 32 =
      StrongPackedBucketN12A3AlignedShard009.missing1248_1280 := by decide
  have h1152_1216 : maskChunk 1152 64 =
      StrongPackedBucketN12A3AlignedShard009.missing1152_1216 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1152_1184, h1184_1216]
    rfl
  have h1216_1280 : maskChunk 1216 64 =
      StrongPackedBucketN12A3AlignedShard009.missing1216_1280 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1216_1248, h1248_1280]
    rfl
  have h1152_1280 : maskChunk 1152 128 =
      StrongPackedBucketN12A3AlignedShard009.missing1152_1280 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1152_1216, h1216_1280]
    rfl
  exact h1152_1280

private theorem shardMask10 : maskChunk 1280 128 =
    StrongPackedBucketN12A3AlignedShard010.missing := by
  have h1280_1312 : maskChunk 1280 32 =
      StrongPackedBucketN12A3AlignedShard010.missing1280_1312 := by decide
  have h1312_1344 : maskChunk 1312 32 =
      StrongPackedBucketN12A3AlignedShard010.missing1312_1344 := by decide
  have h1344_1376 : maskChunk 1344 32 =
      StrongPackedBucketN12A3AlignedShard010.missing1344_1376 := by decide
  have h1376_1408 : maskChunk 1376 32 =
      StrongPackedBucketN12A3AlignedShard010.missing1376_1408 := by decide
  have h1280_1344 : maskChunk 1280 64 =
      StrongPackedBucketN12A3AlignedShard010.missing1280_1344 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1280_1312, h1312_1344]
    rfl
  have h1344_1408 : maskChunk 1344 64 =
      StrongPackedBucketN12A3AlignedShard010.missing1344_1408 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1344_1376, h1376_1408]
    rfl
  have h1280_1408 : maskChunk 1280 128 =
      StrongPackedBucketN12A3AlignedShard010.missing1280_1408 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1280_1344, h1344_1408]
    rfl
  exact h1280_1408

private theorem shardMask11 : maskChunk 1408 128 =
    StrongPackedBucketN12A3AlignedShard011.missing := by
  have h1408_1440 : maskChunk 1408 32 =
      StrongPackedBucketN12A3AlignedShard011.missing1408_1440 := by decide
  have h1440_1472 : maskChunk 1440 32 =
      StrongPackedBucketN12A3AlignedShard011.missing1440_1472 := by decide
  have h1472_1504 : maskChunk 1472 32 =
      StrongPackedBucketN12A3AlignedShard011.missing1472_1504 := by decide
  have h1504_1536 : maskChunk 1504 32 =
      StrongPackedBucketN12A3AlignedShard011.missing1504_1536 := by decide
  have h1408_1472 : maskChunk 1408 64 =
      StrongPackedBucketN12A3AlignedShard011.missing1408_1472 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1408_1440, h1440_1472]
    rfl
  have h1472_1536 : maskChunk 1472 64 =
      StrongPackedBucketN12A3AlignedShard011.missing1472_1536 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1472_1504, h1504_1536]
    rfl
  have h1408_1536 : maskChunk 1408 128 =
      StrongPackedBucketN12A3AlignedShard011.missing1408_1536 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1408_1472, h1472_1536]
    rfl
  exact h1408_1536

private theorem shardMask12 : maskChunk 1536 128 =
    StrongPackedBucketN12A3AlignedShard012.missing := by
  have h1536_1568 : maskChunk 1536 32 =
      StrongPackedBucketN12A3AlignedShard012.missing1536_1568 := by decide
  have h1568_1600 : maskChunk 1568 32 =
      StrongPackedBucketN12A3AlignedShard012.missing1568_1600 := by decide
  have h1600_1632 : maskChunk 1600 32 =
      StrongPackedBucketN12A3AlignedShard012.missing1600_1632 := by decide
  have h1632_1664 : maskChunk 1632 32 =
      StrongPackedBucketN12A3AlignedShard012.missing1632_1664 := by decide
  have h1536_1600 : maskChunk 1536 64 =
      StrongPackedBucketN12A3AlignedShard012.missing1536_1600 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1536_1568, h1568_1600]
    rfl
  have h1600_1664 : maskChunk 1600 64 =
      StrongPackedBucketN12A3AlignedShard012.missing1600_1664 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1600_1632, h1632_1664]
    rfl
  have h1536_1664 : maskChunk 1536 128 =
      StrongPackedBucketN12A3AlignedShard012.missing1536_1664 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1536_1600, h1600_1664]
    rfl
  exact h1536_1664

private theorem shardMask13 : maskChunk 1664 128 =
    StrongPackedBucketN12A3AlignedShard013.missing := by
  have h1664_1696 : maskChunk 1664 32 =
      StrongPackedBucketN12A3AlignedShard013.missing1664_1696 := by decide
  have h1696_1728 : maskChunk 1696 32 =
      StrongPackedBucketN12A3AlignedShard013.missing1696_1728 := by decide
  have h1728_1760 : maskChunk 1728 32 =
      StrongPackedBucketN12A3AlignedShard013.missing1728_1760 := by decide
  have h1760_1792 : maskChunk 1760 32 =
      StrongPackedBucketN12A3AlignedShard013.missing1760_1792 := by decide
  have h1664_1728 : maskChunk 1664 64 =
      StrongPackedBucketN12A3AlignedShard013.missing1664_1728 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1664_1696, h1696_1728]
    rfl
  have h1728_1792 : maskChunk 1728 64 =
      StrongPackedBucketN12A3AlignedShard013.missing1728_1792 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1728_1760, h1760_1792]
    rfl
  have h1664_1792 : maskChunk 1664 128 =
      StrongPackedBucketN12A3AlignedShard013.missing1664_1792 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1664_1728, h1728_1792]
    rfl
  exact h1664_1792

private theorem shardMask14 : maskChunk 1792 128 =
    StrongPackedBucketN12A3AlignedShard014.missing := by
  have h1792_1824 : maskChunk 1792 32 =
      StrongPackedBucketN12A3AlignedShard014.missing1792_1824 := by decide
  have h1824_1856 : maskChunk 1824 32 =
      StrongPackedBucketN12A3AlignedShard014.missing1824_1856 := by decide
  have h1856_1888 : maskChunk 1856 32 =
      StrongPackedBucketN12A3AlignedShard014.missing1856_1888 := by decide
  have h1888_1920 : maskChunk 1888 32 =
      StrongPackedBucketN12A3AlignedShard014.missing1888_1920 := by decide
  have h1792_1856 : maskChunk 1792 64 =
      StrongPackedBucketN12A3AlignedShard014.missing1792_1856 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1792_1824, h1824_1856]
    rfl
  have h1856_1920 : maskChunk 1856 64 =
      StrongPackedBucketN12A3AlignedShard014.missing1856_1920 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1856_1888, h1888_1920]
    rfl
  have h1792_1920 : maskChunk 1792 128 =
      StrongPackedBucketN12A3AlignedShard014.missing1792_1920 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1792_1856, h1856_1920]
    rfl
  exact h1792_1920

private theorem shardMask15 : maskChunk 1920 128 =
    StrongPackedBucketN12A3AlignedShard015.missing := by
  have h1920_1952 : maskChunk 1920 32 =
      StrongPackedBucketN12A3AlignedShard015.missing1920_1952 := by decide
  have h1952_1984 : maskChunk 1952 32 =
      StrongPackedBucketN12A3AlignedShard015.missing1952_1984 := by decide
  have h1984_2016 : maskChunk 1984 32 =
      StrongPackedBucketN12A3AlignedShard015.missing1984_2016 := by decide
  have h2016_2048 : maskChunk 2016 32 =
      StrongPackedBucketN12A3AlignedShard015.missing2016_2048 := by decide
  have h1920_1984 : maskChunk 1920 64 =
      StrongPackedBucketN12A3AlignedShard015.missing1920_1984 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1920_1952, h1952_1984]
    rfl
  have h1984_2048 : maskChunk 1984 64 =
      StrongPackedBucketN12A3AlignedShard015.missing1984_2048 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1984_2016, h2016_2048]
    rfl
  have h1920_2048 : maskChunk 1920 128 =
      StrongPackedBucketN12A3AlignedShard015.missing1920_2048 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1920_1984, h1984_2048]
    rfl
  exact h1920_2048

private theorem shardMask16 : maskChunk 2048 128 =
    StrongPackedBucketN12A3AlignedShard016.missing := by
  have h2048_2080 : maskChunk 2048 32 =
      StrongPackedBucketN12A3AlignedShard016.missing2048_2080 := by decide
  have h2080_2112 : maskChunk 2080 32 =
      StrongPackedBucketN12A3AlignedShard016.missing2080_2112 := by decide
  have h2112_2144 : maskChunk 2112 32 =
      StrongPackedBucketN12A3AlignedShard016.missing2112_2144 := by decide
  have h2144_2176 : maskChunk 2144 32 =
      StrongPackedBucketN12A3AlignedShard016.missing2144_2176 := by decide
  have h2048_2112 : maskChunk 2048 64 =
      StrongPackedBucketN12A3AlignedShard016.missing2048_2112 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2048_2080, h2080_2112]
    rfl
  have h2112_2176 : maskChunk 2112 64 =
      StrongPackedBucketN12A3AlignedShard016.missing2112_2176 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2112_2144, h2144_2176]
    rfl
  have h2048_2176 : maskChunk 2048 128 =
      StrongPackedBucketN12A3AlignedShard016.missing2048_2176 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2048_2112, h2112_2176]
    rfl
  exact h2048_2176

private theorem shardMask17 : maskChunk 2176 128 =
    StrongPackedBucketN12A3AlignedShard017.missing := by
  have h2176_2208 : maskChunk 2176 32 =
      StrongPackedBucketN12A3AlignedShard017.missing2176_2208 := by decide
  have h2208_2240 : maskChunk 2208 32 =
      StrongPackedBucketN12A3AlignedShard017.missing2208_2240 := by decide
  have h2240_2272 : maskChunk 2240 32 =
      StrongPackedBucketN12A3AlignedShard017.missing2240_2272 := by decide
  have h2272_2304 : maskChunk 2272 32 =
      StrongPackedBucketN12A3AlignedShard017.missing2272_2304 := by decide
  have h2176_2240 : maskChunk 2176 64 =
      StrongPackedBucketN12A3AlignedShard017.missing2176_2240 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2176_2208, h2208_2240]
    rfl
  have h2240_2304 : maskChunk 2240 64 =
      StrongPackedBucketN12A3AlignedShard017.missing2240_2304 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2240_2272, h2272_2304]
    rfl
  have h2176_2304 : maskChunk 2176 128 =
      StrongPackedBucketN12A3AlignedShard017.missing2176_2304 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2176_2240, h2240_2304]
    rfl
  exact h2176_2304

private theorem shardMask18 : maskChunk 2304 128 =
    StrongPackedBucketN12A3AlignedShard018.missing := by
  have h2304_2336 : maskChunk 2304 32 =
      StrongPackedBucketN12A3AlignedShard018.missing2304_2336 := by decide
  have h2336_2368 : maskChunk 2336 32 =
      StrongPackedBucketN12A3AlignedShard018.missing2336_2368 := by decide
  have h2368_2400 : maskChunk 2368 32 =
      StrongPackedBucketN12A3AlignedShard018.missing2368_2400 := by decide
  have h2400_2432 : maskChunk 2400 32 =
      StrongPackedBucketN12A3AlignedShard018.missing2400_2432 := by decide
  have h2304_2368 : maskChunk 2304 64 =
      StrongPackedBucketN12A3AlignedShard018.missing2304_2368 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2304_2336, h2336_2368]
    rfl
  have h2368_2432 : maskChunk 2368 64 =
      StrongPackedBucketN12A3AlignedShard018.missing2368_2432 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2368_2400, h2400_2432]
    rfl
  have h2304_2432 : maskChunk 2304 128 =
      StrongPackedBucketN12A3AlignedShard018.missing2304_2432 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2304_2368, h2368_2432]
    rfl
  exact h2304_2432

private theorem shardMask19 : maskChunk 2432 128 =
    StrongPackedBucketN12A3AlignedShard019.missing := by
  have h2432_2464 : maskChunk 2432 32 =
      StrongPackedBucketN12A3AlignedShard019.missing2432_2464 := by decide
  have h2464_2496 : maskChunk 2464 32 =
      StrongPackedBucketN12A3AlignedShard019.missing2464_2496 := by decide
  have h2496_2528 : maskChunk 2496 32 =
      StrongPackedBucketN12A3AlignedShard019.missing2496_2528 := by decide
  have h2528_2560 : maskChunk 2528 32 =
      StrongPackedBucketN12A3AlignedShard019.missing2528_2560 := by decide
  have h2432_2496 : maskChunk 2432 64 =
      StrongPackedBucketN12A3AlignedShard019.missing2432_2496 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2432_2464, h2464_2496]
    rfl
  have h2496_2560 : maskChunk 2496 64 =
      StrongPackedBucketN12A3AlignedShard019.missing2496_2560 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2496_2528, h2528_2560]
    rfl
  have h2432_2560 : maskChunk 2432 128 =
      StrongPackedBucketN12A3AlignedShard019.missing2432_2560 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2432_2496, h2496_2560]
    rfl
  exact h2432_2560

private theorem shardMask20 : maskChunk 2560 128 =
    StrongPackedBucketN12A3AlignedShard020.missing := by
  have h2560_2592 : maskChunk 2560 32 =
      StrongPackedBucketN12A3AlignedShard020.missing2560_2592 := by decide
  have h2592_2624 : maskChunk 2592 32 =
      StrongPackedBucketN12A3AlignedShard020.missing2592_2624 := by decide
  have h2624_2656 : maskChunk 2624 32 =
      StrongPackedBucketN12A3AlignedShard020.missing2624_2656 := by decide
  have h2656_2688 : maskChunk 2656 32 =
      StrongPackedBucketN12A3AlignedShard020.missing2656_2688 := by decide
  have h2560_2624 : maskChunk 2560 64 =
      StrongPackedBucketN12A3AlignedShard020.missing2560_2624 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2560_2592, h2592_2624]
    rfl
  have h2624_2688 : maskChunk 2624 64 =
      StrongPackedBucketN12A3AlignedShard020.missing2624_2688 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2624_2656, h2656_2688]
    rfl
  have h2560_2688 : maskChunk 2560 128 =
      StrongPackedBucketN12A3AlignedShard020.missing2560_2688 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2560_2624, h2624_2688]
    rfl
  exact h2560_2688

private theorem shardMask21 : maskChunk 2688 128 =
    StrongPackedBucketN12A3AlignedShard021.missing := by
  have h2688_2720 : maskChunk 2688 32 =
      StrongPackedBucketN12A3AlignedShard021.missing2688_2720 := by decide
  have h2720_2752 : maskChunk 2720 32 =
      StrongPackedBucketN12A3AlignedShard021.missing2720_2752 := by decide
  have h2752_2784 : maskChunk 2752 32 =
      StrongPackedBucketN12A3AlignedShard021.missing2752_2784 := by decide
  have h2784_2816 : maskChunk 2784 32 =
      StrongPackedBucketN12A3AlignedShard021.missing2784_2816 := by decide
  have h2688_2752 : maskChunk 2688 64 =
      StrongPackedBucketN12A3AlignedShard021.missing2688_2752 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2688_2720, h2720_2752]
    rfl
  have h2752_2816 : maskChunk 2752 64 =
      StrongPackedBucketN12A3AlignedShard021.missing2752_2816 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2752_2784, h2784_2816]
    rfl
  have h2688_2816 : maskChunk 2688 128 =
      StrongPackedBucketN12A3AlignedShard021.missing2688_2816 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2688_2752, h2752_2816]
    rfl
  exact h2688_2816

private theorem shardMask22 : maskChunk 2816 128 =
    StrongPackedBucketN12A3AlignedShard022.missing := by
  have h2816_2848 : maskChunk 2816 32 =
      StrongPackedBucketN12A3AlignedShard022.missing2816_2848 := by decide
  have h2848_2880 : maskChunk 2848 32 =
      StrongPackedBucketN12A3AlignedShard022.missing2848_2880 := by decide
  have h2880_2912 : maskChunk 2880 32 =
      StrongPackedBucketN12A3AlignedShard022.missing2880_2912 := by decide
  have h2912_2944 : maskChunk 2912 32 =
      StrongPackedBucketN12A3AlignedShard022.missing2912_2944 := by decide
  have h2816_2880 : maskChunk 2816 64 =
      StrongPackedBucketN12A3AlignedShard022.missing2816_2880 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2816_2848, h2848_2880]
    rfl
  have h2880_2944 : maskChunk 2880 64 =
      StrongPackedBucketN12A3AlignedShard022.missing2880_2944 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2880_2912, h2912_2944]
    rfl
  have h2816_2944 : maskChunk 2816 128 =
      StrongPackedBucketN12A3AlignedShard022.missing2816_2944 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2816_2880, h2880_2944]
    rfl
  exact h2816_2944

private theorem shardMask23 : maskChunk 2944 128 =
    StrongPackedBucketN12A3AlignedShard023.missing := by
  have h2944_2976 : maskChunk 2944 32 =
      StrongPackedBucketN12A3AlignedShard023.missing2944_2976 := by decide
  have h2976_3008 : maskChunk 2976 32 =
      StrongPackedBucketN12A3AlignedShard023.missing2976_3008 := by decide
  have h3008_3040 : maskChunk 3008 32 =
      StrongPackedBucketN12A3AlignedShard023.missing3008_3040 := by decide
  have h3040_3072 : maskChunk 3040 32 =
      StrongPackedBucketN12A3AlignedShard023.missing3040_3072 := by decide
  have h2944_3008 : maskChunk 2944 64 =
      StrongPackedBucketN12A3AlignedShard023.missing2944_3008 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2944_2976, h2976_3008]
    rfl
  have h3008_3072 : maskChunk 3008 64 =
      StrongPackedBucketN12A3AlignedShard023.missing3008_3072 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3008_3040, h3040_3072]
    rfl
  have h2944_3072 : maskChunk 2944 128 =
      StrongPackedBucketN12A3AlignedShard023.missing2944_3072 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2944_3008, h3008_3072]
    rfl
  exact h2944_3072

private theorem shardMask24 : maskChunk 3072 128 =
    StrongPackedBucketN12A3AlignedShard024.missing := by
  have h3072_3104 : maskChunk 3072 32 =
      StrongPackedBucketN12A3AlignedShard024.missing3072_3104 := by decide
  have h3104_3136 : maskChunk 3104 32 =
      StrongPackedBucketN12A3AlignedShard024.missing3104_3136 := by decide
  have h3136_3168 : maskChunk 3136 32 =
      StrongPackedBucketN12A3AlignedShard024.missing3136_3168 := by decide
  have h3168_3200 : maskChunk 3168 32 =
      StrongPackedBucketN12A3AlignedShard024.missing3168_3200 := by decide
  have h3072_3136 : maskChunk 3072 64 =
      StrongPackedBucketN12A3AlignedShard024.missing3072_3136 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3072_3104, h3104_3136]
    rfl
  have h3136_3200 : maskChunk 3136 64 =
      StrongPackedBucketN12A3AlignedShard024.missing3136_3200 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3136_3168, h3168_3200]
    rfl
  have h3072_3200 : maskChunk 3072 128 =
      StrongPackedBucketN12A3AlignedShard024.missing3072_3200 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3072_3136, h3136_3200]
    rfl
  exact h3072_3200

private theorem shardMask25 : maskChunk 3200 128 =
    StrongPackedBucketN12A3AlignedShard025.missing := by
  have h3200_3232 : maskChunk 3200 32 =
      StrongPackedBucketN12A3AlignedShard025.missing3200_3232 := by decide
  have h3232_3264 : maskChunk 3232 32 =
      StrongPackedBucketN12A3AlignedShard025.missing3232_3264 := by decide
  have h3264_3296 : maskChunk 3264 32 =
      StrongPackedBucketN12A3AlignedShard025.missing3264_3296 := by decide
  have h3296_3328 : maskChunk 3296 32 =
      StrongPackedBucketN12A3AlignedShard025.missing3296_3328 := by decide
  have h3200_3264 : maskChunk 3200 64 =
      StrongPackedBucketN12A3AlignedShard025.missing3200_3264 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3200_3232, h3232_3264]
    rfl
  have h3264_3328 : maskChunk 3264 64 =
      StrongPackedBucketN12A3AlignedShard025.missing3264_3328 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3264_3296, h3296_3328]
    rfl
  have h3200_3328 : maskChunk 3200 128 =
      StrongPackedBucketN12A3AlignedShard025.missing3200_3328 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3200_3264, h3264_3328]
    rfl
  exact h3200_3328

private theorem shardMask26 : maskChunk 3328 128 =
    StrongPackedBucketN12A3AlignedShard026.missing := by
  have h3328_3360 : maskChunk 3328 32 =
      StrongPackedBucketN12A3AlignedShard026.missing3328_3360 := by decide
  have h3360_3392 : maskChunk 3360 32 =
      StrongPackedBucketN12A3AlignedShard026.missing3360_3392 := by decide
  have h3392_3424 : maskChunk 3392 32 =
      StrongPackedBucketN12A3AlignedShard026.missing3392_3424 := by decide
  have h3424_3456 : maskChunk 3424 32 =
      StrongPackedBucketN12A3AlignedShard026.missing3424_3456 := by decide
  have h3328_3392 : maskChunk 3328 64 =
      StrongPackedBucketN12A3AlignedShard026.missing3328_3392 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3328_3360, h3360_3392]
    rfl
  have h3392_3456 : maskChunk 3392 64 =
      StrongPackedBucketN12A3AlignedShard026.missing3392_3456 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3392_3424, h3424_3456]
    rfl
  have h3328_3456 : maskChunk 3328 128 =
      StrongPackedBucketN12A3AlignedShard026.missing3328_3456 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3328_3392, h3392_3456]
    rfl
  exact h3328_3456

private theorem shardMask27 : maskChunk 3456 128 =
    StrongPackedBucketN12A3AlignedShard027.missing := by
  have h3456_3488 : maskChunk 3456 32 =
      StrongPackedBucketN12A3AlignedShard027.missing3456_3488 := by decide
  have h3488_3520 : maskChunk 3488 32 =
      StrongPackedBucketN12A3AlignedShard027.missing3488_3520 := by decide
  have h3520_3552 : maskChunk 3520 32 =
      StrongPackedBucketN12A3AlignedShard027.missing3520_3552 := by decide
  have h3552_3584 : maskChunk 3552 32 =
      StrongPackedBucketN12A3AlignedShard027.missing3552_3584 := by decide
  have h3456_3520 : maskChunk 3456 64 =
      StrongPackedBucketN12A3AlignedShard027.missing3456_3520 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3456_3488, h3488_3520]
    rfl
  have h3520_3584 : maskChunk 3520 64 =
      StrongPackedBucketN12A3AlignedShard027.missing3520_3584 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3520_3552, h3552_3584]
    rfl
  have h3456_3584 : maskChunk 3456 128 =
      StrongPackedBucketN12A3AlignedShard027.missing3456_3584 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3456_3520, h3520_3584]
    rfl
  exact h3456_3584

private theorem shardMask28 : maskChunk 3584 128 =
    StrongPackedBucketN12A3AlignedShard028.missing := by
  have h3584_3616 : maskChunk 3584 32 =
      StrongPackedBucketN12A3AlignedShard028.missing3584_3616 := by decide
  have h3616_3648 : maskChunk 3616 32 =
      StrongPackedBucketN12A3AlignedShard028.missing3616_3648 := by decide
  have h3648_3680 : maskChunk 3648 32 =
      StrongPackedBucketN12A3AlignedShard028.missing3648_3680 := by decide
  have h3680_3712 : maskChunk 3680 32 =
      StrongPackedBucketN12A3AlignedShard028.missing3680_3712 := by decide
  have h3584_3648 : maskChunk 3584 64 =
      StrongPackedBucketN12A3AlignedShard028.missing3584_3648 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3584_3616, h3616_3648]
    rfl
  have h3648_3712 : maskChunk 3648 64 =
      StrongPackedBucketN12A3AlignedShard028.missing3648_3712 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3648_3680, h3680_3712]
    rfl
  have h3584_3712 : maskChunk 3584 128 =
      StrongPackedBucketN12A3AlignedShard028.missing3584_3712 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3584_3648, h3648_3712]
    rfl
  exact h3584_3712

private theorem shardMask29 : maskChunk 3712 128 =
    StrongPackedBucketN12A3AlignedShard029.missing := by
  have h3712_3744 : maskChunk 3712 32 =
      StrongPackedBucketN12A3AlignedShard029.missing3712_3744 := by decide
  have h3744_3776 : maskChunk 3744 32 =
      StrongPackedBucketN12A3AlignedShard029.missing3744_3776 := by decide
  have h3776_3808 : maskChunk 3776 32 =
      StrongPackedBucketN12A3AlignedShard029.missing3776_3808 := by decide
  have h3808_3840 : maskChunk 3808 32 =
      StrongPackedBucketN12A3AlignedShard029.missing3808_3840 := by decide
  have h3712_3776 : maskChunk 3712 64 =
      StrongPackedBucketN12A3AlignedShard029.missing3712_3776 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3712_3744, h3744_3776]
    rfl
  have h3776_3840 : maskChunk 3776 64 =
      StrongPackedBucketN12A3AlignedShard029.missing3776_3840 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3776_3808, h3808_3840]
    rfl
  have h3712_3840 : maskChunk 3712 128 =
      StrongPackedBucketN12A3AlignedShard029.missing3712_3840 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3712_3776, h3776_3840]
    rfl
  exact h3712_3840

private theorem shardMask30 : maskChunk 3840 128 =
    StrongPackedBucketN12A3AlignedShard030.missing := by
  have h3840_3872 : maskChunk 3840 32 =
      StrongPackedBucketN12A3AlignedShard030.missing3840_3872 := by decide
  have h3872_3904 : maskChunk 3872 32 =
      StrongPackedBucketN12A3AlignedShard030.missing3872_3904 := by decide
  have h3904_3936 : maskChunk 3904 32 =
      StrongPackedBucketN12A3AlignedShard030.missing3904_3936 := by decide
  have h3936_3968 : maskChunk 3936 32 =
      StrongPackedBucketN12A3AlignedShard030.missing3936_3968 := by decide
  have h3840_3904 : maskChunk 3840 64 =
      StrongPackedBucketN12A3AlignedShard030.missing3840_3904 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3840_3872, h3872_3904]
    rfl
  have h3904_3968 : maskChunk 3904 64 =
      StrongPackedBucketN12A3AlignedShard030.missing3904_3968 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3904_3936, h3936_3968]
    rfl
  have h3840_3968 : maskChunk 3840 128 =
      StrongPackedBucketN12A3AlignedShard030.missing3840_3968 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3840_3904, h3904_3968]
    rfl
  exact h3840_3968

private theorem shardMask31 : maskChunk 3968 128 =
    StrongPackedBucketN12A3AlignedShard031.missing := by
  have h3968_4000 : maskChunk 3968 32 =
      StrongPackedBucketN12A3AlignedShard031.missing3968_4000 := by decide
  have h4000_4032 : maskChunk 4000 32 =
      StrongPackedBucketN12A3AlignedShard031.missing4000_4032 := by decide
  have h4032_4064 : maskChunk 4032 32 =
      StrongPackedBucketN12A3AlignedShard031.missing4032_4064 := by decide
  have h4064_4096 : maskChunk 4064 32 =
      StrongPackedBucketN12A3AlignedShard031.missing4064_4096 := by decide
  have h3968_4032 : maskChunk 3968 64 =
      StrongPackedBucketN12A3AlignedShard031.missing3968_4032 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3968_4000, h4000_4032]
    rfl
  have h4032_4096 : maskChunk 4032 64 =
      StrongPackedBucketN12A3AlignedShard031.missing4032_4096 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4032_4064, h4064_4096]
    rfl
  have h3968_4096 : maskChunk 3968 128 =
      StrongPackedBucketN12A3AlignedShard031.missing3968_4096 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3968_4032, h4032_4096]
    rfl
  exact h3968_4096

private theorem shardMask32 : maskChunk 4096 128 =
    StrongPackedBucketN12A3AlignedShard032.missing := by
  have h4096_4128 : maskChunk 4096 32 =
      StrongPackedBucketN12A3AlignedShard032.missing4096_4128 := by decide
  have h4128_4160 : maskChunk 4128 32 =
      StrongPackedBucketN12A3AlignedShard032.missing4128_4160 := by decide
  have h4160_4192 : maskChunk 4160 32 =
      StrongPackedBucketN12A3AlignedShard032.missing4160_4192 := by decide
  have h4192_4224 : maskChunk 4192 32 =
      StrongPackedBucketN12A3AlignedShard032.missing4192_4224 := by decide
  have h4096_4160 : maskChunk 4096 64 =
      StrongPackedBucketN12A3AlignedShard032.missing4096_4160 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4096_4128, h4128_4160]
    rfl
  have h4160_4224 : maskChunk 4160 64 =
      StrongPackedBucketN12A3AlignedShard032.missing4160_4224 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4160_4192, h4192_4224]
    rfl
  have h4096_4224 : maskChunk 4096 128 =
      StrongPackedBucketN12A3AlignedShard032.missing4096_4224 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h4096_4160, h4160_4224]
    rfl
  exact h4096_4224

private theorem shardMask33 : maskChunk 4224 128 =
    StrongPackedBucketN12A3AlignedShard033.missing := by
  have h4224_4256 : maskChunk 4224 32 =
      StrongPackedBucketN12A3AlignedShard033.missing4224_4256 := by decide
  have h4256_4288 : maskChunk 4256 32 =
      StrongPackedBucketN12A3AlignedShard033.missing4256_4288 := by decide
  have h4288_4320 : maskChunk 4288 32 =
      StrongPackedBucketN12A3AlignedShard033.missing4288_4320 := by decide
  have h4320_4352 : maskChunk 4320 32 =
      StrongPackedBucketN12A3AlignedShard033.missing4320_4352 := by decide
  have h4224_4288 : maskChunk 4224 64 =
      StrongPackedBucketN12A3AlignedShard033.missing4224_4288 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4224_4256, h4256_4288]
    rfl
  have h4288_4352 : maskChunk 4288 64 =
      StrongPackedBucketN12A3AlignedShard033.missing4288_4352 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4288_4320, h4320_4352]
    rfl
  have h4224_4352 : maskChunk 4224 128 =
      StrongPackedBucketN12A3AlignedShard033.missing4224_4352 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h4224_4288, h4288_4352]
    rfl
  exact h4224_4352

private theorem shardMask34 : maskChunk 4352 128 =
    StrongPackedBucketN12A3AlignedShard034.missing := by
  have h4352_4384 : maskChunk 4352 32 =
      StrongPackedBucketN12A3AlignedShard034.missing4352_4384 := by decide
  have h4384_4416 : maskChunk 4384 32 =
      StrongPackedBucketN12A3AlignedShard034.missing4384_4416 := by decide
  have h4416_4448 : maskChunk 4416 32 =
      StrongPackedBucketN12A3AlignedShard034.missing4416_4448 := by decide
  have h4448_4480 : maskChunk 4448 32 =
      StrongPackedBucketN12A3AlignedShard034.missing4448_4480 := by decide
  have h4352_4416 : maskChunk 4352 64 =
      StrongPackedBucketN12A3AlignedShard034.missing4352_4416 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4352_4384, h4384_4416]
    rfl
  have h4416_4480 : maskChunk 4416 64 =
      StrongPackedBucketN12A3AlignedShard034.missing4416_4480 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4416_4448, h4448_4480]
    rfl
  have h4352_4480 : maskChunk 4352 128 =
      StrongPackedBucketN12A3AlignedShard034.missing4352_4480 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h4352_4416, h4416_4480]
    rfl
  exact h4352_4480

private theorem shardMask35 : maskChunk 4480 128 =
    StrongPackedBucketN12A3AlignedShard035.missing := by
  have h4480_4512 : maskChunk 4480 32 =
      StrongPackedBucketN12A3AlignedShard035.missing4480_4512 := by decide
  have h4512_4544 : maskChunk 4512 32 =
      StrongPackedBucketN12A3AlignedShard035.missing4512_4544 := by decide
  have h4544_4576 : maskChunk 4544 32 =
      StrongPackedBucketN12A3AlignedShard035.missing4544_4576 := by decide
  have h4576_4608 : maskChunk 4576 32 =
      StrongPackedBucketN12A3AlignedShard035.missing4576_4608 := by decide
  have h4480_4544 : maskChunk 4480 64 =
      StrongPackedBucketN12A3AlignedShard035.missing4480_4544 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4480_4512, h4512_4544]
    rfl
  have h4544_4608 : maskChunk 4544 64 =
      StrongPackedBucketN12A3AlignedShard035.missing4544_4608 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4544_4576, h4576_4608]
    rfl
  have h4480_4608 : maskChunk 4480 128 =
      StrongPackedBucketN12A3AlignedShard035.missing4480_4608 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h4480_4544, h4544_4608]
    rfl
  exact h4480_4608

private theorem shardMask36 : maskChunk 4608 128 =
    StrongPackedBucketN12A3AlignedShard036.missing := by
  have h4608_4640 : maskChunk 4608 32 =
      StrongPackedBucketN12A3AlignedShard036.missing4608_4640 := by decide
  have h4640_4672 : maskChunk 4640 32 =
      StrongPackedBucketN12A3AlignedShard036.missing4640_4672 := by decide
  have h4672_4704 : maskChunk 4672 32 =
      StrongPackedBucketN12A3AlignedShard036.missing4672_4704 := by decide
  have h4704_4736 : maskChunk 4704 32 =
      StrongPackedBucketN12A3AlignedShard036.missing4704_4736 := by decide
  have h4608_4672 : maskChunk 4608 64 =
      StrongPackedBucketN12A3AlignedShard036.missing4608_4672 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4608_4640, h4640_4672]
    rfl
  have h4672_4736 : maskChunk 4672 64 =
      StrongPackedBucketN12A3AlignedShard036.missing4672_4736 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4672_4704, h4704_4736]
    rfl
  have h4608_4736 : maskChunk 4608 128 =
      StrongPackedBucketN12A3AlignedShard036.missing4608_4736 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h4608_4672, h4672_4736]
    rfl
  exact h4608_4736

private theorem shardMask37 : maskChunk 4736 128 =
    StrongPackedBucketN12A3AlignedShard037.missing := by
  have h4736_4768 : maskChunk 4736 32 =
      StrongPackedBucketN12A3AlignedShard037.missing4736_4768 := by decide
  have h4768_4800 : maskChunk 4768 32 =
      StrongPackedBucketN12A3AlignedShard037.missing4768_4800 := by decide
  have h4800_4832 : maskChunk 4800 32 =
      StrongPackedBucketN12A3AlignedShard037.missing4800_4832 := by decide
  have h4832_4864 : maskChunk 4832 32 =
      StrongPackedBucketN12A3AlignedShard037.missing4832_4864 := by decide
  have h4736_4800 : maskChunk 4736 64 =
      StrongPackedBucketN12A3AlignedShard037.missing4736_4800 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4736_4768, h4768_4800]
    rfl
  have h4800_4864 : maskChunk 4800 64 =
      StrongPackedBucketN12A3AlignedShard037.missing4800_4864 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4800_4832, h4832_4864]
    rfl
  have h4736_4864 : maskChunk 4736 128 =
      StrongPackedBucketN12A3AlignedShard037.missing4736_4864 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h4736_4800, h4800_4864]
    rfl
  exact h4736_4864

private theorem shardMask38 : maskChunk 4864 128 =
    StrongPackedBucketN12A3AlignedShard038.missing := by
  have h4864_4896 : maskChunk 4864 32 =
      StrongPackedBucketN12A3AlignedShard038.missing4864_4896 := by decide
  have h4896_4928 : maskChunk 4896 32 =
      StrongPackedBucketN12A3AlignedShard038.missing4896_4928 := by decide
  have h4928_4960 : maskChunk 4928 32 =
      StrongPackedBucketN12A3AlignedShard038.missing4928_4960 := by decide
  have h4960_4992 : maskChunk 4960 32 =
      StrongPackedBucketN12A3AlignedShard038.missing4960_4992 := by decide
  have h4864_4928 : maskChunk 4864 64 =
      StrongPackedBucketN12A3AlignedShard038.missing4864_4928 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4864_4896, h4896_4928]
    rfl
  have h4928_4992 : maskChunk 4928 64 =
      StrongPackedBucketN12A3AlignedShard038.missing4928_4992 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4928_4960, h4960_4992]
    rfl
  have h4864_4992 : maskChunk 4864 128 =
      StrongPackedBucketN12A3AlignedShard038.missing4864_4992 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h4864_4928, h4928_4992]
    rfl
  exact h4864_4992

private theorem shardMask39 : maskChunk 4992 128 =
    StrongPackedBucketN12A3AlignedShard039.missing := by
  have h4992_5024 : maskChunk 4992 32 =
      StrongPackedBucketN12A3AlignedShard039.missing4992_5024 := by decide
  have h5024_5056 : maskChunk 5024 32 =
      StrongPackedBucketN12A3AlignedShard039.missing5024_5056 := by decide
  have h5056_5088 : maskChunk 5056 32 =
      StrongPackedBucketN12A3AlignedShard039.missing5056_5088 := by decide
  have h5088_5120 : maskChunk 5088 32 =
      StrongPackedBucketN12A3AlignedShard039.missing5088_5120 := by decide
  have h4992_5056 : maskChunk 4992 64 =
      StrongPackedBucketN12A3AlignedShard039.missing4992_5056 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4992_5024, h5024_5056]
    rfl
  have h5056_5120 : maskChunk 5056 64 =
      StrongPackedBucketN12A3AlignedShard039.missing5056_5120 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5056_5088, h5088_5120]
    rfl
  have h4992_5120 : maskChunk 4992 128 =
      StrongPackedBucketN12A3AlignedShard039.missing4992_5120 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h4992_5056, h5056_5120]
    rfl
  exact h4992_5120

private theorem shardMask40 : maskChunk 5120 128 =
    StrongPackedBucketN12A3AlignedShard040.missing := by
  have h5120_5152 : maskChunk 5120 32 =
      StrongPackedBucketN12A3AlignedShard040.missing5120_5152 := by decide
  have h5152_5184 : maskChunk 5152 32 =
      StrongPackedBucketN12A3AlignedShard040.missing5152_5184 := by decide
  have h5184_5216 : maskChunk 5184 32 =
      StrongPackedBucketN12A3AlignedShard040.missing5184_5216 := by decide
  have h5216_5248 : maskChunk 5216 32 =
      StrongPackedBucketN12A3AlignedShard040.missing5216_5248 := by decide
  have h5120_5184 : maskChunk 5120 64 =
      StrongPackedBucketN12A3AlignedShard040.missing5120_5184 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5120_5152, h5152_5184]
    rfl
  have h5184_5248 : maskChunk 5184 64 =
      StrongPackedBucketN12A3AlignedShard040.missing5184_5248 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5184_5216, h5216_5248]
    rfl
  have h5120_5248 : maskChunk 5120 128 =
      StrongPackedBucketN12A3AlignedShard040.missing5120_5248 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h5120_5184, h5184_5248]
    rfl
  exact h5120_5248

private theorem shardMask41 : maskChunk 5248 128 =
    StrongPackedBucketN12A3AlignedShard041.missing := by
  have h5248_5280 : maskChunk 5248 32 =
      StrongPackedBucketN12A3AlignedShard041.missing5248_5280 := by decide
  have h5280_5312 : maskChunk 5280 32 =
      StrongPackedBucketN12A3AlignedShard041.missing5280_5312 := by decide
  have h5312_5344 : maskChunk 5312 32 =
      StrongPackedBucketN12A3AlignedShard041.missing5312_5344 := by decide
  have h5344_5376 : maskChunk 5344 32 =
      StrongPackedBucketN12A3AlignedShard041.missing5344_5376 := by decide
  have h5248_5312 : maskChunk 5248 64 =
      StrongPackedBucketN12A3AlignedShard041.missing5248_5312 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5248_5280, h5280_5312]
    rfl
  have h5312_5376 : maskChunk 5312 64 =
      StrongPackedBucketN12A3AlignedShard041.missing5312_5376 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5312_5344, h5344_5376]
    rfl
  have h5248_5376 : maskChunk 5248 128 =
      StrongPackedBucketN12A3AlignedShard041.missing5248_5376 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h5248_5312, h5312_5376]
    rfl
  exact h5248_5376

private theorem shardMask42 : maskChunk 5376 128 =
    StrongPackedBucketN12A3AlignedShard042.missing := by
  have h5376_5408 : maskChunk 5376 32 =
      StrongPackedBucketN12A3AlignedShard042.missing5376_5408 := by decide
  have h5408_5440 : maskChunk 5408 32 =
      StrongPackedBucketN12A3AlignedShard042.missing5408_5440 := by decide
  have h5440_5472 : maskChunk 5440 32 =
      StrongPackedBucketN12A3AlignedShard042.missing5440_5472 := by decide
  have h5472_5504 : maskChunk 5472 32 =
      StrongPackedBucketN12A3AlignedShard042.missing5472_5504 := by decide
  have h5376_5440 : maskChunk 5376 64 =
      StrongPackedBucketN12A3AlignedShard042.missing5376_5440 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5376_5408, h5408_5440]
    rfl
  have h5440_5504 : maskChunk 5440 64 =
      StrongPackedBucketN12A3AlignedShard042.missing5440_5504 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5440_5472, h5472_5504]
    rfl
  have h5376_5504 : maskChunk 5376 128 =
      StrongPackedBucketN12A3AlignedShard042.missing5376_5504 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h5376_5440, h5440_5504]
    rfl
  exact h5376_5504

private theorem shardMask43 : maskChunk 5504 128 =
    StrongPackedBucketN12A3AlignedShard043.missing := by
  have h5504_5536 : maskChunk 5504 32 =
      StrongPackedBucketN12A3AlignedShard043.missing5504_5536 := by decide
  have h5536_5568 : maskChunk 5536 32 =
      StrongPackedBucketN12A3AlignedShard043.missing5536_5568 := by decide
  have h5568_5600 : maskChunk 5568 32 =
      StrongPackedBucketN12A3AlignedShard043.missing5568_5600 := by decide
  have h5600_5632 : maskChunk 5600 32 =
      StrongPackedBucketN12A3AlignedShard043.missing5600_5632 := by decide
  have h5504_5568 : maskChunk 5504 64 =
      StrongPackedBucketN12A3AlignedShard043.missing5504_5568 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5504_5536, h5536_5568]
    rfl
  have h5568_5632 : maskChunk 5568 64 =
      StrongPackedBucketN12A3AlignedShard043.missing5568_5632 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5568_5600, h5600_5632]
    rfl
  have h5504_5632 : maskChunk 5504 128 =
      StrongPackedBucketN12A3AlignedShard043.missing5504_5632 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h5504_5568, h5568_5632]
    rfl
  exact h5504_5632

private theorem shardMask44 : maskChunk 5632 128 =
    StrongPackedBucketN12A3AlignedShard044.missing := by
  have h5632_5664 : maskChunk 5632 32 =
      StrongPackedBucketN12A3AlignedShard044.missing5632_5664 := by decide
  have h5664_5696 : maskChunk 5664 32 =
      StrongPackedBucketN12A3AlignedShard044.missing5664_5696 := by decide
  have h5696_5728 : maskChunk 5696 32 =
      StrongPackedBucketN12A3AlignedShard044.missing5696_5728 := by decide
  have h5728_5760 : maskChunk 5728 32 =
      StrongPackedBucketN12A3AlignedShard044.missing5728_5760 := by decide
  have h5632_5696 : maskChunk 5632 64 =
      StrongPackedBucketN12A3AlignedShard044.missing5632_5696 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5632_5664, h5664_5696]
    rfl
  have h5696_5760 : maskChunk 5696 64 =
      StrongPackedBucketN12A3AlignedShard044.missing5696_5760 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5696_5728, h5728_5760]
    rfl
  have h5632_5760 : maskChunk 5632 128 =
      StrongPackedBucketN12A3AlignedShard044.missing5632_5760 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h5632_5696, h5696_5760]
    rfl
  exact h5632_5760

private theorem shardMask45 : maskChunk 5760 128 =
    StrongPackedBucketN12A3AlignedShard045.missing := by
  have h5760_5792 : maskChunk 5760 32 =
      StrongPackedBucketN12A3AlignedShard045.missing5760_5792 := by decide
  have h5792_5824 : maskChunk 5792 32 =
      StrongPackedBucketN12A3AlignedShard045.missing5792_5824 := by decide
  have h5824_5856 : maskChunk 5824 32 =
      StrongPackedBucketN12A3AlignedShard045.missing5824_5856 := by decide
  have h5856_5888 : maskChunk 5856 32 =
      StrongPackedBucketN12A3AlignedShard045.missing5856_5888 := by decide
  have h5760_5824 : maskChunk 5760 64 =
      StrongPackedBucketN12A3AlignedShard045.missing5760_5824 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5760_5792, h5792_5824]
    rfl
  have h5824_5888 : maskChunk 5824 64 =
      StrongPackedBucketN12A3AlignedShard045.missing5824_5888 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5824_5856, h5856_5888]
    rfl
  have h5760_5888 : maskChunk 5760 128 =
      StrongPackedBucketN12A3AlignedShard045.missing5760_5888 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h5760_5824, h5824_5888]
    rfl
  exact h5760_5888

private theorem shardMask46 : maskChunk 5888 128 =
    StrongPackedBucketN12A3AlignedShard046.missing := by
  have h5888_5920 : maskChunk 5888 32 =
      StrongPackedBucketN12A3AlignedShard046.missing5888_5920 := by decide
  have h5920_5952 : maskChunk 5920 32 =
      StrongPackedBucketN12A3AlignedShard046.missing5920_5952 := by decide
  have h5952_5984 : maskChunk 5952 32 =
      StrongPackedBucketN12A3AlignedShard046.missing5952_5984 := by decide
  have h5984_6016 : maskChunk 5984 32 =
      StrongPackedBucketN12A3AlignedShard046.missing5984_6016 := by decide
  have h5888_5952 : maskChunk 5888 64 =
      StrongPackedBucketN12A3AlignedShard046.missing5888_5952 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5888_5920, h5920_5952]
    rfl
  have h5952_6016 : maskChunk 5952 64 =
      StrongPackedBucketN12A3AlignedShard046.missing5952_6016 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h5952_5984, h5984_6016]
    rfl
  have h5888_6016 : maskChunk 5888 128 =
      StrongPackedBucketN12A3AlignedShard046.missing5888_6016 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h5888_5952, h5952_6016]
    rfl
  exact h5888_6016

private theorem shardMask47 : maskChunk 6016 128 =
    StrongPackedBucketN12A3AlignedShard047.missing := by
  have h6016_6048 : maskChunk 6016 32 =
      StrongPackedBucketN12A3AlignedShard047.missing6016_6048 := by decide
  have h6048_6080 : maskChunk 6048 32 =
      StrongPackedBucketN12A3AlignedShard047.missing6048_6080 := by decide
  have h6080_6112 : maskChunk 6080 32 =
      StrongPackedBucketN12A3AlignedShard047.missing6080_6112 := by decide
  have h6112_6144 : maskChunk 6112 32 =
      StrongPackedBucketN12A3AlignedShard047.missing6112_6144 := by decide
  have h6016_6080 : maskChunk 6016 64 =
      StrongPackedBucketN12A3AlignedShard047.missing6016_6080 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6016_6048, h6048_6080]
    rfl
  have h6080_6144 : maskChunk 6080 64 =
      StrongPackedBucketN12A3AlignedShard047.missing6080_6144 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6080_6112, h6112_6144]
    rfl
  have h6016_6144 : maskChunk 6016 128 =
      StrongPackedBucketN12A3AlignedShard047.missing6016_6144 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h6016_6080, h6080_6144]
    rfl
  exact h6016_6144

private theorem shardMask48 : maskChunk 6144 128 =
    StrongPackedBucketN12A3AlignedShard048.missing := by
  have h6144_6176 : maskChunk 6144 32 =
      StrongPackedBucketN12A3AlignedShard048.missing6144_6176 := by decide
  have h6176_6208 : maskChunk 6176 32 =
      StrongPackedBucketN12A3AlignedShard048.missing6176_6208 := by decide
  have h6208_6240 : maskChunk 6208 32 =
      StrongPackedBucketN12A3AlignedShard048.missing6208_6240 := by decide
  have h6240_6272 : maskChunk 6240 32 =
      StrongPackedBucketN12A3AlignedShard048.missing6240_6272 := by decide
  have h6144_6208 : maskChunk 6144 64 =
      StrongPackedBucketN12A3AlignedShard048.missing6144_6208 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6144_6176, h6176_6208]
    rfl
  have h6208_6272 : maskChunk 6208 64 =
      StrongPackedBucketN12A3AlignedShard048.missing6208_6272 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6208_6240, h6240_6272]
    rfl
  have h6144_6272 : maskChunk 6144 128 =
      StrongPackedBucketN12A3AlignedShard048.missing6144_6272 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h6144_6208, h6208_6272]
    rfl
  exact h6144_6272

private theorem shardMask49 : maskChunk 6272 128 =
    StrongPackedBucketN12A3AlignedShard049.missing := by
  have h6272_6304 : maskChunk 6272 32 =
      StrongPackedBucketN12A3AlignedShard049.missing6272_6304 := by decide
  have h6304_6336 : maskChunk 6304 32 =
      StrongPackedBucketN12A3AlignedShard049.missing6304_6336 := by decide
  have h6336_6368 : maskChunk 6336 32 =
      StrongPackedBucketN12A3AlignedShard049.missing6336_6368 := by decide
  have h6368_6400 : maskChunk 6368 32 =
      StrongPackedBucketN12A3AlignedShard049.missing6368_6400 := by decide
  have h6272_6336 : maskChunk 6272 64 =
      StrongPackedBucketN12A3AlignedShard049.missing6272_6336 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6272_6304, h6304_6336]
    rfl
  have h6336_6400 : maskChunk 6336 64 =
      StrongPackedBucketN12A3AlignedShard049.missing6336_6400 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6336_6368, h6368_6400]
    rfl
  have h6272_6400 : maskChunk 6272 128 =
      StrongPackedBucketN12A3AlignedShard049.missing6272_6400 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h6272_6336, h6336_6400]
    rfl
  exact h6272_6400

private theorem shardMask50 : maskChunk 6400 128 =
    StrongPackedBucketN12A3AlignedShard050.missing := by
  have h6400_6432 : maskChunk 6400 32 =
      StrongPackedBucketN12A3AlignedShard050.missing6400_6432 := by decide
  have h6432_6464 : maskChunk 6432 32 =
      StrongPackedBucketN12A3AlignedShard050.missing6432_6464 := by decide
  have h6464_6496 : maskChunk 6464 32 =
      StrongPackedBucketN12A3AlignedShard050.missing6464_6496 := by decide
  have h6496_6528 : maskChunk 6496 32 =
      StrongPackedBucketN12A3AlignedShard050.missing6496_6528 := by decide
  have h6400_6464 : maskChunk 6400 64 =
      StrongPackedBucketN12A3AlignedShard050.missing6400_6464 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6400_6432, h6432_6464]
    rfl
  have h6464_6528 : maskChunk 6464 64 =
      StrongPackedBucketN12A3AlignedShard050.missing6464_6528 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6464_6496, h6496_6528]
    rfl
  have h6400_6528 : maskChunk 6400 128 =
      StrongPackedBucketN12A3AlignedShard050.missing6400_6528 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h6400_6464, h6464_6528]
    rfl
  exact h6400_6528

private theorem shardMask51 : maskChunk 6528 128 =
    StrongPackedBucketN12A3AlignedShard051.missing := by
  have h6528_6560 : maskChunk 6528 32 =
      StrongPackedBucketN12A3AlignedShard051.missing6528_6560 := by decide
  have h6560_6592 : maskChunk 6560 32 =
      StrongPackedBucketN12A3AlignedShard051.missing6560_6592 := by decide
  have h6592_6624 : maskChunk 6592 32 =
      StrongPackedBucketN12A3AlignedShard051.missing6592_6624 := by decide
  have h6624_6656 : maskChunk 6624 32 =
      StrongPackedBucketN12A3AlignedShard051.missing6624_6656 := by decide
  have h6528_6592 : maskChunk 6528 64 =
      StrongPackedBucketN12A3AlignedShard051.missing6528_6592 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6528_6560, h6560_6592]
    rfl
  have h6592_6656 : maskChunk 6592 64 =
      StrongPackedBucketN12A3AlignedShard051.missing6592_6656 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6592_6624, h6624_6656]
    rfl
  have h6528_6656 : maskChunk 6528 128 =
      StrongPackedBucketN12A3AlignedShard051.missing6528_6656 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h6528_6592, h6592_6656]
    rfl
  exact h6528_6656

private theorem shardMask52 : maskChunk 6656 128 =
    StrongPackedBucketN12A3AlignedShard052.missing := by
  have h6656_6688 : maskChunk 6656 32 =
      StrongPackedBucketN12A3AlignedShard052.missing6656_6688 := by decide
  have h6688_6720 : maskChunk 6688 32 =
      StrongPackedBucketN12A3AlignedShard052.missing6688_6720 := by decide
  have h6720_6752 : maskChunk 6720 32 =
      StrongPackedBucketN12A3AlignedShard052.missing6720_6752 := by decide
  have h6752_6784 : maskChunk 6752 32 =
      StrongPackedBucketN12A3AlignedShard052.missing6752_6784 := by decide
  have h6656_6720 : maskChunk 6656 64 =
      StrongPackedBucketN12A3AlignedShard052.missing6656_6720 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6656_6688, h6688_6720]
    rfl
  have h6720_6784 : maskChunk 6720 64 =
      StrongPackedBucketN12A3AlignedShard052.missing6720_6784 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6720_6752, h6752_6784]
    rfl
  have h6656_6784 : maskChunk 6656 128 =
      StrongPackedBucketN12A3AlignedShard052.missing6656_6784 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h6656_6720, h6720_6784]
    rfl
  exact h6656_6784

private theorem shardMask53 : maskChunk 6784 128 =
    StrongPackedBucketN12A3AlignedShard053.missing := by
  have h6784_6816 : maskChunk 6784 32 =
      StrongPackedBucketN12A3AlignedShard053.missing6784_6816 := by decide
  have h6816_6848 : maskChunk 6816 32 =
      StrongPackedBucketN12A3AlignedShard053.missing6816_6848 := by decide
  have h6848_6880 : maskChunk 6848 32 =
      StrongPackedBucketN12A3AlignedShard053.missing6848_6880 := by decide
  have h6880_6912 : maskChunk 6880 32 =
      StrongPackedBucketN12A3AlignedShard053.missing6880_6912 := by decide
  have h6784_6848 : maskChunk 6784 64 =
      StrongPackedBucketN12A3AlignedShard053.missing6784_6848 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6784_6816, h6816_6848]
    rfl
  have h6848_6912 : maskChunk 6848 64 =
      StrongPackedBucketN12A3AlignedShard053.missing6848_6912 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6848_6880, h6880_6912]
    rfl
  have h6784_6912 : maskChunk 6784 128 =
      StrongPackedBucketN12A3AlignedShard053.missing6784_6912 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h6784_6848, h6848_6912]
    rfl
  exact h6784_6912

private theorem shardMask54 : maskChunk 6912 128 =
    StrongPackedBucketN12A3AlignedShard054.missing := by
  have h6912_6944 : maskChunk 6912 32 =
      StrongPackedBucketN12A3AlignedShard054.missing6912_6944 := by decide
  have h6944_6976 : maskChunk 6944 32 =
      StrongPackedBucketN12A3AlignedShard054.missing6944_6976 := by decide
  have h6976_7008 : maskChunk 6976 32 =
      StrongPackedBucketN12A3AlignedShard054.missing6976_7008 := by decide
  have h7008_7040 : maskChunk 7008 32 =
      StrongPackedBucketN12A3AlignedShard054.missing7008_7040 := by decide
  have h6912_6976 : maskChunk 6912 64 =
      StrongPackedBucketN12A3AlignedShard054.missing6912_6976 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6912_6944, h6944_6976]
    rfl
  have h6976_7040 : maskChunk 6976 64 =
      StrongPackedBucketN12A3AlignedShard054.missing6976_7040 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h6976_7008, h7008_7040]
    rfl
  have h6912_7040 : maskChunk 6912 128 =
      StrongPackedBucketN12A3AlignedShard054.missing6912_7040 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h6912_6976, h6976_7040]
    rfl
  exact h6912_7040

private theorem shardMask55 : maskChunk 7040 128 =
    StrongPackedBucketN12A3AlignedShard055.missing := by
  have h7040_7072 : maskChunk 7040 32 =
      StrongPackedBucketN12A3AlignedShard055.missing7040_7072 := by decide
  have h7072_7104 : maskChunk 7072 32 =
      StrongPackedBucketN12A3AlignedShard055.missing7072_7104 := by decide
  have h7104_7136 : maskChunk 7104 32 =
      StrongPackedBucketN12A3AlignedShard055.missing7104_7136 := by decide
  have h7136_7168 : maskChunk 7136 32 =
      StrongPackedBucketN12A3AlignedShard055.missing7136_7168 := by decide
  have h7040_7104 : maskChunk 7040 64 =
      StrongPackedBucketN12A3AlignedShard055.missing7040_7104 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7040_7072, h7072_7104]
    rfl
  have h7104_7168 : maskChunk 7104 64 =
      StrongPackedBucketN12A3AlignedShard055.missing7104_7168 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7104_7136, h7136_7168]
    rfl
  have h7040_7168 : maskChunk 7040 128 =
      StrongPackedBucketN12A3AlignedShard055.missing7040_7168 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h7040_7104, h7104_7168]
    rfl
  exact h7040_7168

private theorem shardMask56 : maskChunk 7168 128 =
    StrongPackedBucketN12A3AlignedShard056.missing := by
  have h7168_7200 : maskChunk 7168 32 =
      StrongPackedBucketN12A3AlignedShard056.missing7168_7200 := by decide
  have h7200_7232 : maskChunk 7200 32 =
      StrongPackedBucketN12A3AlignedShard056.missing7200_7232 := by decide
  have h7232_7264 : maskChunk 7232 32 =
      StrongPackedBucketN12A3AlignedShard056.missing7232_7264 := by decide
  have h7264_7296 : maskChunk 7264 32 =
      StrongPackedBucketN12A3AlignedShard056.missing7264_7296 := by decide
  have h7168_7232 : maskChunk 7168 64 =
      StrongPackedBucketN12A3AlignedShard056.missing7168_7232 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7168_7200, h7200_7232]
    rfl
  have h7232_7296 : maskChunk 7232 64 =
      StrongPackedBucketN12A3AlignedShard056.missing7232_7296 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7232_7264, h7264_7296]
    rfl
  have h7168_7296 : maskChunk 7168 128 =
      StrongPackedBucketN12A3AlignedShard056.missing7168_7296 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h7168_7232, h7232_7296]
    rfl
  exact h7168_7296

private theorem shardMask57 : maskChunk 7296 128 =
    StrongPackedBucketN12A3AlignedShard057.missing := by
  have h7296_7328 : maskChunk 7296 32 =
      StrongPackedBucketN12A3AlignedShard057.missing7296_7328 := by decide
  have h7328_7360 : maskChunk 7328 32 =
      StrongPackedBucketN12A3AlignedShard057.missing7328_7360 := by decide
  have h7360_7392 : maskChunk 7360 32 =
      StrongPackedBucketN12A3AlignedShard057.missing7360_7392 := by decide
  have h7392_7424 : maskChunk 7392 32 =
      StrongPackedBucketN12A3AlignedShard057.missing7392_7424 := by decide
  have h7296_7360 : maskChunk 7296 64 =
      StrongPackedBucketN12A3AlignedShard057.missing7296_7360 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7296_7328, h7328_7360]
    rfl
  have h7360_7424 : maskChunk 7360 64 =
      StrongPackedBucketN12A3AlignedShard057.missing7360_7424 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7360_7392, h7392_7424]
    rfl
  have h7296_7424 : maskChunk 7296 128 =
      StrongPackedBucketN12A3AlignedShard057.missing7296_7424 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h7296_7360, h7360_7424]
    rfl
  exact h7296_7424

private theorem shardMask58 : maskChunk 7424 128 =
    StrongPackedBucketN12A3AlignedShard058.missing := by
  have h7424_7456 : maskChunk 7424 32 =
      StrongPackedBucketN12A3AlignedShard058.missing7424_7456 := by decide
  have h7456_7488 : maskChunk 7456 32 =
      StrongPackedBucketN12A3AlignedShard058.missing7456_7488 := by decide
  have h7488_7520 : maskChunk 7488 32 =
      StrongPackedBucketN12A3AlignedShard058.missing7488_7520 := by decide
  have h7520_7552 : maskChunk 7520 32 =
      StrongPackedBucketN12A3AlignedShard058.missing7520_7552 := by decide
  have h7424_7488 : maskChunk 7424 64 =
      StrongPackedBucketN12A3AlignedShard058.missing7424_7488 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7424_7456, h7456_7488]
    rfl
  have h7488_7552 : maskChunk 7488 64 =
      StrongPackedBucketN12A3AlignedShard058.missing7488_7552 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7488_7520, h7520_7552]
    rfl
  have h7424_7552 : maskChunk 7424 128 =
      StrongPackedBucketN12A3AlignedShard058.missing7424_7552 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h7424_7488, h7488_7552]
    rfl
  exact h7424_7552

private theorem shardMask59 : maskChunk 7552 128 =
    StrongPackedBucketN12A3AlignedShard059.missing := by
  have h7552_7584 : maskChunk 7552 32 =
      StrongPackedBucketN12A3AlignedShard059.missing7552_7584 := by decide
  have h7584_7616 : maskChunk 7584 32 =
      StrongPackedBucketN12A3AlignedShard059.missing7584_7616 := by decide
  have h7616_7648 : maskChunk 7616 32 =
      StrongPackedBucketN12A3AlignedShard059.missing7616_7648 := by decide
  have h7648_7680 : maskChunk 7648 32 =
      StrongPackedBucketN12A3AlignedShard059.missing7648_7680 := by decide
  have h7552_7616 : maskChunk 7552 64 =
      StrongPackedBucketN12A3AlignedShard059.missing7552_7616 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7552_7584, h7584_7616]
    rfl
  have h7616_7680 : maskChunk 7616 64 =
      StrongPackedBucketN12A3AlignedShard059.missing7616_7680 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7616_7648, h7648_7680]
    rfl
  have h7552_7680 : maskChunk 7552 128 =
      StrongPackedBucketN12A3AlignedShard059.missing7552_7680 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h7552_7616, h7616_7680]
    rfl
  exact h7552_7680

private theorem shardMask60 : maskChunk 7680 128 =
    StrongPackedBucketN12A3AlignedShard060.missing := by
  have h7680_7712 : maskChunk 7680 32 =
      StrongPackedBucketN12A3AlignedShard060.missing7680_7712 := by decide
  have h7712_7744 : maskChunk 7712 32 =
      StrongPackedBucketN12A3AlignedShard060.missing7712_7744 := by decide
  have h7744_7776 : maskChunk 7744 32 =
      StrongPackedBucketN12A3AlignedShard060.missing7744_7776 := by decide
  have h7776_7808 : maskChunk 7776 32 =
      StrongPackedBucketN12A3AlignedShard060.missing7776_7808 := by decide
  have h7680_7744 : maskChunk 7680 64 =
      StrongPackedBucketN12A3AlignedShard060.missing7680_7744 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7680_7712, h7712_7744]
    rfl
  have h7744_7808 : maskChunk 7744 64 =
      StrongPackedBucketN12A3AlignedShard060.missing7744_7808 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7744_7776, h7776_7808]
    rfl
  have h7680_7808 : maskChunk 7680 128 =
      StrongPackedBucketN12A3AlignedShard060.missing7680_7808 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h7680_7744, h7744_7808]
    rfl
  exact h7680_7808

private theorem shardMask61 : maskChunk 7808 128 =
    StrongPackedBucketN12A3AlignedShard061.missing := by
  have h7808_7840 : maskChunk 7808 32 =
      StrongPackedBucketN12A3AlignedShard061.missing7808_7840 := by decide
  have h7840_7872 : maskChunk 7840 32 =
      StrongPackedBucketN12A3AlignedShard061.missing7840_7872 := by decide
  have h7872_7904 : maskChunk 7872 32 =
      StrongPackedBucketN12A3AlignedShard061.missing7872_7904 := by decide
  have h7904_7936 : maskChunk 7904 32 =
      StrongPackedBucketN12A3AlignedShard061.missing7904_7936 := by decide
  have h7808_7872 : maskChunk 7808 64 =
      StrongPackedBucketN12A3AlignedShard061.missing7808_7872 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7808_7840, h7840_7872]
    rfl
  have h7872_7936 : maskChunk 7872 64 =
      StrongPackedBucketN12A3AlignedShard061.missing7872_7936 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7872_7904, h7904_7936]
    rfl
  have h7808_7936 : maskChunk 7808 128 =
      StrongPackedBucketN12A3AlignedShard061.missing7808_7936 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h7808_7872, h7872_7936]
    rfl
  exact h7808_7936

private theorem shardMask62 : maskChunk 7936 128 =
    StrongPackedBucketN12A3AlignedShard062.missing := by
  have h7936_7968 : maskChunk 7936 32 =
      StrongPackedBucketN12A3AlignedShard062.missing7936_7968 := by decide
  have h7968_8000 : maskChunk 7968 32 =
      StrongPackedBucketN12A3AlignedShard062.missing7968_8000 := by decide
  have h8000_8032 : maskChunk 8000 32 =
      StrongPackedBucketN12A3AlignedShard062.missing8000_8032 := by decide
  have h8032_8064 : maskChunk 8032 32 =
      StrongPackedBucketN12A3AlignedShard062.missing8032_8064 := by decide
  have h7936_8000 : maskChunk 7936 64 =
      StrongPackedBucketN12A3AlignedShard062.missing7936_8000 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h7936_7968, h7968_8000]
    rfl
  have h8000_8064 : maskChunk 8000 64 =
      StrongPackedBucketN12A3AlignedShard062.missing8000_8064 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8000_8032, h8032_8064]
    rfl
  have h7936_8064 : maskChunk 7936 128 =
      StrongPackedBucketN12A3AlignedShard062.missing7936_8064 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h7936_8000, h8000_8064]
    rfl
  exact h7936_8064

private theorem shardMask63 : maskChunk 8064 128 =
    StrongPackedBucketN12A3AlignedShard063.missing := by
  have h8064_8096 : maskChunk 8064 32 =
      StrongPackedBucketN12A3AlignedShard063.missing8064_8096 := by decide
  have h8096_8128 : maskChunk 8096 32 =
      StrongPackedBucketN12A3AlignedShard063.missing8096_8128 := by decide
  have h8128_8160 : maskChunk 8128 32 =
      StrongPackedBucketN12A3AlignedShard063.missing8128_8160 := by decide
  have h8160_8192 : maskChunk 8160 32 =
      StrongPackedBucketN12A3AlignedShard063.missing8160_8192 := by decide
  have h8064_8128 : maskChunk 8064 64 =
      StrongPackedBucketN12A3AlignedShard063.missing8064_8128 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8064_8096, h8096_8128]
    rfl
  have h8128_8192 : maskChunk 8128 64 =
      StrongPackedBucketN12A3AlignedShard063.missing8128_8192 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8128_8160, h8160_8192]
    rfl
  have h8064_8192 : maskChunk 8064 128 =
      StrongPackedBucketN12A3AlignedShard063.missing8064_8192 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h8064_8128, h8128_8192]
    rfl
  exact h8064_8192

private theorem shardMask64 : maskChunk 8192 128 =
    StrongPackedBucketN12A3AlignedShard064.missing := by
  have h8192_8224 : maskChunk 8192 32 =
      StrongPackedBucketN12A3AlignedShard064.missing8192_8224 := by decide
  have h8224_8256 : maskChunk 8224 32 =
      StrongPackedBucketN12A3AlignedShard064.missing8224_8256 := by decide
  have h8256_8288 : maskChunk 8256 32 =
      StrongPackedBucketN12A3AlignedShard064.missing8256_8288 := by decide
  have h8288_8320 : maskChunk 8288 32 =
      StrongPackedBucketN12A3AlignedShard064.missing8288_8320 := by decide
  have h8192_8256 : maskChunk 8192 64 =
      StrongPackedBucketN12A3AlignedShard064.missing8192_8256 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8192_8224, h8224_8256]
    rfl
  have h8256_8320 : maskChunk 8256 64 =
      StrongPackedBucketN12A3AlignedShard064.missing8256_8320 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8256_8288, h8288_8320]
    rfl
  have h8192_8320 : maskChunk 8192 128 =
      StrongPackedBucketN12A3AlignedShard064.missing8192_8320 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h8192_8256, h8256_8320]
    rfl
  exact h8192_8320

private theorem shardMask65 : maskChunk 8320 128 =
    StrongPackedBucketN12A3AlignedShard065.missing := by
  have h8320_8352 : maskChunk 8320 32 =
      StrongPackedBucketN12A3AlignedShard065.missing8320_8352 := by decide
  have h8352_8384 : maskChunk 8352 32 =
      StrongPackedBucketN12A3AlignedShard065.missing8352_8384 := by decide
  have h8384_8416 : maskChunk 8384 32 =
      StrongPackedBucketN12A3AlignedShard065.missing8384_8416 := by decide
  have h8416_8448 : maskChunk 8416 32 =
      StrongPackedBucketN12A3AlignedShard065.missing8416_8448 := by decide
  have h8320_8384 : maskChunk 8320 64 =
      StrongPackedBucketN12A3AlignedShard065.missing8320_8384 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8320_8352, h8352_8384]
    rfl
  have h8384_8448 : maskChunk 8384 64 =
      StrongPackedBucketN12A3AlignedShard065.missing8384_8448 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8384_8416, h8416_8448]
    rfl
  have h8320_8448 : maskChunk 8320 128 =
      StrongPackedBucketN12A3AlignedShard065.missing8320_8448 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h8320_8384, h8384_8448]
    rfl
  exact h8320_8448

private theorem shardMask66 : maskChunk 8448 128 =
    StrongPackedBucketN12A3AlignedShard066.missing := by
  have h8448_8480 : maskChunk 8448 32 =
      StrongPackedBucketN12A3AlignedShard066.missing8448_8480 := by decide
  have h8480_8512 : maskChunk 8480 32 =
      StrongPackedBucketN12A3AlignedShard066.missing8480_8512 := by decide
  have h8512_8544 : maskChunk 8512 32 =
      StrongPackedBucketN12A3AlignedShard066.missing8512_8544 := by decide
  have h8544_8576 : maskChunk 8544 32 =
      StrongPackedBucketN12A3AlignedShard066.missing8544_8576 := by decide
  have h8448_8512 : maskChunk 8448 64 =
      StrongPackedBucketN12A3AlignedShard066.missing8448_8512 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8448_8480, h8480_8512]
    rfl
  have h8512_8576 : maskChunk 8512 64 =
      StrongPackedBucketN12A3AlignedShard066.missing8512_8576 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8512_8544, h8544_8576]
    rfl
  have h8448_8576 : maskChunk 8448 128 =
      StrongPackedBucketN12A3AlignedShard066.missing8448_8576 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h8448_8512, h8512_8576]
    rfl
  exact h8448_8576

private theorem shardMask67 : maskChunk 8576 128 =
    StrongPackedBucketN12A3AlignedShard067.missing := by
  have h8576_8608 : maskChunk 8576 32 =
      StrongPackedBucketN12A3AlignedShard067.missing8576_8608 := by decide
  have h8608_8640 : maskChunk 8608 32 =
      StrongPackedBucketN12A3AlignedShard067.missing8608_8640 := by decide
  have h8640_8672 : maskChunk 8640 32 =
      StrongPackedBucketN12A3AlignedShard067.missing8640_8672 := by decide
  have h8672_8704 : maskChunk 8672 32 =
      StrongPackedBucketN12A3AlignedShard067.missing8672_8704 := by decide
  have h8576_8640 : maskChunk 8576 64 =
      StrongPackedBucketN12A3AlignedShard067.missing8576_8640 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8576_8608, h8608_8640]
    rfl
  have h8640_8704 : maskChunk 8640 64 =
      StrongPackedBucketN12A3AlignedShard067.missing8640_8704 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8640_8672, h8672_8704]
    rfl
  have h8576_8704 : maskChunk 8576 128 =
      StrongPackedBucketN12A3AlignedShard067.missing8576_8704 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h8576_8640, h8640_8704]
    rfl
  exact h8576_8704

private theorem shardMask68 : maskChunk 8704 128 =
    StrongPackedBucketN12A3AlignedShard068.missing := by
  have h8704_8736 : maskChunk 8704 32 =
      StrongPackedBucketN12A3AlignedShard068.missing8704_8736 := by decide
  have h8736_8768 : maskChunk 8736 32 =
      StrongPackedBucketN12A3AlignedShard068.missing8736_8768 := by decide
  have h8768_8800 : maskChunk 8768 32 =
      StrongPackedBucketN12A3AlignedShard068.missing8768_8800 := by decide
  have h8800_8832 : maskChunk 8800 32 =
      StrongPackedBucketN12A3AlignedShard068.missing8800_8832 := by decide
  have h8704_8768 : maskChunk 8704 64 =
      StrongPackedBucketN12A3AlignedShard068.missing8704_8768 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8704_8736, h8736_8768]
    rfl
  have h8768_8832 : maskChunk 8768 64 =
      StrongPackedBucketN12A3AlignedShard068.missing8768_8832 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8768_8800, h8800_8832]
    rfl
  have h8704_8832 : maskChunk 8704 128 =
      StrongPackedBucketN12A3AlignedShard068.missing8704_8832 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h8704_8768, h8768_8832]
    rfl
  exact h8704_8832

private theorem shardMask69 : maskChunk 8832 128 =
    StrongPackedBucketN12A3AlignedShard069.missing := by
  have h8832_8864 : maskChunk 8832 32 =
      StrongPackedBucketN12A3AlignedShard069.missing8832_8864 := by decide
  have h8864_8896 : maskChunk 8864 32 =
      StrongPackedBucketN12A3AlignedShard069.missing8864_8896 := by decide
  have h8896_8928 : maskChunk 8896 32 =
      StrongPackedBucketN12A3AlignedShard069.missing8896_8928 := by decide
  have h8928_8960 : maskChunk 8928 32 =
      StrongPackedBucketN12A3AlignedShard069.missing8928_8960 := by decide
  have h8832_8896 : maskChunk 8832 64 =
      StrongPackedBucketN12A3AlignedShard069.missing8832_8896 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8832_8864, h8864_8896]
    rfl
  have h8896_8960 : maskChunk 8896 64 =
      StrongPackedBucketN12A3AlignedShard069.missing8896_8960 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8896_8928, h8928_8960]
    rfl
  have h8832_8960 : maskChunk 8832 128 =
      StrongPackedBucketN12A3AlignedShard069.missing8832_8960 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h8832_8896, h8896_8960]
    rfl
  exact h8832_8960

private theorem shardMask70 : maskChunk 8960 128 =
    StrongPackedBucketN12A3AlignedShard070.missing := by
  have h8960_8992 : maskChunk 8960 32 =
      StrongPackedBucketN12A3AlignedShard070.missing8960_8992 := by decide
  have h8992_9024 : maskChunk 8992 32 =
      StrongPackedBucketN12A3AlignedShard070.missing8992_9024 := by decide
  have h9024_9056 : maskChunk 9024 32 =
      StrongPackedBucketN12A3AlignedShard070.missing9024_9056 := by decide
  have h9056_9088 : maskChunk 9056 32 =
      StrongPackedBucketN12A3AlignedShard070.missing9056_9088 := by decide
  have h8960_9024 : maskChunk 8960 64 =
      StrongPackedBucketN12A3AlignedShard070.missing8960_9024 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h8960_8992, h8992_9024]
    rfl
  have h9024_9088 : maskChunk 9024 64 =
      StrongPackedBucketN12A3AlignedShard070.missing9024_9088 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9024_9056, h9056_9088]
    rfl
  have h8960_9088 : maskChunk 8960 128 =
      StrongPackedBucketN12A3AlignedShard070.missing8960_9088 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h8960_9024, h9024_9088]
    rfl
  exact h8960_9088

private theorem shardMask71 : maskChunk 9088 128 =
    StrongPackedBucketN12A3AlignedShard071.missing := by
  have h9088_9120 : maskChunk 9088 32 =
      StrongPackedBucketN12A3AlignedShard071.missing9088_9120 := by decide
  have h9120_9152 : maskChunk 9120 32 =
      StrongPackedBucketN12A3AlignedShard071.missing9120_9152 := by decide
  have h9152_9184 : maskChunk 9152 32 =
      StrongPackedBucketN12A3AlignedShard071.missing9152_9184 := by decide
  have h9184_9216 : maskChunk 9184 32 =
      StrongPackedBucketN12A3AlignedShard071.missing9184_9216 := by decide
  have h9088_9152 : maskChunk 9088 64 =
      StrongPackedBucketN12A3AlignedShard071.missing9088_9152 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9088_9120, h9120_9152]
    rfl
  have h9152_9216 : maskChunk 9152 64 =
      StrongPackedBucketN12A3AlignedShard071.missing9152_9216 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9152_9184, h9184_9216]
    rfl
  have h9088_9216 : maskChunk 9088 128 =
      StrongPackedBucketN12A3AlignedShard071.missing9088_9216 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h9088_9152, h9152_9216]
    rfl
  exact h9088_9216

private theorem shardMask72 : maskChunk 9216 128 =
    StrongPackedBucketN12A3AlignedShard072.missing := by
  have h9216_9248 : maskChunk 9216 32 =
      StrongPackedBucketN12A3AlignedShard072.missing9216_9248 := by decide
  have h9248_9280 : maskChunk 9248 32 =
      StrongPackedBucketN12A3AlignedShard072.missing9248_9280 := by decide
  have h9280_9312 : maskChunk 9280 32 =
      StrongPackedBucketN12A3AlignedShard072.missing9280_9312 := by decide
  have h9312_9344 : maskChunk 9312 32 =
      StrongPackedBucketN12A3AlignedShard072.missing9312_9344 := by decide
  have h9216_9280 : maskChunk 9216 64 =
      StrongPackedBucketN12A3AlignedShard072.missing9216_9280 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9216_9248, h9248_9280]
    rfl
  have h9280_9344 : maskChunk 9280 64 =
      StrongPackedBucketN12A3AlignedShard072.missing9280_9344 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9280_9312, h9312_9344]
    rfl
  have h9216_9344 : maskChunk 9216 128 =
      StrongPackedBucketN12A3AlignedShard072.missing9216_9344 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h9216_9280, h9280_9344]
    rfl
  exact h9216_9344

private theorem shardMask73 : maskChunk 9344 128 =
    StrongPackedBucketN12A3AlignedShard073.missing := by
  have h9344_9376 : maskChunk 9344 32 =
      StrongPackedBucketN12A3AlignedShard073.missing9344_9376 := by decide
  have h9376_9408 : maskChunk 9376 32 =
      StrongPackedBucketN12A3AlignedShard073.missing9376_9408 := by decide
  have h9408_9440 : maskChunk 9408 32 =
      StrongPackedBucketN12A3AlignedShard073.missing9408_9440 := by decide
  have h9440_9472 : maskChunk 9440 32 =
      StrongPackedBucketN12A3AlignedShard073.missing9440_9472 := by decide
  have h9344_9408 : maskChunk 9344 64 =
      StrongPackedBucketN12A3AlignedShard073.missing9344_9408 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9344_9376, h9376_9408]
    rfl
  have h9408_9472 : maskChunk 9408 64 =
      StrongPackedBucketN12A3AlignedShard073.missing9408_9472 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9408_9440, h9440_9472]
    rfl
  have h9344_9472 : maskChunk 9344 128 =
      StrongPackedBucketN12A3AlignedShard073.missing9344_9472 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h9344_9408, h9408_9472]
    rfl
  exact h9344_9472

private theorem shardMask74 : maskChunk 9472 128 =
    StrongPackedBucketN12A3AlignedShard074.missing := by
  have h9472_9504 : maskChunk 9472 32 =
      StrongPackedBucketN12A3AlignedShard074.missing9472_9504 := by decide
  have h9504_9536 : maskChunk 9504 32 =
      StrongPackedBucketN12A3AlignedShard074.missing9504_9536 := by decide
  have h9536_9568 : maskChunk 9536 32 =
      StrongPackedBucketN12A3AlignedShard074.missing9536_9568 := by decide
  have h9568_9600 : maskChunk 9568 32 =
      StrongPackedBucketN12A3AlignedShard074.missing9568_9600 := by decide
  have h9472_9536 : maskChunk 9472 64 =
      StrongPackedBucketN12A3AlignedShard074.missing9472_9536 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9472_9504, h9504_9536]
    rfl
  have h9536_9600 : maskChunk 9536 64 =
      StrongPackedBucketN12A3AlignedShard074.missing9536_9600 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9536_9568, h9568_9600]
    rfl
  have h9472_9600 : maskChunk 9472 128 =
      StrongPackedBucketN12A3AlignedShard074.missing9472_9600 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h9472_9536, h9536_9600]
    rfl
  exact h9472_9600

private theorem shardMask75 : maskChunk 9600 128 =
    StrongPackedBucketN12A3AlignedShard075.missing := by
  have h9600_9632 : maskChunk 9600 32 =
      StrongPackedBucketN12A3AlignedShard075.missing9600_9632 := by decide
  have h9632_9664 : maskChunk 9632 32 =
      StrongPackedBucketN12A3AlignedShard075.missing9632_9664 := by decide
  have h9664_9696 : maskChunk 9664 32 =
      StrongPackedBucketN12A3AlignedShard075.missing9664_9696 := by decide
  have h9696_9728 : maskChunk 9696 32 =
      StrongPackedBucketN12A3AlignedShard075.missing9696_9728 := by decide
  have h9600_9664 : maskChunk 9600 64 =
      StrongPackedBucketN12A3AlignedShard075.missing9600_9664 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9600_9632, h9632_9664]
    rfl
  have h9664_9728 : maskChunk 9664 64 =
      StrongPackedBucketN12A3AlignedShard075.missing9664_9728 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9664_9696, h9696_9728]
    rfl
  have h9600_9728 : maskChunk 9600 128 =
      StrongPackedBucketN12A3AlignedShard075.missing9600_9728 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h9600_9664, h9664_9728]
    rfl
  exact h9600_9728

private theorem shardMask76 : maskChunk 9728 128 =
    StrongPackedBucketN12A3AlignedShard076.missing := by
  have h9728_9760 : maskChunk 9728 32 =
      StrongPackedBucketN12A3AlignedShard076.missing9728_9760 := by decide
  have h9760_9792 : maskChunk 9760 32 =
      StrongPackedBucketN12A3AlignedShard076.missing9760_9792 := by decide
  have h9792_9824 : maskChunk 9792 32 =
      StrongPackedBucketN12A3AlignedShard076.missing9792_9824 := by decide
  have h9824_9856 : maskChunk 9824 32 =
      StrongPackedBucketN12A3AlignedShard076.missing9824_9856 := by decide
  have h9728_9792 : maskChunk 9728 64 =
      StrongPackedBucketN12A3AlignedShard076.missing9728_9792 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9728_9760, h9760_9792]
    rfl
  have h9792_9856 : maskChunk 9792 64 =
      StrongPackedBucketN12A3AlignedShard076.missing9792_9856 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9792_9824, h9824_9856]
    rfl
  have h9728_9856 : maskChunk 9728 128 =
      StrongPackedBucketN12A3AlignedShard076.missing9728_9856 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h9728_9792, h9792_9856]
    rfl
  exact h9728_9856

private theorem shardMask77 : maskChunk 9856 128 =
    StrongPackedBucketN12A3AlignedShard077.missing := by
  have h9856_9888 : maskChunk 9856 32 =
      StrongPackedBucketN12A3AlignedShard077.missing9856_9888 := by decide
  have h9888_9920 : maskChunk 9888 32 =
      StrongPackedBucketN12A3AlignedShard077.missing9888_9920 := by decide
  have h9920_9952 : maskChunk 9920 32 =
      StrongPackedBucketN12A3AlignedShard077.missing9920_9952 := by decide
  have h9952_9984 : maskChunk 9952 32 =
      StrongPackedBucketN12A3AlignedShard077.missing9952_9984 := by decide
  have h9856_9920 : maskChunk 9856 64 =
      StrongPackedBucketN12A3AlignedShard077.missing9856_9920 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9856_9888, h9888_9920]
    rfl
  have h9920_9984 : maskChunk 9920 64 =
      StrongPackedBucketN12A3AlignedShard077.missing9920_9984 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9920_9952, h9952_9984]
    rfl
  have h9856_9984 : maskChunk 9856 128 =
      StrongPackedBucketN12A3AlignedShard077.missing9856_9984 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h9856_9920, h9920_9984]
    rfl
  exact h9856_9984

private theorem shardMask78 : maskChunk 9984 128 =
    StrongPackedBucketN12A3AlignedShard078.missing := by
  have h9984_10016 : maskChunk 9984 32 =
      StrongPackedBucketN12A3AlignedShard078.missing9984_10016 := by decide
  have h10016_10048 : maskChunk 10016 32 =
      StrongPackedBucketN12A3AlignedShard078.missing10016_10048 := by decide
  have h10048_10080 : maskChunk 10048 32 =
      StrongPackedBucketN12A3AlignedShard078.missing10048_10080 := by decide
  have h10080_10112 : maskChunk 10080 32 =
      StrongPackedBucketN12A3AlignedShard078.missing10080_10112 := by decide
  have h9984_10048 : maskChunk 9984 64 =
      StrongPackedBucketN12A3AlignedShard078.missing9984_10048 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h9984_10016, h10016_10048]
    rfl
  have h10048_10112 : maskChunk 10048 64 =
      StrongPackedBucketN12A3AlignedShard078.missing10048_10112 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10048_10080, h10080_10112]
    rfl
  have h9984_10112 : maskChunk 9984 128 =
      StrongPackedBucketN12A3AlignedShard078.missing9984_10112 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h9984_10048, h10048_10112]
    rfl
  exact h9984_10112

private theorem shardMask79 : maskChunk 10112 128 =
    StrongPackedBucketN12A3AlignedShard079.missing := by
  have h10112_10144 : maskChunk 10112 32 =
      StrongPackedBucketN12A3AlignedShard079.missing10112_10144 := by decide
  have h10144_10176 : maskChunk 10144 32 =
      StrongPackedBucketN12A3AlignedShard079.missing10144_10176 := by decide
  have h10176_10208 : maskChunk 10176 32 =
      StrongPackedBucketN12A3AlignedShard079.missing10176_10208 := by decide
  have h10208_10240 : maskChunk 10208 32 =
      StrongPackedBucketN12A3AlignedShard079.missing10208_10240 := by decide
  have h10112_10176 : maskChunk 10112 64 =
      StrongPackedBucketN12A3AlignedShard079.missing10112_10176 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10112_10144, h10144_10176]
    rfl
  have h10176_10240 : maskChunk 10176 64 =
      StrongPackedBucketN12A3AlignedShard079.missing10176_10240 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10176_10208, h10208_10240]
    rfl
  have h10112_10240 : maskChunk 10112 128 =
      StrongPackedBucketN12A3AlignedShard079.missing10112_10240 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h10112_10176, h10176_10240]
    rfl
  exact h10112_10240

private theorem shardMask80 : maskChunk 10240 128 =
    StrongPackedBucketN12A3AlignedShard080.missing := by
  have h10240_10272 : maskChunk 10240 32 =
      StrongPackedBucketN12A3AlignedShard080.missing10240_10272 := by decide
  have h10272_10304 : maskChunk 10272 32 =
      StrongPackedBucketN12A3AlignedShard080.missing10272_10304 := by decide
  have h10304_10336 : maskChunk 10304 32 =
      StrongPackedBucketN12A3AlignedShard080.missing10304_10336 := by decide
  have h10336_10368 : maskChunk 10336 32 =
      StrongPackedBucketN12A3AlignedShard080.missing10336_10368 := by decide
  have h10240_10304 : maskChunk 10240 64 =
      StrongPackedBucketN12A3AlignedShard080.missing10240_10304 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10240_10272, h10272_10304]
    rfl
  have h10304_10368 : maskChunk 10304 64 =
      StrongPackedBucketN12A3AlignedShard080.missing10304_10368 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10304_10336, h10336_10368]
    rfl
  have h10240_10368 : maskChunk 10240 128 =
      StrongPackedBucketN12A3AlignedShard080.missing10240_10368 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h10240_10304, h10304_10368]
    rfl
  exact h10240_10368

private theorem shardMask81 : maskChunk 10368 128 =
    StrongPackedBucketN12A3AlignedShard081.missing := by
  have h10368_10400 : maskChunk 10368 32 =
      StrongPackedBucketN12A3AlignedShard081.missing10368_10400 := by decide
  have h10400_10432 : maskChunk 10400 32 =
      StrongPackedBucketN12A3AlignedShard081.missing10400_10432 := by decide
  have h10432_10464 : maskChunk 10432 32 =
      StrongPackedBucketN12A3AlignedShard081.missing10432_10464 := by decide
  have h10464_10496 : maskChunk 10464 32 =
      StrongPackedBucketN12A3AlignedShard081.missing10464_10496 := by decide
  have h10368_10432 : maskChunk 10368 64 =
      StrongPackedBucketN12A3AlignedShard081.missing10368_10432 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10368_10400, h10400_10432]
    rfl
  have h10432_10496 : maskChunk 10432 64 =
      StrongPackedBucketN12A3AlignedShard081.missing10432_10496 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10432_10464, h10464_10496]
    rfl
  have h10368_10496 : maskChunk 10368 128 =
      StrongPackedBucketN12A3AlignedShard081.missing10368_10496 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h10368_10432, h10432_10496]
    rfl
  exact h10368_10496

private theorem shardMask82 : maskChunk 10496 128 =
    StrongPackedBucketN12A3AlignedShard082.missing := by
  have h10496_10528 : maskChunk 10496 32 =
      StrongPackedBucketN12A3AlignedShard082.missing10496_10528 := by decide
  have h10528_10560 : maskChunk 10528 32 =
      StrongPackedBucketN12A3AlignedShard082.missing10528_10560 := by decide
  have h10560_10592 : maskChunk 10560 32 =
      StrongPackedBucketN12A3AlignedShard082.missing10560_10592 := by decide
  have h10592_10624 : maskChunk 10592 32 =
      StrongPackedBucketN12A3AlignedShard082.missing10592_10624 := by decide
  have h10496_10560 : maskChunk 10496 64 =
      StrongPackedBucketN12A3AlignedShard082.missing10496_10560 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10496_10528, h10528_10560]
    rfl
  have h10560_10624 : maskChunk 10560 64 =
      StrongPackedBucketN12A3AlignedShard082.missing10560_10624 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10560_10592, h10592_10624]
    rfl
  have h10496_10624 : maskChunk 10496 128 =
      StrongPackedBucketN12A3AlignedShard082.missing10496_10624 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h10496_10560, h10560_10624]
    rfl
  exact h10496_10624

private theorem shardMask83 : maskChunk 10624 128 =
    StrongPackedBucketN12A3AlignedShard083.missing := by
  have h10624_10656 : maskChunk 10624 32 =
      StrongPackedBucketN12A3AlignedShard083.missing10624_10656 := by decide
  have h10656_10688 : maskChunk 10656 32 =
      StrongPackedBucketN12A3AlignedShard083.missing10656_10688 := by decide
  have h10688_10720 : maskChunk 10688 32 =
      StrongPackedBucketN12A3AlignedShard083.missing10688_10720 := by decide
  have h10720_10752 : maskChunk 10720 32 =
      StrongPackedBucketN12A3AlignedShard083.missing10720_10752 := by decide
  have h10624_10688 : maskChunk 10624 64 =
      StrongPackedBucketN12A3AlignedShard083.missing10624_10688 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10624_10656, h10656_10688]
    rfl
  have h10688_10752 : maskChunk 10688 64 =
      StrongPackedBucketN12A3AlignedShard083.missing10688_10752 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10688_10720, h10720_10752]
    rfl
  have h10624_10752 : maskChunk 10624 128 =
      StrongPackedBucketN12A3AlignedShard083.missing10624_10752 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h10624_10688, h10688_10752]
    rfl
  exact h10624_10752

private theorem shardMask84 : maskChunk 10752 128 =
    StrongPackedBucketN12A3AlignedShard084.missing := by
  have h10752_10784 : maskChunk 10752 32 =
      StrongPackedBucketN12A3AlignedShard084.missing10752_10784 := by decide
  have h10784_10816 : maskChunk 10784 32 =
      StrongPackedBucketN12A3AlignedShard084.missing10784_10816 := by decide
  have h10816_10848 : maskChunk 10816 32 =
      StrongPackedBucketN12A3AlignedShard084.missing10816_10848 := by decide
  have h10848_10880 : maskChunk 10848 32 =
      StrongPackedBucketN12A3AlignedShard084.missing10848_10880 := by decide
  have h10752_10816 : maskChunk 10752 64 =
      StrongPackedBucketN12A3AlignedShard084.missing10752_10816 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10752_10784, h10784_10816]
    rfl
  have h10816_10880 : maskChunk 10816 64 =
      StrongPackedBucketN12A3AlignedShard084.missing10816_10880 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10816_10848, h10848_10880]
    rfl
  have h10752_10880 : maskChunk 10752 128 =
      StrongPackedBucketN12A3AlignedShard084.missing10752_10880 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h10752_10816, h10816_10880]
    rfl
  exact h10752_10880

private theorem shardMask85 : maskChunk 10880 128 =
    StrongPackedBucketN12A3AlignedShard085.missing := by
  have h10880_10912 : maskChunk 10880 32 =
      StrongPackedBucketN12A3AlignedShard085.missing10880_10912 := by decide
  have h10912_10944 : maskChunk 10912 32 =
      StrongPackedBucketN12A3AlignedShard085.missing10912_10944 := by decide
  have h10944_10976 : maskChunk 10944 32 =
      StrongPackedBucketN12A3AlignedShard085.missing10944_10976 := by decide
  have h10976_11008 : maskChunk 10976 32 =
      StrongPackedBucketN12A3AlignedShard085.missing10976_11008 := by decide
  have h10880_10944 : maskChunk 10880 64 =
      StrongPackedBucketN12A3AlignedShard085.missing10880_10944 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10880_10912, h10912_10944]
    rfl
  have h10944_11008 : maskChunk 10944 64 =
      StrongPackedBucketN12A3AlignedShard085.missing10944_11008 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h10944_10976, h10976_11008]
    rfl
  have h10880_11008 : maskChunk 10880 128 =
      StrongPackedBucketN12A3AlignedShard085.missing10880_11008 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h10880_10944, h10944_11008]
    rfl
  exact h10880_11008

private theorem shardMask86 : maskChunk 11008 128 =
    StrongPackedBucketN12A3AlignedShard086.missing := by
  have h11008_11040 : maskChunk 11008 32 =
      StrongPackedBucketN12A3AlignedShard086.missing11008_11040 := by decide
  have h11040_11072 : maskChunk 11040 32 =
      StrongPackedBucketN12A3AlignedShard086.missing11040_11072 := by decide
  have h11072_11104 : maskChunk 11072 32 =
      StrongPackedBucketN12A3AlignedShard086.missing11072_11104 := by decide
  have h11104_11136 : maskChunk 11104 32 =
      StrongPackedBucketN12A3AlignedShard086.missing11104_11136 := by decide
  have h11008_11072 : maskChunk 11008 64 =
      StrongPackedBucketN12A3AlignedShard086.missing11008_11072 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11008_11040, h11040_11072]
    rfl
  have h11072_11136 : maskChunk 11072 64 =
      StrongPackedBucketN12A3AlignedShard086.missing11072_11136 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11072_11104, h11104_11136]
    rfl
  have h11008_11136 : maskChunk 11008 128 =
      StrongPackedBucketN12A3AlignedShard086.missing11008_11136 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h11008_11072, h11072_11136]
    rfl
  exact h11008_11136

private theorem shardMask87 : maskChunk 11136 128 =
    StrongPackedBucketN12A3AlignedShard087.missing := by
  have h11136_11168 : maskChunk 11136 32 =
      StrongPackedBucketN12A3AlignedShard087.missing11136_11168 := by decide
  have h11168_11200 : maskChunk 11168 32 =
      StrongPackedBucketN12A3AlignedShard087.missing11168_11200 := by decide
  have h11200_11232 : maskChunk 11200 32 =
      StrongPackedBucketN12A3AlignedShard087.missing11200_11232 := by decide
  have h11232_11264 : maskChunk 11232 32 =
      StrongPackedBucketN12A3AlignedShard087.missing11232_11264 := by decide
  have h11136_11200 : maskChunk 11136 64 =
      StrongPackedBucketN12A3AlignedShard087.missing11136_11200 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11136_11168, h11168_11200]
    rfl
  have h11200_11264 : maskChunk 11200 64 =
      StrongPackedBucketN12A3AlignedShard087.missing11200_11264 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11200_11232, h11232_11264]
    rfl
  have h11136_11264 : maskChunk 11136 128 =
      StrongPackedBucketN12A3AlignedShard087.missing11136_11264 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h11136_11200, h11200_11264]
    rfl
  exact h11136_11264

private theorem shardMask88 : maskChunk 11264 128 =
    StrongPackedBucketN12A3AlignedShard088.missing := by
  have h11264_11296 : maskChunk 11264 32 =
      StrongPackedBucketN12A3AlignedShard088.missing11264_11296 := by decide
  have h11296_11328 : maskChunk 11296 32 =
      StrongPackedBucketN12A3AlignedShard088.missing11296_11328 := by decide
  have h11328_11360 : maskChunk 11328 32 =
      StrongPackedBucketN12A3AlignedShard088.missing11328_11360 := by decide
  have h11360_11392 : maskChunk 11360 32 =
      StrongPackedBucketN12A3AlignedShard088.missing11360_11392 := by decide
  have h11264_11328 : maskChunk 11264 64 =
      StrongPackedBucketN12A3AlignedShard088.missing11264_11328 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11264_11296, h11296_11328]
    rfl
  have h11328_11392 : maskChunk 11328 64 =
      StrongPackedBucketN12A3AlignedShard088.missing11328_11392 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11328_11360, h11360_11392]
    rfl
  have h11264_11392 : maskChunk 11264 128 =
      StrongPackedBucketN12A3AlignedShard088.missing11264_11392 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h11264_11328, h11328_11392]
    rfl
  exact h11264_11392

private theorem shardMask89 : maskChunk 11392 128 =
    StrongPackedBucketN12A3AlignedShard089.missing := by
  have h11392_11424 : maskChunk 11392 32 =
      StrongPackedBucketN12A3AlignedShard089.missing11392_11424 := by decide
  have h11424_11456 : maskChunk 11424 32 =
      StrongPackedBucketN12A3AlignedShard089.missing11424_11456 := by decide
  have h11456_11488 : maskChunk 11456 32 =
      StrongPackedBucketN12A3AlignedShard089.missing11456_11488 := by decide
  have h11488_11520 : maskChunk 11488 32 =
      StrongPackedBucketN12A3AlignedShard089.missing11488_11520 := by decide
  have h11392_11456 : maskChunk 11392 64 =
      StrongPackedBucketN12A3AlignedShard089.missing11392_11456 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11392_11424, h11424_11456]
    rfl
  have h11456_11520 : maskChunk 11456 64 =
      StrongPackedBucketN12A3AlignedShard089.missing11456_11520 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11456_11488, h11488_11520]
    rfl
  have h11392_11520 : maskChunk 11392 128 =
      StrongPackedBucketN12A3AlignedShard089.missing11392_11520 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h11392_11456, h11456_11520]
    rfl
  exact h11392_11520

private theorem shardMask90 : maskChunk 11520 128 =
    StrongPackedBucketN12A3AlignedShard090.missing := by
  have h11520_11552 : maskChunk 11520 32 =
      StrongPackedBucketN12A3AlignedShard090.missing11520_11552 := by decide
  have h11552_11584 : maskChunk 11552 32 =
      StrongPackedBucketN12A3AlignedShard090.missing11552_11584 := by decide
  have h11584_11616 : maskChunk 11584 32 =
      StrongPackedBucketN12A3AlignedShard090.missing11584_11616 := by decide
  have h11616_11648 : maskChunk 11616 32 =
      StrongPackedBucketN12A3AlignedShard090.missing11616_11648 := by decide
  have h11520_11584 : maskChunk 11520 64 =
      StrongPackedBucketN12A3AlignedShard090.missing11520_11584 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11520_11552, h11552_11584]
    rfl
  have h11584_11648 : maskChunk 11584 64 =
      StrongPackedBucketN12A3AlignedShard090.missing11584_11648 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11584_11616, h11616_11648]
    rfl
  have h11520_11648 : maskChunk 11520 128 =
      StrongPackedBucketN12A3AlignedShard090.missing11520_11648 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h11520_11584, h11584_11648]
    rfl
  exact h11520_11648

private theorem shardMask91 : maskChunk 11648 128 =
    StrongPackedBucketN12A3AlignedShard091.missing := by
  have h11648_11680 : maskChunk 11648 32 =
      StrongPackedBucketN12A3AlignedShard091.missing11648_11680 := by decide
  have h11680_11712 : maskChunk 11680 32 =
      StrongPackedBucketN12A3AlignedShard091.missing11680_11712 := by decide
  have h11712_11744 : maskChunk 11712 32 =
      StrongPackedBucketN12A3AlignedShard091.missing11712_11744 := by decide
  have h11744_11776 : maskChunk 11744 32 =
      StrongPackedBucketN12A3AlignedShard091.missing11744_11776 := by decide
  have h11648_11712 : maskChunk 11648 64 =
      StrongPackedBucketN12A3AlignedShard091.missing11648_11712 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11648_11680, h11680_11712]
    rfl
  have h11712_11776 : maskChunk 11712 64 =
      StrongPackedBucketN12A3AlignedShard091.missing11712_11776 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11712_11744, h11744_11776]
    rfl
  have h11648_11776 : maskChunk 11648 128 =
      StrongPackedBucketN12A3AlignedShard091.missing11648_11776 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h11648_11712, h11712_11776]
    rfl
  exact h11648_11776

private theorem shardMask92 : maskChunk 11776 128 =
    StrongPackedBucketN12A3AlignedShard092.missing := by
  have h11776_11808 : maskChunk 11776 32 =
      StrongPackedBucketN12A3AlignedShard092.missing11776_11808 := by decide
  have h11808_11840 : maskChunk 11808 32 =
      StrongPackedBucketN12A3AlignedShard092.missing11808_11840 := by decide
  have h11840_11872 : maskChunk 11840 32 =
      StrongPackedBucketN12A3AlignedShard092.missing11840_11872 := by decide
  have h11872_11904 : maskChunk 11872 32 =
      StrongPackedBucketN12A3AlignedShard092.missing11872_11904 := by decide
  have h11776_11840 : maskChunk 11776 64 =
      StrongPackedBucketN12A3AlignedShard092.missing11776_11840 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11776_11808, h11808_11840]
    rfl
  have h11840_11904 : maskChunk 11840 64 =
      StrongPackedBucketN12A3AlignedShard092.missing11840_11904 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11840_11872, h11872_11904]
    rfl
  have h11776_11904 : maskChunk 11776 128 =
      StrongPackedBucketN12A3AlignedShard092.missing11776_11904 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h11776_11840, h11840_11904]
    rfl
  exact h11776_11904

private theorem shardMask93 : maskChunk 11904 128 =
    StrongPackedBucketN12A3AlignedShard093.missing := by
  have h11904_11936 : maskChunk 11904 32 =
      StrongPackedBucketN12A3AlignedShard093.missing11904_11936 := by decide
  have h11936_11968 : maskChunk 11936 32 =
      StrongPackedBucketN12A3AlignedShard093.missing11936_11968 := by decide
  have h11968_12000 : maskChunk 11968 32 =
      StrongPackedBucketN12A3AlignedShard093.missing11968_12000 := by decide
  have h12000_12032 : maskChunk 12000 32 =
      StrongPackedBucketN12A3AlignedShard093.missing12000_12032 := by decide
  have h11904_11968 : maskChunk 11904 64 =
      StrongPackedBucketN12A3AlignedShard093.missing11904_11968 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11904_11936, h11936_11968]
    rfl
  have h11968_12032 : maskChunk 11968 64 =
      StrongPackedBucketN12A3AlignedShard093.missing11968_12032 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h11968_12000, h12000_12032]
    rfl
  have h11904_12032 : maskChunk 11904 128 =
      StrongPackedBucketN12A3AlignedShard093.missing11904_12032 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h11904_11968, h11968_12032]
    rfl
  exact h11904_12032

private theorem shardMask94 : maskChunk 12032 128 =
    StrongPackedBucketN12A3AlignedShard094.missing := by
  have h12032_12064 : maskChunk 12032 32 =
      StrongPackedBucketN12A3AlignedShard094.missing12032_12064 := by decide
  have h12064_12096 : maskChunk 12064 32 =
      StrongPackedBucketN12A3AlignedShard094.missing12064_12096 := by decide
  have h12096_12128 : maskChunk 12096 32 =
      StrongPackedBucketN12A3AlignedShard094.missing12096_12128 := by decide
  have h12128_12160 : maskChunk 12128 32 =
      StrongPackedBucketN12A3AlignedShard094.missing12128_12160 := by decide
  have h12032_12096 : maskChunk 12032 64 =
      StrongPackedBucketN12A3AlignedShard094.missing12032_12096 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h12032_12064, h12064_12096]
    rfl
  have h12096_12160 : maskChunk 12096 64 =
      StrongPackedBucketN12A3AlignedShard094.missing12096_12160 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h12096_12128, h12128_12160]
    rfl
  have h12032_12160 : maskChunk 12032 128 =
      StrongPackedBucketN12A3AlignedShard094.missing12032_12160 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h12032_12096, h12096_12160]
    rfl
  exact h12032_12160

private theorem shardMask95 : maskChunk 12160 128 =
    StrongPackedBucketN12A3AlignedShard095.missing := by
  have h12160_12192 : maskChunk 12160 32 =
      StrongPackedBucketN12A3AlignedShard095.missing12160_12192 := by decide
  have h12192_12224 : maskChunk 12192 32 =
      StrongPackedBucketN12A3AlignedShard095.missing12192_12224 := by decide
  have h12224_12256 : maskChunk 12224 32 =
      StrongPackedBucketN12A3AlignedShard095.missing12224_12256 := by decide
  have h12256_12288 : maskChunk 12256 32 =
      StrongPackedBucketN12A3AlignedShard095.missing12256_12288 := by decide
  have h12160_12224 : maskChunk 12160 64 =
      StrongPackedBucketN12A3AlignedShard095.missing12160_12224 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h12160_12192, h12192_12224]
    rfl
  have h12224_12288 : maskChunk 12224 64 =
      StrongPackedBucketN12A3AlignedShard095.missing12224_12288 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h12224_12256, h12256_12288]
    rfl
  have h12160_12288 : maskChunk 12160 128 =
      StrongPackedBucketN12A3AlignedShard095.missing12160_12288 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h12160_12224, h12224_12288]
    rfl
  exact h12160_12288

private theorem shardMask96 : maskChunk 12288 128 =
    StrongPackedBucketN12A3AlignedShard096.missing := by
  have h12288_12320 : maskChunk 12288 32 =
      StrongPackedBucketN12A3AlignedShard096.missing12288_12320 := by decide
  have h12320_12352 : maskChunk 12320 32 =
      StrongPackedBucketN12A3AlignedShard096.missing12320_12352 := by decide
  have h12352_12384 : maskChunk 12352 32 =
      StrongPackedBucketN12A3AlignedShard096.missing12352_12384 := by decide
  have h12384_12416 : maskChunk 12384 32 =
      StrongPackedBucketN12A3AlignedShard096.missing12384_12416 := by decide
  have h12288_12352 : maskChunk 12288 64 =
      StrongPackedBucketN12A3AlignedShard096.missing12288_12352 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h12288_12320, h12320_12352]
    rfl
  have h12352_12416 : maskChunk 12352 64 =
      StrongPackedBucketN12A3AlignedShard096.missing12352_12416 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h12352_12384, h12384_12416]
    rfl
  have h12288_12416 : maskChunk 12288 128 =
      StrongPackedBucketN12A3AlignedShard096.missing12288_12416 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h12288_12352, h12352_12416]
    rfl
  exact h12288_12416

private theorem shardMask97 : maskChunk 12416 128 =
    StrongPackedBucketN12A3AlignedShard097.missing := by
  have h12416_12448 : maskChunk 12416 32 =
      StrongPackedBucketN12A3AlignedShard097.missing12416_12448 := by decide
  have h12448_12480 : maskChunk 12448 32 =
      StrongPackedBucketN12A3AlignedShard097.missing12448_12480 := by decide
  have h12480_12512 : maskChunk 12480 32 =
      StrongPackedBucketN12A3AlignedShard097.missing12480_12512 := by decide
  have h12512_12544 : maskChunk 12512 32 =
      StrongPackedBucketN12A3AlignedShard097.missing12512_12544 := by decide
  have h12416_12480 : maskChunk 12416 64 =
      StrongPackedBucketN12A3AlignedShard097.missing12416_12480 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h12416_12448, h12448_12480]
    rfl
  have h12480_12544 : maskChunk 12480 64 =
      StrongPackedBucketN12A3AlignedShard097.missing12480_12544 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h12480_12512, h12512_12544]
    rfl
  have h12416_12544 : maskChunk 12416 128 =
      StrongPackedBucketN12A3AlignedShard097.missing12416_12544 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h12416_12480, h12480_12544]
    rfl
  exact h12416_12544

private theorem shardMask98 : maskChunk 12544 128 =
    StrongPackedBucketN12A3AlignedShard098.missing := by
  have h12544_12576 : maskChunk 12544 32 =
      StrongPackedBucketN12A3AlignedShard098.missing12544_12576 := by decide
  have h12576_12608 : maskChunk 12576 32 =
      StrongPackedBucketN12A3AlignedShard098.missing12576_12608 := by decide
  have h12608_12640 : maskChunk 12608 32 =
      StrongPackedBucketN12A3AlignedShard098.missing12608_12640 := by decide
  have h12640_12672 : maskChunk 12640 32 =
      StrongPackedBucketN12A3AlignedShard098.missing12640_12672 := by decide
  have h12544_12608 : maskChunk 12544 64 =
      StrongPackedBucketN12A3AlignedShard098.missing12544_12608 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h12544_12576, h12576_12608]
    rfl
  have h12608_12672 : maskChunk 12608 64 =
      StrongPackedBucketN12A3AlignedShard098.missing12608_12672 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h12608_12640, h12640_12672]
    rfl
  have h12544_12672 : maskChunk 12544 128 =
      StrongPackedBucketN12A3AlignedShard098.missing12544_12672 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h12544_12608, h12608_12672]
    rfl
  exact h12544_12672

private theorem shardMask99 : maskChunk 12672 91 =
    StrongPackedBucketN12A3AlignedShard099.missing := by
  have h12672_12694 : maskChunk 12672 22 =
      StrongPackedBucketN12A3AlignedShard099.missing12672_12694 := by decide
  have h12694_12717 : maskChunk 12694 23 =
      StrongPackedBucketN12A3AlignedShard099.missing12694_12717 := by decide
  have h12717_12740 : maskChunk 12717 23 =
      StrongPackedBucketN12A3AlignedShard099.missing12717_12740 := by decide
  have h12740_12763 : maskChunk 12740 23 =
      StrongPackedBucketN12A3AlignedShard099.missing12740_12763 := by decide
  have h12672_12717 : maskChunk 12672 45 =
      StrongPackedBucketN12A3AlignedShard099.missing12672_12717 := by
    rw [show 45 = 22 + 23 by omega,
      maskChunk_add, h12672_12694, h12694_12717]
    rfl
  have h12717_12763 : maskChunk 12717 46 =
      StrongPackedBucketN12A3AlignedShard099.missing12717_12763 := by
    rw [show 46 = 23 + 23 by omega,
      maskChunk_add, h12717_12740, h12740_12763]
    rfl
  have h12672_12763 : maskChunk 12672 91 =
      StrongPackedBucketN12A3AlignedShard099.missing12672_12763 := by
    rw [show 91 = 45 + 46 by omega,
      maskChunk_add, h12672_12717, h12717_12763]
    rfl
  exact h12672_12763

private theorem aggregateMask0_1 : maskChunk 0 128 =
    StrongPackedBucketN12A3Aligned.missing0_1 := by
  exact shardMask0

private theorem aggregateMask1_2 : maskChunk 128 128 =
    StrongPackedBucketN12A3Aligned.missing1_2 := by
  exact shardMask1

private theorem aggregateMask2_3 : maskChunk 256 128 =
    StrongPackedBucketN12A3Aligned.missing2_3 := by
  exact shardMask2

private theorem aggregateMask1_3 : maskChunk 128 256 =
    StrongPackedBucketN12A3Aligned.missing1_3 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask1_2, aggregateMask2_3]
  rfl

private theorem aggregateMask0_3 : maskChunk 0 384 =
    StrongPackedBucketN12A3Aligned.missing0_3 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask0_1, aggregateMask1_3]
  rfl

private theorem aggregateMask3_4 : maskChunk 384 128 =
    StrongPackedBucketN12A3Aligned.missing3_4 := by
  exact shardMask3

private theorem aggregateMask4_5 : maskChunk 512 128 =
    StrongPackedBucketN12A3Aligned.missing4_5 := by
  exact shardMask4

private theorem aggregateMask5_6 : maskChunk 640 128 =
    StrongPackedBucketN12A3Aligned.missing5_6 := by
  exact shardMask5

private theorem aggregateMask4_6 : maskChunk 512 256 =
    StrongPackedBucketN12A3Aligned.missing4_6 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask4_5, aggregateMask5_6]
  rfl

private theorem aggregateMask3_6 : maskChunk 384 384 =
    StrongPackedBucketN12A3Aligned.missing3_6 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask3_4, aggregateMask4_6]
  rfl

private theorem aggregateMask0_6 : maskChunk 0 768 =
    StrongPackedBucketN12A3Aligned.missing0_6 := by
  rw [show 768 = 384 + 384 by omega,
    maskChunk_add, aggregateMask0_3, aggregateMask3_6]
  rfl

private theorem aggregateMask6_7 : maskChunk 768 128 =
    StrongPackedBucketN12A3Aligned.missing6_7 := by
  exact shardMask6

private theorem aggregateMask7_8 : maskChunk 896 128 =
    StrongPackedBucketN12A3Aligned.missing7_8 := by
  exact shardMask7

private theorem aggregateMask8_9 : maskChunk 1024 128 =
    StrongPackedBucketN12A3Aligned.missing8_9 := by
  exact shardMask8

private theorem aggregateMask7_9 : maskChunk 896 256 =
    StrongPackedBucketN12A3Aligned.missing7_9 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask7_8, aggregateMask8_9]
  rfl

private theorem aggregateMask6_9 : maskChunk 768 384 =
    StrongPackedBucketN12A3Aligned.missing6_9 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask6_7, aggregateMask7_9]
  rfl

private theorem aggregateMask9_10 : maskChunk 1152 128 =
    StrongPackedBucketN12A3Aligned.missing9_10 := by
  exact shardMask9

private theorem aggregateMask10_11 : maskChunk 1280 128 =
    StrongPackedBucketN12A3Aligned.missing10_11 := by
  exact shardMask10

private theorem aggregateMask11_12 : maskChunk 1408 128 =
    StrongPackedBucketN12A3Aligned.missing11_12 := by
  exact shardMask11

private theorem aggregateMask10_12 : maskChunk 1280 256 =
    StrongPackedBucketN12A3Aligned.missing10_12 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask10_11, aggregateMask11_12]
  rfl

private theorem aggregateMask9_12 : maskChunk 1152 384 =
    StrongPackedBucketN12A3Aligned.missing9_12 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask9_10, aggregateMask10_12]
  rfl

private theorem aggregateMask6_12 : maskChunk 768 768 =
    StrongPackedBucketN12A3Aligned.missing6_12 := by
  rw [show 768 = 384 + 384 by omega,
    maskChunk_add, aggregateMask6_9, aggregateMask9_12]
  rfl

private theorem aggregateMask0_12 : maskChunk 0 1536 =
    StrongPackedBucketN12A3Aligned.missing0_12 := by
  rw [show 1536 = 768 + 768 by omega,
    maskChunk_add, aggregateMask0_6, aggregateMask6_12]
  rfl

private theorem aggregateMask12_13 : maskChunk 1536 128 =
    StrongPackedBucketN12A3Aligned.missing12_13 := by
  exact shardMask12

private theorem aggregateMask13_14 : maskChunk 1664 128 =
    StrongPackedBucketN12A3Aligned.missing13_14 := by
  exact shardMask13

private theorem aggregateMask14_15 : maskChunk 1792 128 =
    StrongPackedBucketN12A3Aligned.missing14_15 := by
  exact shardMask14

private theorem aggregateMask13_15 : maskChunk 1664 256 =
    StrongPackedBucketN12A3Aligned.missing13_15 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask13_14, aggregateMask14_15]
  rfl

private theorem aggregateMask12_15 : maskChunk 1536 384 =
    StrongPackedBucketN12A3Aligned.missing12_15 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask12_13, aggregateMask13_15]
  rfl

private theorem aggregateMask15_16 : maskChunk 1920 128 =
    StrongPackedBucketN12A3Aligned.missing15_16 := by
  exact shardMask15

private theorem aggregateMask16_17 : maskChunk 2048 128 =
    StrongPackedBucketN12A3Aligned.missing16_17 := by
  exact shardMask16

private theorem aggregateMask17_18 : maskChunk 2176 128 =
    StrongPackedBucketN12A3Aligned.missing17_18 := by
  exact shardMask17

private theorem aggregateMask16_18 : maskChunk 2048 256 =
    StrongPackedBucketN12A3Aligned.missing16_18 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask16_17, aggregateMask17_18]
  rfl

private theorem aggregateMask15_18 : maskChunk 1920 384 =
    StrongPackedBucketN12A3Aligned.missing15_18 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask15_16, aggregateMask16_18]
  rfl

private theorem aggregateMask12_18 : maskChunk 1536 768 =
    StrongPackedBucketN12A3Aligned.missing12_18 := by
  rw [show 768 = 384 + 384 by omega,
    maskChunk_add, aggregateMask12_15, aggregateMask15_18]
  rfl

private theorem aggregateMask18_19 : maskChunk 2304 128 =
    StrongPackedBucketN12A3Aligned.missing18_19 := by
  exact shardMask18

private theorem aggregateMask19_20 : maskChunk 2432 128 =
    StrongPackedBucketN12A3Aligned.missing19_20 := by
  exact shardMask19

private theorem aggregateMask20_21 : maskChunk 2560 128 =
    StrongPackedBucketN12A3Aligned.missing20_21 := by
  exact shardMask20

private theorem aggregateMask19_21 : maskChunk 2432 256 =
    StrongPackedBucketN12A3Aligned.missing19_21 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask19_20, aggregateMask20_21]
  rfl

private theorem aggregateMask18_21 : maskChunk 2304 384 =
    StrongPackedBucketN12A3Aligned.missing18_21 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask18_19, aggregateMask19_21]
  rfl

private theorem aggregateMask21_22 : maskChunk 2688 128 =
    StrongPackedBucketN12A3Aligned.missing21_22 := by
  exact shardMask21

private theorem aggregateMask22_23 : maskChunk 2816 128 =
    StrongPackedBucketN12A3Aligned.missing22_23 := by
  exact shardMask22

private theorem aggregateMask21_23 : maskChunk 2688 256 =
    StrongPackedBucketN12A3Aligned.missing21_23 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask21_22, aggregateMask22_23]
  rfl

private theorem aggregateMask23_24 : maskChunk 2944 128 =
    StrongPackedBucketN12A3Aligned.missing23_24 := by
  exact shardMask23

private theorem aggregateMask24_25 : maskChunk 3072 128 =
    StrongPackedBucketN12A3Aligned.missing24_25 := by
  exact shardMask24

private theorem aggregateMask23_25 : maskChunk 2944 256 =
    StrongPackedBucketN12A3Aligned.missing23_25 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask23_24, aggregateMask24_25]
  rfl

private theorem aggregateMask21_25 : maskChunk 2688 512 =
    StrongPackedBucketN12A3Aligned.missing21_25 := by
  rw [show 512 = 256 + 256 by omega,
    maskChunk_add, aggregateMask21_23, aggregateMask23_25]
  rfl

private theorem aggregateMask18_25 : maskChunk 2304 896 =
    StrongPackedBucketN12A3Aligned.missing18_25 := by
  rw [show 896 = 384 + 512 by omega,
    maskChunk_add, aggregateMask18_21, aggregateMask21_25]
  rfl

private theorem aggregateMask12_25 : maskChunk 1536 1664 =
    StrongPackedBucketN12A3Aligned.missing12_25 := by
  rw [show 1664 = 768 + 896 by omega,
    maskChunk_add, aggregateMask12_18, aggregateMask18_25]
  rfl

private theorem aggregateMask0_25 : maskChunk 0 3200 =
    StrongPackedBucketN12A3Aligned.missing0_25 := by
  rw [show 3200 = 1536 + 1664 by omega,
    maskChunk_add, aggregateMask0_12, aggregateMask12_25]
  rfl

private theorem aggregateMask25_26 : maskChunk 3200 128 =
    StrongPackedBucketN12A3Aligned.missing25_26 := by
  exact shardMask25

private theorem aggregateMask26_27 : maskChunk 3328 128 =
    StrongPackedBucketN12A3Aligned.missing26_27 := by
  exact shardMask26

private theorem aggregateMask27_28 : maskChunk 3456 128 =
    StrongPackedBucketN12A3Aligned.missing27_28 := by
  exact shardMask27

private theorem aggregateMask26_28 : maskChunk 3328 256 =
    StrongPackedBucketN12A3Aligned.missing26_28 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask26_27, aggregateMask27_28]
  rfl

private theorem aggregateMask25_28 : maskChunk 3200 384 =
    StrongPackedBucketN12A3Aligned.missing25_28 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask25_26, aggregateMask26_28]
  rfl

private theorem aggregateMask28_29 : maskChunk 3584 128 =
    StrongPackedBucketN12A3Aligned.missing28_29 := by
  exact shardMask28

private theorem aggregateMask29_30 : maskChunk 3712 128 =
    StrongPackedBucketN12A3Aligned.missing29_30 := by
  exact shardMask29

private theorem aggregateMask30_31 : maskChunk 3840 128 =
    StrongPackedBucketN12A3Aligned.missing30_31 := by
  exact shardMask30

private theorem aggregateMask29_31 : maskChunk 3712 256 =
    StrongPackedBucketN12A3Aligned.missing29_31 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask29_30, aggregateMask30_31]
  rfl

private theorem aggregateMask28_31 : maskChunk 3584 384 =
    StrongPackedBucketN12A3Aligned.missing28_31 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask28_29, aggregateMask29_31]
  rfl

private theorem aggregateMask25_31 : maskChunk 3200 768 =
    StrongPackedBucketN12A3Aligned.missing25_31 := by
  rw [show 768 = 384 + 384 by omega,
    maskChunk_add, aggregateMask25_28, aggregateMask28_31]
  rfl

private theorem aggregateMask31_32 : maskChunk 3968 128 =
    StrongPackedBucketN12A3Aligned.missing31_32 := by
  exact shardMask31

private theorem aggregateMask32_33 : maskChunk 4096 128 =
    StrongPackedBucketN12A3Aligned.missing32_33 := by
  exact shardMask32

private theorem aggregateMask33_34 : maskChunk 4224 128 =
    StrongPackedBucketN12A3Aligned.missing33_34 := by
  exact shardMask33

private theorem aggregateMask32_34 : maskChunk 4096 256 =
    StrongPackedBucketN12A3Aligned.missing32_34 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask32_33, aggregateMask33_34]
  rfl

private theorem aggregateMask31_34 : maskChunk 3968 384 =
    StrongPackedBucketN12A3Aligned.missing31_34 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask31_32, aggregateMask32_34]
  rfl

private theorem aggregateMask34_35 : maskChunk 4352 128 =
    StrongPackedBucketN12A3Aligned.missing34_35 := by
  exact shardMask34

private theorem aggregateMask35_36 : maskChunk 4480 128 =
    StrongPackedBucketN12A3Aligned.missing35_36 := by
  exact shardMask35

private theorem aggregateMask36_37 : maskChunk 4608 128 =
    StrongPackedBucketN12A3Aligned.missing36_37 := by
  exact shardMask36

private theorem aggregateMask35_37 : maskChunk 4480 256 =
    StrongPackedBucketN12A3Aligned.missing35_37 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask35_36, aggregateMask36_37]
  rfl

private theorem aggregateMask34_37 : maskChunk 4352 384 =
    StrongPackedBucketN12A3Aligned.missing34_37 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask34_35, aggregateMask35_37]
  rfl

private theorem aggregateMask31_37 : maskChunk 3968 768 =
    StrongPackedBucketN12A3Aligned.missing31_37 := by
  rw [show 768 = 384 + 384 by omega,
    maskChunk_add, aggregateMask31_34, aggregateMask34_37]
  rfl

private theorem aggregateMask25_37 : maskChunk 3200 1536 =
    StrongPackedBucketN12A3Aligned.missing25_37 := by
  rw [show 1536 = 768 + 768 by omega,
    maskChunk_add, aggregateMask25_31, aggregateMask31_37]
  rfl

private theorem aggregateMask37_38 : maskChunk 4736 128 =
    StrongPackedBucketN12A3Aligned.missing37_38 := by
  exact shardMask37

private theorem aggregateMask38_39 : maskChunk 4864 128 =
    StrongPackedBucketN12A3Aligned.missing38_39 := by
  exact shardMask38

private theorem aggregateMask39_40 : maskChunk 4992 128 =
    StrongPackedBucketN12A3Aligned.missing39_40 := by
  exact shardMask39

private theorem aggregateMask38_40 : maskChunk 4864 256 =
    StrongPackedBucketN12A3Aligned.missing38_40 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask38_39, aggregateMask39_40]
  rfl

private theorem aggregateMask37_40 : maskChunk 4736 384 =
    StrongPackedBucketN12A3Aligned.missing37_40 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask37_38, aggregateMask38_40]
  rfl

private theorem aggregateMask40_41 : maskChunk 5120 128 =
    StrongPackedBucketN12A3Aligned.missing40_41 := by
  exact shardMask40

private theorem aggregateMask41_42 : maskChunk 5248 128 =
    StrongPackedBucketN12A3Aligned.missing41_42 := by
  exact shardMask41

private theorem aggregateMask42_43 : maskChunk 5376 128 =
    StrongPackedBucketN12A3Aligned.missing42_43 := by
  exact shardMask42

private theorem aggregateMask41_43 : maskChunk 5248 256 =
    StrongPackedBucketN12A3Aligned.missing41_43 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask41_42, aggregateMask42_43]
  rfl

private theorem aggregateMask40_43 : maskChunk 5120 384 =
    StrongPackedBucketN12A3Aligned.missing40_43 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask40_41, aggregateMask41_43]
  rfl

private theorem aggregateMask37_43 : maskChunk 4736 768 =
    StrongPackedBucketN12A3Aligned.missing37_43 := by
  rw [show 768 = 384 + 384 by omega,
    maskChunk_add, aggregateMask37_40, aggregateMask40_43]
  rfl

private theorem aggregateMask43_44 : maskChunk 5504 128 =
    StrongPackedBucketN12A3Aligned.missing43_44 := by
  exact shardMask43

private theorem aggregateMask44_45 : maskChunk 5632 128 =
    StrongPackedBucketN12A3Aligned.missing44_45 := by
  exact shardMask44

private theorem aggregateMask45_46 : maskChunk 5760 128 =
    StrongPackedBucketN12A3Aligned.missing45_46 := by
  exact shardMask45

private theorem aggregateMask44_46 : maskChunk 5632 256 =
    StrongPackedBucketN12A3Aligned.missing44_46 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask44_45, aggregateMask45_46]
  rfl

private theorem aggregateMask43_46 : maskChunk 5504 384 =
    StrongPackedBucketN12A3Aligned.missing43_46 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask43_44, aggregateMask44_46]
  rfl

private theorem aggregateMask46_47 : maskChunk 5888 128 =
    StrongPackedBucketN12A3Aligned.missing46_47 := by
  exact shardMask46

private theorem aggregateMask47_48 : maskChunk 6016 128 =
    StrongPackedBucketN12A3Aligned.missing47_48 := by
  exact shardMask47

private theorem aggregateMask46_48 : maskChunk 5888 256 =
    StrongPackedBucketN12A3Aligned.missing46_48 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask46_47, aggregateMask47_48]
  rfl

private theorem aggregateMask48_49 : maskChunk 6144 128 =
    StrongPackedBucketN12A3Aligned.missing48_49 := by
  exact shardMask48

private theorem aggregateMask49_50 : maskChunk 6272 128 =
    StrongPackedBucketN12A3Aligned.missing49_50 := by
  exact shardMask49

private theorem aggregateMask48_50 : maskChunk 6144 256 =
    StrongPackedBucketN12A3Aligned.missing48_50 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask48_49, aggregateMask49_50]
  rfl

private theorem aggregateMask46_50 : maskChunk 5888 512 =
    StrongPackedBucketN12A3Aligned.missing46_50 := by
  rw [show 512 = 256 + 256 by omega,
    maskChunk_add, aggregateMask46_48, aggregateMask48_50]
  rfl

private theorem aggregateMask43_50 : maskChunk 5504 896 =
    StrongPackedBucketN12A3Aligned.missing43_50 := by
  rw [show 896 = 384 + 512 by omega,
    maskChunk_add, aggregateMask43_46, aggregateMask46_50]
  rfl

private theorem aggregateMask37_50 : maskChunk 4736 1664 =
    StrongPackedBucketN12A3Aligned.missing37_50 := by
  rw [show 1664 = 768 + 896 by omega,
    maskChunk_add, aggregateMask37_43, aggregateMask43_50]
  rfl

private theorem aggregateMask25_50 : maskChunk 3200 3200 =
    StrongPackedBucketN12A3Aligned.missing25_50 := by
  rw [show 3200 = 1536 + 1664 by omega,
    maskChunk_add, aggregateMask25_37, aggregateMask37_50]
  rfl

private theorem aggregateMask0_50 : maskChunk 0 6400 =
    StrongPackedBucketN12A3Aligned.missing0_50 := by
  rw [show 6400 = 3200 + 3200 by omega,
    maskChunk_add, aggregateMask0_25, aggregateMask25_50]
  rfl

private theorem aggregateMask50_51 : maskChunk 6400 128 =
    StrongPackedBucketN12A3Aligned.missing50_51 := by
  exact shardMask50

private theorem aggregateMask51_52 : maskChunk 6528 128 =
    StrongPackedBucketN12A3Aligned.missing51_52 := by
  exact shardMask51

private theorem aggregateMask52_53 : maskChunk 6656 128 =
    StrongPackedBucketN12A3Aligned.missing52_53 := by
  exact shardMask52

private theorem aggregateMask51_53 : maskChunk 6528 256 =
    StrongPackedBucketN12A3Aligned.missing51_53 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask51_52, aggregateMask52_53]
  rfl

private theorem aggregateMask50_53 : maskChunk 6400 384 =
    StrongPackedBucketN12A3Aligned.missing50_53 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask50_51, aggregateMask51_53]
  rfl

private theorem aggregateMask53_54 : maskChunk 6784 128 =
    StrongPackedBucketN12A3Aligned.missing53_54 := by
  exact shardMask53

private theorem aggregateMask54_55 : maskChunk 6912 128 =
    StrongPackedBucketN12A3Aligned.missing54_55 := by
  exact shardMask54

private theorem aggregateMask55_56 : maskChunk 7040 128 =
    StrongPackedBucketN12A3Aligned.missing55_56 := by
  exact shardMask55

private theorem aggregateMask54_56 : maskChunk 6912 256 =
    StrongPackedBucketN12A3Aligned.missing54_56 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask54_55, aggregateMask55_56]
  rfl

private theorem aggregateMask53_56 : maskChunk 6784 384 =
    StrongPackedBucketN12A3Aligned.missing53_56 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask53_54, aggregateMask54_56]
  rfl

private theorem aggregateMask50_56 : maskChunk 6400 768 =
    StrongPackedBucketN12A3Aligned.missing50_56 := by
  rw [show 768 = 384 + 384 by omega,
    maskChunk_add, aggregateMask50_53, aggregateMask53_56]
  rfl

private theorem aggregateMask56_57 : maskChunk 7168 128 =
    StrongPackedBucketN12A3Aligned.missing56_57 := by
  exact shardMask56

private theorem aggregateMask57_58 : maskChunk 7296 128 =
    StrongPackedBucketN12A3Aligned.missing57_58 := by
  exact shardMask57

private theorem aggregateMask58_59 : maskChunk 7424 128 =
    StrongPackedBucketN12A3Aligned.missing58_59 := by
  exact shardMask58

private theorem aggregateMask57_59 : maskChunk 7296 256 =
    StrongPackedBucketN12A3Aligned.missing57_59 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask57_58, aggregateMask58_59]
  rfl

private theorem aggregateMask56_59 : maskChunk 7168 384 =
    StrongPackedBucketN12A3Aligned.missing56_59 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask56_57, aggregateMask57_59]
  rfl

private theorem aggregateMask59_60 : maskChunk 7552 128 =
    StrongPackedBucketN12A3Aligned.missing59_60 := by
  exact shardMask59

private theorem aggregateMask60_61 : maskChunk 7680 128 =
    StrongPackedBucketN12A3Aligned.missing60_61 := by
  exact shardMask60

private theorem aggregateMask61_62 : maskChunk 7808 128 =
    StrongPackedBucketN12A3Aligned.missing61_62 := by
  exact shardMask61

private theorem aggregateMask60_62 : maskChunk 7680 256 =
    StrongPackedBucketN12A3Aligned.missing60_62 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask60_61, aggregateMask61_62]
  rfl

private theorem aggregateMask59_62 : maskChunk 7552 384 =
    StrongPackedBucketN12A3Aligned.missing59_62 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask59_60, aggregateMask60_62]
  rfl

private theorem aggregateMask56_62 : maskChunk 7168 768 =
    StrongPackedBucketN12A3Aligned.missing56_62 := by
  rw [show 768 = 384 + 384 by omega,
    maskChunk_add, aggregateMask56_59, aggregateMask59_62]
  rfl

private theorem aggregateMask50_62 : maskChunk 6400 1536 =
    StrongPackedBucketN12A3Aligned.missing50_62 := by
  rw [show 1536 = 768 + 768 by omega,
    maskChunk_add, aggregateMask50_56, aggregateMask56_62]
  rfl

private theorem aggregateMask62_63 : maskChunk 7936 128 =
    StrongPackedBucketN12A3Aligned.missing62_63 := by
  exact shardMask62

private theorem aggregateMask63_64 : maskChunk 8064 128 =
    StrongPackedBucketN12A3Aligned.missing63_64 := by
  exact shardMask63

private theorem aggregateMask64_65 : maskChunk 8192 128 =
    StrongPackedBucketN12A3Aligned.missing64_65 := by
  exact shardMask64

private theorem aggregateMask63_65 : maskChunk 8064 256 =
    StrongPackedBucketN12A3Aligned.missing63_65 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask63_64, aggregateMask64_65]
  rfl

private theorem aggregateMask62_65 : maskChunk 7936 384 =
    StrongPackedBucketN12A3Aligned.missing62_65 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask62_63, aggregateMask63_65]
  rfl

private theorem aggregateMask65_66 : maskChunk 8320 128 =
    StrongPackedBucketN12A3Aligned.missing65_66 := by
  exact shardMask65

private theorem aggregateMask66_67 : maskChunk 8448 128 =
    StrongPackedBucketN12A3Aligned.missing66_67 := by
  exact shardMask66

private theorem aggregateMask67_68 : maskChunk 8576 128 =
    StrongPackedBucketN12A3Aligned.missing67_68 := by
  exact shardMask67

private theorem aggregateMask66_68 : maskChunk 8448 256 =
    StrongPackedBucketN12A3Aligned.missing66_68 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask66_67, aggregateMask67_68]
  rfl

private theorem aggregateMask65_68 : maskChunk 8320 384 =
    StrongPackedBucketN12A3Aligned.missing65_68 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask65_66, aggregateMask66_68]
  rfl

private theorem aggregateMask62_68 : maskChunk 7936 768 =
    StrongPackedBucketN12A3Aligned.missing62_68 := by
  rw [show 768 = 384 + 384 by omega,
    maskChunk_add, aggregateMask62_65, aggregateMask65_68]
  rfl

private theorem aggregateMask68_69 : maskChunk 8704 128 =
    StrongPackedBucketN12A3Aligned.missing68_69 := by
  exact shardMask68

private theorem aggregateMask69_70 : maskChunk 8832 128 =
    StrongPackedBucketN12A3Aligned.missing69_70 := by
  exact shardMask69

private theorem aggregateMask70_71 : maskChunk 8960 128 =
    StrongPackedBucketN12A3Aligned.missing70_71 := by
  exact shardMask70

private theorem aggregateMask69_71 : maskChunk 8832 256 =
    StrongPackedBucketN12A3Aligned.missing69_71 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask69_70, aggregateMask70_71]
  rfl

private theorem aggregateMask68_71 : maskChunk 8704 384 =
    StrongPackedBucketN12A3Aligned.missing68_71 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask68_69, aggregateMask69_71]
  rfl

private theorem aggregateMask71_72 : maskChunk 9088 128 =
    StrongPackedBucketN12A3Aligned.missing71_72 := by
  exact shardMask71

private theorem aggregateMask72_73 : maskChunk 9216 128 =
    StrongPackedBucketN12A3Aligned.missing72_73 := by
  exact shardMask72

private theorem aggregateMask71_73 : maskChunk 9088 256 =
    StrongPackedBucketN12A3Aligned.missing71_73 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask71_72, aggregateMask72_73]
  rfl

private theorem aggregateMask73_74 : maskChunk 9344 128 =
    StrongPackedBucketN12A3Aligned.missing73_74 := by
  exact shardMask73

private theorem aggregateMask74_75 : maskChunk 9472 128 =
    StrongPackedBucketN12A3Aligned.missing74_75 := by
  exact shardMask74

private theorem aggregateMask73_75 : maskChunk 9344 256 =
    StrongPackedBucketN12A3Aligned.missing73_75 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask73_74, aggregateMask74_75]
  rfl

private theorem aggregateMask71_75 : maskChunk 9088 512 =
    StrongPackedBucketN12A3Aligned.missing71_75 := by
  rw [show 512 = 256 + 256 by omega,
    maskChunk_add, aggregateMask71_73, aggregateMask73_75]
  rfl

private theorem aggregateMask68_75 : maskChunk 8704 896 =
    StrongPackedBucketN12A3Aligned.missing68_75 := by
  rw [show 896 = 384 + 512 by omega,
    maskChunk_add, aggregateMask68_71, aggregateMask71_75]
  rfl

private theorem aggregateMask62_75 : maskChunk 7936 1664 =
    StrongPackedBucketN12A3Aligned.missing62_75 := by
  rw [show 1664 = 768 + 896 by omega,
    maskChunk_add, aggregateMask62_68, aggregateMask68_75]
  rfl

private theorem aggregateMask50_75 : maskChunk 6400 3200 =
    StrongPackedBucketN12A3Aligned.missing50_75 := by
  rw [show 3200 = 1536 + 1664 by omega,
    maskChunk_add, aggregateMask50_62, aggregateMask62_75]
  rfl

private theorem aggregateMask75_76 : maskChunk 9600 128 =
    StrongPackedBucketN12A3Aligned.missing75_76 := by
  exact shardMask75

private theorem aggregateMask76_77 : maskChunk 9728 128 =
    StrongPackedBucketN12A3Aligned.missing76_77 := by
  exact shardMask76

private theorem aggregateMask77_78 : maskChunk 9856 128 =
    StrongPackedBucketN12A3Aligned.missing77_78 := by
  exact shardMask77

private theorem aggregateMask76_78 : maskChunk 9728 256 =
    StrongPackedBucketN12A3Aligned.missing76_78 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask76_77, aggregateMask77_78]
  rfl

private theorem aggregateMask75_78 : maskChunk 9600 384 =
    StrongPackedBucketN12A3Aligned.missing75_78 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask75_76, aggregateMask76_78]
  rfl

private theorem aggregateMask78_79 : maskChunk 9984 128 =
    StrongPackedBucketN12A3Aligned.missing78_79 := by
  exact shardMask78

private theorem aggregateMask79_80 : maskChunk 10112 128 =
    StrongPackedBucketN12A3Aligned.missing79_80 := by
  exact shardMask79

private theorem aggregateMask80_81 : maskChunk 10240 128 =
    StrongPackedBucketN12A3Aligned.missing80_81 := by
  exact shardMask80

private theorem aggregateMask79_81 : maskChunk 10112 256 =
    StrongPackedBucketN12A3Aligned.missing79_81 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask79_80, aggregateMask80_81]
  rfl

private theorem aggregateMask78_81 : maskChunk 9984 384 =
    StrongPackedBucketN12A3Aligned.missing78_81 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask78_79, aggregateMask79_81]
  rfl

private theorem aggregateMask75_81 : maskChunk 9600 768 =
    StrongPackedBucketN12A3Aligned.missing75_81 := by
  rw [show 768 = 384 + 384 by omega,
    maskChunk_add, aggregateMask75_78, aggregateMask78_81]
  rfl

private theorem aggregateMask81_82 : maskChunk 10368 128 =
    StrongPackedBucketN12A3Aligned.missing81_82 := by
  exact shardMask81

private theorem aggregateMask82_83 : maskChunk 10496 128 =
    StrongPackedBucketN12A3Aligned.missing82_83 := by
  exact shardMask82

private theorem aggregateMask83_84 : maskChunk 10624 128 =
    StrongPackedBucketN12A3Aligned.missing83_84 := by
  exact shardMask83

private theorem aggregateMask82_84 : maskChunk 10496 256 =
    StrongPackedBucketN12A3Aligned.missing82_84 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask82_83, aggregateMask83_84]
  rfl

private theorem aggregateMask81_84 : maskChunk 10368 384 =
    StrongPackedBucketN12A3Aligned.missing81_84 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask81_82, aggregateMask82_84]
  rfl

private theorem aggregateMask84_85 : maskChunk 10752 128 =
    StrongPackedBucketN12A3Aligned.missing84_85 := by
  exact shardMask84

private theorem aggregateMask85_86 : maskChunk 10880 128 =
    StrongPackedBucketN12A3Aligned.missing85_86 := by
  exact shardMask85

private theorem aggregateMask86_87 : maskChunk 11008 128 =
    StrongPackedBucketN12A3Aligned.missing86_87 := by
  exact shardMask86

private theorem aggregateMask85_87 : maskChunk 10880 256 =
    StrongPackedBucketN12A3Aligned.missing85_87 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask85_86, aggregateMask86_87]
  rfl

private theorem aggregateMask84_87 : maskChunk 10752 384 =
    StrongPackedBucketN12A3Aligned.missing84_87 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask84_85, aggregateMask85_87]
  rfl

private theorem aggregateMask81_87 : maskChunk 10368 768 =
    StrongPackedBucketN12A3Aligned.missing81_87 := by
  rw [show 768 = 384 + 384 by omega,
    maskChunk_add, aggregateMask81_84, aggregateMask84_87]
  rfl

private theorem aggregateMask75_87 : maskChunk 9600 1536 =
    StrongPackedBucketN12A3Aligned.missing75_87 := by
  rw [show 1536 = 768 + 768 by omega,
    maskChunk_add, aggregateMask75_81, aggregateMask81_87]
  rfl

private theorem aggregateMask87_88 : maskChunk 11136 128 =
    StrongPackedBucketN12A3Aligned.missing87_88 := by
  exact shardMask87

private theorem aggregateMask88_89 : maskChunk 11264 128 =
    StrongPackedBucketN12A3Aligned.missing88_89 := by
  exact shardMask88

private theorem aggregateMask89_90 : maskChunk 11392 128 =
    StrongPackedBucketN12A3Aligned.missing89_90 := by
  exact shardMask89

private theorem aggregateMask88_90 : maskChunk 11264 256 =
    StrongPackedBucketN12A3Aligned.missing88_90 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask88_89, aggregateMask89_90]
  rfl

private theorem aggregateMask87_90 : maskChunk 11136 384 =
    StrongPackedBucketN12A3Aligned.missing87_90 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask87_88, aggregateMask88_90]
  rfl

private theorem aggregateMask90_91 : maskChunk 11520 128 =
    StrongPackedBucketN12A3Aligned.missing90_91 := by
  exact shardMask90

private theorem aggregateMask91_92 : maskChunk 11648 128 =
    StrongPackedBucketN12A3Aligned.missing91_92 := by
  exact shardMask91

private theorem aggregateMask92_93 : maskChunk 11776 128 =
    StrongPackedBucketN12A3Aligned.missing92_93 := by
  exact shardMask92

private theorem aggregateMask91_93 : maskChunk 11648 256 =
    StrongPackedBucketN12A3Aligned.missing91_93 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask91_92, aggregateMask92_93]
  rfl

private theorem aggregateMask90_93 : maskChunk 11520 384 =
    StrongPackedBucketN12A3Aligned.missing90_93 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask90_91, aggregateMask91_93]
  rfl

private theorem aggregateMask87_93 : maskChunk 11136 768 =
    StrongPackedBucketN12A3Aligned.missing87_93 := by
  rw [show 768 = 384 + 384 by omega,
    maskChunk_add, aggregateMask87_90, aggregateMask90_93]
  rfl

private theorem aggregateMask93_94 : maskChunk 11904 128 =
    StrongPackedBucketN12A3Aligned.missing93_94 := by
  exact shardMask93

private theorem aggregateMask94_95 : maskChunk 12032 128 =
    StrongPackedBucketN12A3Aligned.missing94_95 := by
  exact shardMask94

private theorem aggregateMask95_96 : maskChunk 12160 128 =
    StrongPackedBucketN12A3Aligned.missing95_96 := by
  exact shardMask95

private theorem aggregateMask94_96 : maskChunk 12032 256 =
    StrongPackedBucketN12A3Aligned.missing94_96 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask94_95, aggregateMask95_96]
  rfl

private theorem aggregateMask93_96 : maskChunk 11904 384 =
    StrongPackedBucketN12A3Aligned.missing93_96 := by
  rw [show 384 = 128 + 256 by omega,
    maskChunk_add, aggregateMask93_94, aggregateMask94_96]
  rfl

private theorem aggregateMask96_97 : maskChunk 12288 128 =
    StrongPackedBucketN12A3Aligned.missing96_97 := by
  exact shardMask96

private theorem aggregateMask97_98 : maskChunk 12416 128 =
    StrongPackedBucketN12A3Aligned.missing97_98 := by
  exact shardMask97

private theorem aggregateMask96_98 : maskChunk 12288 256 =
    StrongPackedBucketN12A3Aligned.missing96_98 := by
  rw [show 256 = 128 + 128 by omega,
    maskChunk_add, aggregateMask96_97, aggregateMask97_98]
  rfl

private theorem aggregateMask98_99 : maskChunk 12544 128 =
    StrongPackedBucketN12A3Aligned.missing98_99 := by
  exact shardMask98

private theorem aggregateMask99_100 : maskChunk 12672 91 =
    StrongPackedBucketN12A3Aligned.missing99_100 := by
  exact shardMask99

private theorem aggregateMask98_100 : maskChunk 12544 219 =
    StrongPackedBucketN12A3Aligned.missing98_100 := by
  rw [show 219 = 128 + 91 by omega,
    maskChunk_add, aggregateMask98_99, aggregateMask99_100]
  rfl

private theorem aggregateMask96_100 : maskChunk 12288 475 =
    StrongPackedBucketN12A3Aligned.missing96_100 := by
  rw [show 475 = 256 + 219 by omega,
    maskChunk_add, aggregateMask96_98, aggregateMask98_100]
  rfl

private theorem aggregateMask93_100 : maskChunk 11904 859 =
    StrongPackedBucketN12A3Aligned.missing93_100 := by
  rw [show 859 = 384 + 475 by omega,
    maskChunk_add, aggregateMask93_96, aggregateMask96_100]
  rfl

private theorem aggregateMask87_100 : maskChunk 11136 1627 =
    StrongPackedBucketN12A3Aligned.missing87_100 := by
  rw [show 1627 = 768 + 859 by omega,
    maskChunk_add, aggregateMask87_93, aggregateMask93_100]
  rfl

private theorem aggregateMask75_100 : maskChunk 9600 3163 =
    StrongPackedBucketN12A3Aligned.missing75_100 := by
  rw [show 3163 = 1536 + 1627 by omega,
    maskChunk_add, aggregateMask75_87, aggregateMask87_100]
  rfl

private theorem aggregateMask50_100 : maskChunk 6400 6363 =
    StrongPackedBucketN12A3Aligned.missing50_100 := by
  rw [show 6363 = 3200 + 3163 by omega,
    maskChunk_add, aggregateMask50_75, aggregateMask75_100]
  rfl

private theorem aggregateMask0_100 : maskChunk 0 12763 =
    StrongPackedBucketN12A3Aligned.missing0_100 := by
  rw [show 12763 = 6400 + 6363 by omega,
    maskChunk_add, aggregateMask0_50, aggregateMask50_100]
  rfl

theorem level11_toList_eq_missing :
    PackedExhaustionN12.level11.toArray.toList =
      StrongPackedBucketN12A3Aligned.missing := by
  calc
    PackedExhaustionN12.level11.toArray.toList =
        maskChunk 0 12763 := by
      exact level11_to_nativeMaskList.trans
        nativeMaskList_eq_maskChunk
    _ = StrongPackedBucketN12A3Aligned.missing := aggregateMask0_100

theorem alignedLevel11 :
    AlignedValid 12 3
      PackedExhaustionN12.level11.toArray.toList
      StrongPackedBucketN12A3Aligned.records := by
  rw [level11_toList_eq_missing]
  exact StrongPackedBucketN12A3Aligned.aligned

private lemma compl_edgeSet_ncard_eq_missingEdgeCount
    (G : SimpleGraph (Fin 12)) :
    Gᶜ.edgeSet.ncard = missingEdgeCount G := by
  classical
  exact Set.ncard_eq_toFinset_card' Gᶜ.edgeSet

theorem strongBase (G : SimpleGraph (Fin 12))
    (hmissing : missingEdgeCount G = 11) :
    HasStrongFractionalPacking G 3 := by
  have haligned :
      AlignedValid 12 3
        (PackedExhaustionN12Through11.data.level 11).toList
        StrongPackedBucketN12A3Aligned.records := by
    change AlignedValid 12 3
      PackedExhaustionN12.level11.toArray.toList
      StrongPackedBucketN12A3Aligned.records
    exact alignedLevel11
  have hcard : Gᶜ.edgeSet.ncard = 11 := by
    calc
      Gᶜ.edgeSet.ncard = missingEdgeCount G :=
        compl_edgeSet_ncard_eq_missingEdgeCount G
      _ = 11 := hmissing
  simpa using
    alignedValid_level_sound PackingCert.pairIndexValid_12
      PackedExhaustionN12Through11.valid (by decide) haligned G hcard

end Erdos76.CertificateChecker.Certificates.StrongBaseN12A3
