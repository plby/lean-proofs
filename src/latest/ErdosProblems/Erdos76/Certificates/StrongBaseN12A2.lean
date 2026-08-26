/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.Certificates.PackedExhaustionN12Through10
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A2Aligned

/-! The exact `n = 12`, `a = 2` strong almost-complete base. -/
namespace Erdos76.CertificateChecker.Certificates.StrongBaseN12A2

open CertificateExhaustion
open CertificateExhaustion.Certificates
open PackedBucketCertificate

private def maskChunk (start count : ℕ) :
    List (BitVec (edgeCount 12)) :=
  List.ofFn (fun i : Fin count ↦
    PackedExhaustionN12.level10.maskAt (start + i))

private lemma maskChunk_add (start left right : ℕ) :
    maskChunk start (left + right) =
      maskChunk start left ++ maskChunk (start + left) right := by
  unfold maskChunk
  simpa only [Nat.add_assoc, Fin.val_castLE, Fin.val_natAdd] using
    (List.ofFn_add (f := fun i : Fin (left + right) ↦
      PackedExhaustionN12.level10.maskAt (start + i)))

private def nativeMaskList : List (BitVec (edgeCount 12)) :=
  List.ofFn (fun i : Fin PackedExhaustionN12.level10.count ↦
    PackedExhaustionN12.level10.maskAt i)

private theorem level10_to_nativeMaskList :
    PackedExhaustionN12.level10.toArray.toList = nativeMaskList := by
  unfold CertificateExhaustion.Packed.Level.toArray nativeMaskList
  exact Array.toList_ofFn

private theorem level10_count :
    PackedExhaustionN12.level10.count = 4191 := by
  rfl

private theorem nativeMaskList_eq_maskChunk :
    nativeMaskList = maskChunk 0 4191 := by
  unfold nativeMaskList maskChunk
  have hc : PackedExhaustionN12.level10.count = 4191 := level10_count
  cases hc
  have h := List.ofFn_congr rfl
    (fun i : Fin 4191 ↦ PackedExhaustionN12.level10.maskAt i)
  refine h.trans ?_
  apply congrArg
    (fun f : Fin 4191 → BitVec (edgeCount 12) ↦ List.ofFn f)
  funext i
  apply congrArg PackedExhaustionN12.level10.maskAt
  simp only [Fin.val_cast, Nat.zero_add]

theorem level10_toList_eq_missing :
    PackedExhaustionN12.level10.toArray.toList =
      StrongPackedBucketN12A2Aligned.missing := by
  have h0_32 : maskChunk 0 32 =
      StrongPackedBucketN12A2AlignedShard000.missing0_32 := by decide
  have h32_64 : maskChunk 32 32 =
      StrongPackedBucketN12A2AlignedShard000.missing32_64 := by decide
  have h64_96 : maskChunk 64 32 =
      StrongPackedBucketN12A2AlignedShard000.missing64_96 := by decide
  have h96_128 : maskChunk 96 32 =
      StrongPackedBucketN12A2AlignedShard000.missing96_128 := by decide
  have h0_64 : maskChunk 0 64 =
      StrongPackedBucketN12A2AlignedShard000.missing0_64 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h0_32, h32_64]
    rfl
  have h64_128 : maskChunk 64 64 =
      StrongPackedBucketN12A2AlignedShard000.missing64_128 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h64_96, h96_128]
    rfl
  have h0_128 : maskChunk 0 128 =
      StrongPackedBucketN12A2AlignedShard000.missing0_128 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h0_64, h64_128]
    rfl
  have hs0 : maskChunk 0 128 =
      StrongPackedBucketN12A2AlignedShard000.missing := h0_128
  have h128_160 : maskChunk 128 32 =
      StrongPackedBucketN12A2AlignedShard001.missing128_160 := by decide
  have h160_192 : maskChunk 160 32 =
      StrongPackedBucketN12A2AlignedShard001.missing160_192 := by decide
  have h192_224 : maskChunk 192 32 =
      StrongPackedBucketN12A2AlignedShard001.missing192_224 := by decide
  have h224_256 : maskChunk 224 32 =
      StrongPackedBucketN12A2AlignedShard001.missing224_256 := by decide
  have h128_192 : maskChunk 128 64 =
      StrongPackedBucketN12A2AlignedShard001.missing128_192 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h128_160, h160_192]
    rfl
  have h192_256 : maskChunk 192 64 =
      StrongPackedBucketN12A2AlignedShard001.missing192_256 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h192_224, h224_256]
    rfl
  have h128_256 : maskChunk 128 128 =
      StrongPackedBucketN12A2AlignedShard001.missing128_256 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h128_192, h192_256]
    rfl
  have hs1 : maskChunk 128 128 =
      StrongPackedBucketN12A2AlignedShard001.missing := h128_256
  have h256_288 : maskChunk 256 32 =
      StrongPackedBucketN12A2AlignedShard002.missing256_288 := by decide
  have h288_320 : maskChunk 288 32 =
      StrongPackedBucketN12A2AlignedShard002.missing288_320 := by decide
  have h320_352 : maskChunk 320 32 =
      StrongPackedBucketN12A2AlignedShard002.missing320_352 := by decide
  have h352_384 : maskChunk 352 32 =
      StrongPackedBucketN12A2AlignedShard002.missing352_384 := by decide
  have h256_320 : maskChunk 256 64 =
      StrongPackedBucketN12A2AlignedShard002.missing256_320 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h256_288, h288_320]
    rfl
  have h320_384 : maskChunk 320 64 =
      StrongPackedBucketN12A2AlignedShard002.missing320_384 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h320_352, h352_384]
    rfl
  have h256_384 : maskChunk 256 128 =
      StrongPackedBucketN12A2AlignedShard002.missing256_384 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h256_320, h320_384]
    rfl
  have hs2 : maskChunk 256 128 =
      StrongPackedBucketN12A2AlignedShard002.missing := h256_384
  have h384_416 : maskChunk 384 32 =
      StrongPackedBucketN12A2AlignedShard003.missing384_416 := by decide
  have h416_448 : maskChunk 416 32 =
      StrongPackedBucketN12A2AlignedShard003.missing416_448 := by decide
  have h448_480 : maskChunk 448 32 =
      StrongPackedBucketN12A2AlignedShard003.missing448_480 := by decide
  have h480_512 : maskChunk 480 32 =
      StrongPackedBucketN12A2AlignedShard003.missing480_512 := by decide
  have h384_448 : maskChunk 384 64 =
      StrongPackedBucketN12A2AlignedShard003.missing384_448 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h384_416, h416_448]
    rfl
  have h448_512 : maskChunk 448 64 =
      StrongPackedBucketN12A2AlignedShard003.missing448_512 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h448_480, h480_512]
    rfl
  have h384_512 : maskChunk 384 128 =
      StrongPackedBucketN12A2AlignedShard003.missing384_512 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h384_448, h448_512]
    rfl
  have hs3 : maskChunk 384 128 =
      StrongPackedBucketN12A2AlignedShard003.missing := h384_512
  have h512_544 : maskChunk 512 32 =
      StrongPackedBucketN12A2AlignedShard004.missing512_544 := by decide
  have h544_576 : maskChunk 544 32 =
      StrongPackedBucketN12A2AlignedShard004.missing544_576 := by decide
  have h576_608 : maskChunk 576 32 =
      StrongPackedBucketN12A2AlignedShard004.missing576_608 := by decide
  have h608_640 : maskChunk 608 32 =
      StrongPackedBucketN12A2AlignedShard004.missing608_640 := by decide
  have h512_576 : maskChunk 512 64 =
      StrongPackedBucketN12A2AlignedShard004.missing512_576 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h512_544, h544_576]
    rfl
  have h576_640 : maskChunk 576 64 =
      StrongPackedBucketN12A2AlignedShard004.missing576_640 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h576_608, h608_640]
    rfl
  have h512_640 : maskChunk 512 128 =
      StrongPackedBucketN12A2AlignedShard004.missing512_640 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h512_576, h576_640]
    rfl
  have hs4 : maskChunk 512 128 =
      StrongPackedBucketN12A2AlignedShard004.missing := h512_640
  have h640_672 : maskChunk 640 32 =
      StrongPackedBucketN12A2AlignedShard005.missing640_672 := by decide
  have h672_704 : maskChunk 672 32 =
      StrongPackedBucketN12A2AlignedShard005.missing672_704 := by decide
  have h704_736 : maskChunk 704 32 =
      StrongPackedBucketN12A2AlignedShard005.missing704_736 := by decide
  have h736_768 : maskChunk 736 32 =
      StrongPackedBucketN12A2AlignedShard005.missing736_768 := by decide
  have h640_704 : maskChunk 640 64 =
      StrongPackedBucketN12A2AlignedShard005.missing640_704 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h640_672, h672_704]
    rfl
  have h704_768 : maskChunk 704 64 =
      StrongPackedBucketN12A2AlignedShard005.missing704_768 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h704_736, h736_768]
    rfl
  have h640_768 : maskChunk 640 128 =
      StrongPackedBucketN12A2AlignedShard005.missing640_768 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h640_704, h704_768]
    rfl
  have hs5 : maskChunk 640 128 =
      StrongPackedBucketN12A2AlignedShard005.missing := h640_768
  have h768_800 : maskChunk 768 32 =
      StrongPackedBucketN12A2AlignedShard006.missing768_800 := by decide
  have h800_832 : maskChunk 800 32 =
      StrongPackedBucketN12A2AlignedShard006.missing800_832 := by decide
  have h832_864 : maskChunk 832 32 =
      StrongPackedBucketN12A2AlignedShard006.missing832_864 := by decide
  have h864_896 : maskChunk 864 32 =
      StrongPackedBucketN12A2AlignedShard006.missing864_896 := by decide
  have h768_832 : maskChunk 768 64 =
      StrongPackedBucketN12A2AlignedShard006.missing768_832 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h768_800, h800_832]
    rfl
  have h832_896 : maskChunk 832 64 =
      StrongPackedBucketN12A2AlignedShard006.missing832_896 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h832_864, h864_896]
    rfl
  have h768_896 : maskChunk 768 128 =
      StrongPackedBucketN12A2AlignedShard006.missing768_896 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h768_832, h832_896]
    rfl
  have hs6 : maskChunk 768 128 =
      StrongPackedBucketN12A2AlignedShard006.missing := h768_896
  have h896_928 : maskChunk 896 32 =
      StrongPackedBucketN12A2AlignedShard007.missing896_928 := by decide
  have h928_960 : maskChunk 928 32 =
      StrongPackedBucketN12A2AlignedShard007.missing928_960 := by decide
  have h960_992 : maskChunk 960 32 =
      StrongPackedBucketN12A2AlignedShard007.missing960_992 := by decide
  have h992_1024 : maskChunk 992 32 =
      StrongPackedBucketN12A2AlignedShard007.missing992_1024 := by decide
  have h896_960 : maskChunk 896 64 =
      StrongPackedBucketN12A2AlignedShard007.missing896_960 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h896_928, h928_960]
    rfl
  have h960_1024 : maskChunk 960 64 =
      StrongPackedBucketN12A2AlignedShard007.missing960_1024 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h960_992, h992_1024]
    rfl
  have h896_1024 : maskChunk 896 128 =
      StrongPackedBucketN12A2AlignedShard007.missing896_1024 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h896_960, h960_1024]
    rfl
  have hs7 : maskChunk 896 128 =
      StrongPackedBucketN12A2AlignedShard007.missing := h896_1024
  have h1024_1056 : maskChunk 1024 32 =
      StrongPackedBucketN12A2AlignedShard008.missing1024_1056 := by decide
  have h1056_1088 : maskChunk 1056 32 =
      StrongPackedBucketN12A2AlignedShard008.missing1056_1088 := by decide
  have h1088_1120 : maskChunk 1088 32 =
      StrongPackedBucketN12A2AlignedShard008.missing1088_1120 := by decide
  have h1120_1152 : maskChunk 1120 32 =
      StrongPackedBucketN12A2AlignedShard008.missing1120_1152 := by decide
  have h1024_1088 : maskChunk 1024 64 =
      StrongPackedBucketN12A2AlignedShard008.missing1024_1088 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1024_1056, h1056_1088]
    rfl
  have h1088_1152 : maskChunk 1088 64 =
      StrongPackedBucketN12A2AlignedShard008.missing1088_1152 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1088_1120, h1120_1152]
    rfl
  have h1024_1152 : maskChunk 1024 128 =
      StrongPackedBucketN12A2AlignedShard008.missing1024_1152 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1024_1088, h1088_1152]
    rfl
  have hs8 : maskChunk 1024 128 =
      StrongPackedBucketN12A2AlignedShard008.missing := h1024_1152
  have h1152_1184 : maskChunk 1152 32 =
      StrongPackedBucketN12A2AlignedShard009.missing1152_1184 := by decide
  have h1184_1216 : maskChunk 1184 32 =
      StrongPackedBucketN12A2AlignedShard009.missing1184_1216 := by decide
  have h1216_1248 : maskChunk 1216 32 =
      StrongPackedBucketN12A2AlignedShard009.missing1216_1248 := by decide
  have h1248_1280 : maskChunk 1248 32 =
      StrongPackedBucketN12A2AlignedShard009.missing1248_1280 := by decide
  have h1152_1216 : maskChunk 1152 64 =
      StrongPackedBucketN12A2AlignedShard009.missing1152_1216 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1152_1184, h1184_1216]
    rfl
  have h1216_1280 : maskChunk 1216 64 =
      StrongPackedBucketN12A2AlignedShard009.missing1216_1280 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1216_1248, h1248_1280]
    rfl
  have h1152_1280 : maskChunk 1152 128 =
      StrongPackedBucketN12A2AlignedShard009.missing1152_1280 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1152_1216, h1216_1280]
    rfl
  have hs9 : maskChunk 1152 128 =
      StrongPackedBucketN12A2AlignedShard009.missing := h1152_1280
  have h1280_1312 : maskChunk 1280 32 =
      StrongPackedBucketN12A2AlignedShard010.missing1280_1312 := by decide
  have h1312_1344 : maskChunk 1312 32 =
      StrongPackedBucketN12A2AlignedShard010.missing1312_1344 := by decide
  have h1344_1376 : maskChunk 1344 32 =
      StrongPackedBucketN12A2AlignedShard010.missing1344_1376 := by decide
  have h1376_1408 : maskChunk 1376 32 =
      StrongPackedBucketN12A2AlignedShard010.missing1376_1408 := by decide
  have h1280_1344 : maskChunk 1280 64 =
      StrongPackedBucketN12A2AlignedShard010.missing1280_1344 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1280_1312, h1312_1344]
    rfl
  have h1344_1408 : maskChunk 1344 64 =
      StrongPackedBucketN12A2AlignedShard010.missing1344_1408 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1344_1376, h1376_1408]
    rfl
  have h1280_1408 : maskChunk 1280 128 =
      StrongPackedBucketN12A2AlignedShard010.missing1280_1408 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1280_1344, h1344_1408]
    rfl
  have hs10 : maskChunk 1280 128 =
      StrongPackedBucketN12A2AlignedShard010.missing := h1280_1408
  have h1408_1440 : maskChunk 1408 32 =
      StrongPackedBucketN12A2AlignedShard011.missing1408_1440 := by decide
  have h1440_1472 : maskChunk 1440 32 =
      StrongPackedBucketN12A2AlignedShard011.missing1440_1472 := by decide
  have h1472_1504 : maskChunk 1472 32 =
      StrongPackedBucketN12A2AlignedShard011.missing1472_1504 := by decide
  have h1504_1536 : maskChunk 1504 32 =
      StrongPackedBucketN12A2AlignedShard011.missing1504_1536 := by decide
  have h1408_1472 : maskChunk 1408 64 =
      StrongPackedBucketN12A2AlignedShard011.missing1408_1472 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1408_1440, h1440_1472]
    rfl
  have h1472_1536 : maskChunk 1472 64 =
      StrongPackedBucketN12A2AlignedShard011.missing1472_1536 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1472_1504, h1504_1536]
    rfl
  have h1408_1536 : maskChunk 1408 128 =
      StrongPackedBucketN12A2AlignedShard011.missing1408_1536 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1408_1472, h1472_1536]
    rfl
  have hs11 : maskChunk 1408 128 =
      StrongPackedBucketN12A2AlignedShard011.missing := h1408_1536
  have h1536_1568 : maskChunk 1536 32 =
      StrongPackedBucketN12A2AlignedShard012.missing1536_1568 := by decide
  have h1568_1600 : maskChunk 1568 32 =
      StrongPackedBucketN12A2AlignedShard012.missing1568_1600 := by decide
  have h1600_1632 : maskChunk 1600 32 =
      StrongPackedBucketN12A2AlignedShard012.missing1600_1632 := by decide
  have h1632_1664 : maskChunk 1632 32 =
      StrongPackedBucketN12A2AlignedShard012.missing1632_1664 := by decide
  have h1536_1600 : maskChunk 1536 64 =
      StrongPackedBucketN12A2AlignedShard012.missing1536_1600 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1536_1568, h1568_1600]
    rfl
  have h1600_1664 : maskChunk 1600 64 =
      StrongPackedBucketN12A2AlignedShard012.missing1600_1664 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1600_1632, h1632_1664]
    rfl
  have h1536_1664 : maskChunk 1536 128 =
      StrongPackedBucketN12A2AlignedShard012.missing1536_1664 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1536_1600, h1600_1664]
    rfl
  have hs12 : maskChunk 1536 128 =
      StrongPackedBucketN12A2AlignedShard012.missing := h1536_1664
  have h1664_1696 : maskChunk 1664 32 =
      StrongPackedBucketN12A2AlignedShard013.missing1664_1696 := by decide
  have h1696_1728 : maskChunk 1696 32 =
      StrongPackedBucketN12A2AlignedShard013.missing1696_1728 := by decide
  have h1728_1760 : maskChunk 1728 32 =
      StrongPackedBucketN12A2AlignedShard013.missing1728_1760 := by decide
  have h1760_1792 : maskChunk 1760 32 =
      StrongPackedBucketN12A2AlignedShard013.missing1760_1792 := by decide
  have h1664_1728 : maskChunk 1664 64 =
      StrongPackedBucketN12A2AlignedShard013.missing1664_1728 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1664_1696, h1696_1728]
    rfl
  have h1728_1792 : maskChunk 1728 64 =
      StrongPackedBucketN12A2AlignedShard013.missing1728_1792 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1728_1760, h1760_1792]
    rfl
  have h1664_1792 : maskChunk 1664 128 =
      StrongPackedBucketN12A2AlignedShard013.missing1664_1792 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1664_1728, h1728_1792]
    rfl
  have hs13 : maskChunk 1664 128 =
      StrongPackedBucketN12A2AlignedShard013.missing := h1664_1792
  have h1792_1824 : maskChunk 1792 32 =
      StrongPackedBucketN12A2AlignedShard014.missing1792_1824 := by decide
  have h1824_1856 : maskChunk 1824 32 =
      StrongPackedBucketN12A2AlignedShard014.missing1824_1856 := by decide
  have h1856_1888 : maskChunk 1856 32 =
      StrongPackedBucketN12A2AlignedShard014.missing1856_1888 := by decide
  have h1888_1920 : maskChunk 1888 32 =
      StrongPackedBucketN12A2AlignedShard014.missing1888_1920 := by decide
  have h1792_1856 : maskChunk 1792 64 =
      StrongPackedBucketN12A2AlignedShard014.missing1792_1856 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1792_1824, h1824_1856]
    rfl
  have h1856_1920 : maskChunk 1856 64 =
      StrongPackedBucketN12A2AlignedShard014.missing1856_1920 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1856_1888, h1888_1920]
    rfl
  have h1792_1920 : maskChunk 1792 128 =
      StrongPackedBucketN12A2AlignedShard014.missing1792_1920 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1792_1856, h1856_1920]
    rfl
  have hs14 : maskChunk 1792 128 =
      StrongPackedBucketN12A2AlignedShard014.missing := h1792_1920
  have h1920_1952 : maskChunk 1920 32 =
      StrongPackedBucketN12A2AlignedShard015.missing1920_1952 := by decide
  have h1952_1984 : maskChunk 1952 32 =
      StrongPackedBucketN12A2AlignedShard015.missing1952_1984 := by decide
  have h1984_2016 : maskChunk 1984 32 =
      StrongPackedBucketN12A2AlignedShard015.missing1984_2016 := by decide
  have h2016_2048 : maskChunk 2016 32 =
      StrongPackedBucketN12A2AlignedShard015.missing2016_2048 := by decide
  have h1920_1984 : maskChunk 1920 64 =
      StrongPackedBucketN12A2AlignedShard015.missing1920_1984 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1920_1952, h1952_1984]
    rfl
  have h1984_2048 : maskChunk 1984 64 =
      StrongPackedBucketN12A2AlignedShard015.missing1984_2048 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h1984_2016, h2016_2048]
    rfl
  have h1920_2048 : maskChunk 1920 128 =
      StrongPackedBucketN12A2AlignedShard015.missing1920_2048 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h1920_1984, h1984_2048]
    rfl
  have hs15 : maskChunk 1920 128 =
      StrongPackedBucketN12A2AlignedShard015.missing := h1920_2048
  have h2048_2080 : maskChunk 2048 32 =
      StrongPackedBucketN12A2AlignedShard016.missing2048_2080 := by decide
  have h2080_2112 : maskChunk 2080 32 =
      StrongPackedBucketN12A2AlignedShard016.missing2080_2112 := by decide
  have h2112_2144 : maskChunk 2112 32 =
      StrongPackedBucketN12A2AlignedShard016.missing2112_2144 := by decide
  have h2144_2176 : maskChunk 2144 32 =
      StrongPackedBucketN12A2AlignedShard016.missing2144_2176 := by decide
  have h2048_2112 : maskChunk 2048 64 =
      StrongPackedBucketN12A2AlignedShard016.missing2048_2112 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2048_2080, h2080_2112]
    rfl
  have h2112_2176 : maskChunk 2112 64 =
      StrongPackedBucketN12A2AlignedShard016.missing2112_2176 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2112_2144, h2144_2176]
    rfl
  have h2048_2176 : maskChunk 2048 128 =
      StrongPackedBucketN12A2AlignedShard016.missing2048_2176 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2048_2112, h2112_2176]
    rfl
  have hs16 : maskChunk 2048 128 =
      StrongPackedBucketN12A2AlignedShard016.missing := h2048_2176
  have h2176_2208 : maskChunk 2176 32 =
      StrongPackedBucketN12A2AlignedShard017.missing2176_2208 := by decide
  have h2208_2240 : maskChunk 2208 32 =
      StrongPackedBucketN12A2AlignedShard017.missing2208_2240 := by decide
  have h2240_2272 : maskChunk 2240 32 =
      StrongPackedBucketN12A2AlignedShard017.missing2240_2272 := by decide
  have h2272_2304 : maskChunk 2272 32 =
      StrongPackedBucketN12A2AlignedShard017.missing2272_2304 := by decide
  have h2176_2240 : maskChunk 2176 64 =
      StrongPackedBucketN12A2AlignedShard017.missing2176_2240 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2176_2208, h2208_2240]
    rfl
  have h2240_2304 : maskChunk 2240 64 =
      StrongPackedBucketN12A2AlignedShard017.missing2240_2304 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2240_2272, h2272_2304]
    rfl
  have h2176_2304 : maskChunk 2176 128 =
      StrongPackedBucketN12A2AlignedShard017.missing2176_2304 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2176_2240, h2240_2304]
    rfl
  have hs17 : maskChunk 2176 128 =
      StrongPackedBucketN12A2AlignedShard017.missing := h2176_2304
  have h2304_2336 : maskChunk 2304 32 =
      StrongPackedBucketN12A2AlignedShard018.missing2304_2336 := by decide
  have h2336_2368 : maskChunk 2336 32 =
      StrongPackedBucketN12A2AlignedShard018.missing2336_2368 := by decide
  have h2368_2400 : maskChunk 2368 32 =
      StrongPackedBucketN12A2AlignedShard018.missing2368_2400 := by decide
  have h2400_2432 : maskChunk 2400 32 =
      StrongPackedBucketN12A2AlignedShard018.missing2400_2432 := by decide
  have h2304_2368 : maskChunk 2304 64 =
      StrongPackedBucketN12A2AlignedShard018.missing2304_2368 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2304_2336, h2336_2368]
    rfl
  have h2368_2432 : maskChunk 2368 64 =
      StrongPackedBucketN12A2AlignedShard018.missing2368_2432 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2368_2400, h2400_2432]
    rfl
  have h2304_2432 : maskChunk 2304 128 =
      StrongPackedBucketN12A2AlignedShard018.missing2304_2432 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2304_2368, h2368_2432]
    rfl
  have hs18 : maskChunk 2304 128 =
      StrongPackedBucketN12A2AlignedShard018.missing := h2304_2432
  have h2432_2464 : maskChunk 2432 32 =
      StrongPackedBucketN12A2AlignedShard019.missing2432_2464 := by decide
  have h2464_2496 : maskChunk 2464 32 =
      StrongPackedBucketN12A2AlignedShard019.missing2464_2496 := by decide
  have h2496_2528 : maskChunk 2496 32 =
      StrongPackedBucketN12A2AlignedShard019.missing2496_2528 := by decide
  have h2528_2560 : maskChunk 2528 32 =
      StrongPackedBucketN12A2AlignedShard019.missing2528_2560 := by decide
  have h2432_2496 : maskChunk 2432 64 =
      StrongPackedBucketN12A2AlignedShard019.missing2432_2496 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2432_2464, h2464_2496]
    rfl
  have h2496_2560 : maskChunk 2496 64 =
      StrongPackedBucketN12A2AlignedShard019.missing2496_2560 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2496_2528, h2528_2560]
    rfl
  have h2432_2560 : maskChunk 2432 128 =
      StrongPackedBucketN12A2AlignedShard019.missing2432_2560 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2432_2496, h2496_2560]
    rfl
  have hs19 : maskChunk 2432 128 =
      StrongPackedBucketN12A2AlignedShard019.missing := h2432_2560
  have h2560_2592 : maskChunk 2560 32 =
      StrongPackedBucketN12A2AlignedShard020.missing2560_2592 := by decide
  have h2592_2624 : maskChunk 2592 32 =
      StrongPackedBucketN12A2AlignedShard020.missing2592_2624 := by decide
  have h2624_2656 : maskChunk 2624 32 =
      StrongPackedBucketN12A2AlignedShard020.missing2624_2656 := by decide
  have h2656_2688 : maskChunk 2656 32 =
      StrongPackedBucketN12A2AlignedShard020.missing2656_2688 := by decide
  have h2560_2624 : maskChunk 2560 64 =
      StrongPackedBucketN12A2AlignedShard020.missing2560_2624 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2560_2592, h2592_2624]
    rfl
  have h2624_2688 : maskChunk 2624 64 =
      StrongPackedBucketN12A2AlignedShard020.missing2624_2688 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2624_2656, h2656_2688]
    rfl
  have h2560_2688 : maskChunk 2560 128 =
      StrongPackedBucketN12A2AlignedShard020.missing2560_2688 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2560_2624, h2624_2688]
    rfl
  have hs20 : maskChunk 2560 128 =
      StrongPackedBucketN12A2AlignedShard020.missing := h2560_2688
  have h2688_2720 : maskChunk 2688 32 =
      StrongPackedBucketN12A2AlignedShard021.missing2688_2720 := by decide
  have h2720_2752 : maskChunk 2720 32 =
      StrongPackedBucketN12A2AlignedShard021.missing2720_2752 := by decide
  have h2752_2784 : maskChunk 2752 32 =
      StrongPackedBucketN12A2AlignedShard021.missing2752_2784 := by decide
  have h2784_2816 : maskChunk 2784 32 =
      StrongPackedBucketN12A2AlignedShard021.missing2784_2816 := by decide
  have h2688_2752 : maskChunk 2688 64 =
      StrongPackedBucketN12A2AlignedShard021.missing2688_2752 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2688_2720, h2720_2752]
    rfl
  have h2752_2816 : maskChunk 2752 64 =
      StrongPackedBucketN12A2AlignedShard021.missing2752_2816 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2752_2784, h2784_2816]
    rfl
  have h2688_2816 : maskChunk 2688 128 =
      StrongPackedBucketN12A2AlignedShard021.missing2688_2816 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2688_2752, h2752_2816]
    rfl
  have hs21 : maskChunk 2688 128 =
      StrongPackedBucketN12A2AlignedShard021.missing := h2688_2816
  have h2816_2848 : maskChunk 2816 32 =
      StrongPackedBucketN12A2AlignedShard022.missing2816_2848 := by decide
  have h2848_2880 : maskChunk 2848 32 =
      StrongPackedBucketN12A2AlignedShard022.missing2848_2880 := by decide
  have h2880_2912 : maskChunk 2880 32 =
      StrongPackedBucketN12A2AlignedShard022.missing2880_2912 := by decide
  have h2912_2944 : maskChunk 2912 32 =
      StrongPackedBucketN12A2AlignedShard022.missing2912_2944 := by decide
  have h2816_2880 : maskChunk 2816 64 =
      StrongPackedBucketN12A2AlignedShard022.missing2816_2880 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2816_2848, h2848_2880]
    rfl
  have h2880_2944 : maskChunk 2880 64 =
      StrongPackedBucketN12A2AlignedShard022.missing2880_2944 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2880_2912, h2912_2944]
    rfl
  have h2816_2944 : maskChunk 2816 128 =
      StrongPackedBucketN12A2AlignedShard022.missing2816_2944 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2816_2880, h2880_2944]
    rfl
  have hs22 : maskChunk 2816 128 =
      StrongPackedBucketN12A2AlignedShard022.missing := h2816_2944
  have h2944_2976 : maskChunk 2944 32 =
      StrongPackedBucketN12A2AlignedShard023.missing2944_2976 := by decide
  have h2976_3008 : maskChunk 2976 32 =
      StrongPackedBucketN12A2AlignedShard023.missing2976_3008 := by decide
  have h3008_3040 : maskChunk 3008 32 =
      StrongPackedBucketN12A2AlignedShard023.missing3008_3040 := by decide
  have h3040_3072 : maskChunk 3040 32 =
      StrongPackedBucketN12A2AlignedShard023.missing3040_3072 := by decide
  have h2944_3008 : maskChunk 2944 64 =
      StrongPackedBucketN12A2AlignedShard023.missing2944_3008 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h2944_2976, h2976_3008]
    rfl
  have h3008_3072 : maskChunk 3008 64 =
      StrongPackedBucketN12A2AlignedShard023.missing3008_3072 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3008_3040, h3040_3072]
    rfl
  have h2944_3072 : maskChunk 2944 128 =
      StrongPackedBucketN12A2AlignedShard023.missing2944_3072 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h2944_3008, h3008_3072]
    rfl
  have hs23 : maskChunk 2944 128 =
      StrongPackedBucketN12A2AlignedShard023.missing := h2944_3072
  have h3072_3104 : maskChunk 3072 32 =
      StrongPackedBucketN12A2AlignedShard024.missing3072_3104 := by decide
  have h3104_3136 : maskChunk 3104 32 =
      StrongPackedBucketN12A2AlignedShard024.missing3104_3136 := by decide
  have h3136_3168 : maskChunk 3136 32 =
      StrongPackedBucketN12A2AlignedShard024.missing3136_3168 := by decide
  have h3168_3200 : maskChunk 3168 32 =
      StrongPackedBucketN12A2AlignedShard024.missing3168_3200 := by decide
  have h3072_3136 : maskChunk 3072 64 =
      StrongPackedBucketN12A2AlignedShard024.missing3072_3136 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3072_3104, h3104_3136]
    rfl
  have h3136_3200 : maskChunk 3136 64 =
      StrongPackedBucketN12A2AlignedShard024.missing3136_3200 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3136_3168, h3168_3200]
    rfl
  have h3072_3200 : maskChunk 3072 128 =
      StrongPackedBucketN12A2AlignedShard024.missing3072_3200 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3072_3136, h3136_3200]
    rfl
  have hs24 : maskChunk 3072 128 =
      StrongPackedBucketN12A2AlignedShard024.missing := h3072_3200
  have h3200_3232 : maskChunk 3200 32 =
      StrongPackedBucketN12A2AlignedShard025.missing3200_3232 := by decide
  have h3232_3264 : maskChunk 3232 32 =
      StrongPackedBucketN12A2AlignedShard025.missing3232_3264 := by decide
  have h3264_3296 : maskChunk 3264 32 =
      StrongPackedBucketN12A2AlignedShard025.missing3264_3296 := by decide
  have h3296_3328 : maskChunk 3296 32 =
      StrongPackedBucketN12A2AlignedShard025.missing3296_3328 := by decide
  have h3200_3264 : maskChunk 3200 64 =
      StrongPackedBucketN12A2AlignedShard025.missing3200_3264 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3200_3232, h3232_3264]
    rfl
  have h3264_3328 : maskChunk 3264 64 =
      StrongPackedBucketN12A2AlignedShard025.missing3264_3328 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3264_3296, h3296_3328]
    rfl
  have h3200_3328 : maskChunk 3200 128 =
      StrongPackedBucketN12A2AlignedShard025.missing3200_3328 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3200_3264, h3264_3328]
    rfl
  have hs25 : maskChunk 3200 128 =
      StrongPackedBucketN12A2AlignedShard025.missing := h3200_3328
  have h3328_3360 : maskChunk 3328 32 =
      StrongPackedBucketN12A2AlignedShard026.missing3328_3360 := by decide
  have h3360_3392 : maskChunk 3360 32 =
      StrongPackedBucketN12A2AlignedShard026.missing3360_3392 := by decide
  have h3392_3424 : maskChunk 3392 32 =
      StrongPackedBucketN12A2AlignedShard026.missing3392_3424 := by decide
  have h3424_3456 : maskChunk 3424 32 =
      StrongPackedBucketN12A2AlignedShard026.missing3424_3456 := by decide
  have h3328_3392 : maskChunk 3328 64 =
      StrongPackedBucketN12A2AlignedShard026.missing3328_3392 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3328_3360, h3360_3392]
    rfl
  have h3392_3456 : maskChunk 3392 64 =
      StrongPackedBucketN12A2AlignedShard026.missing3392_3456 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3392_3424, h3424_3456]
    rfl
  have h3328_3456 : maskChunk 3328 128 =
      StrongPackedBucketN12A2AlignedShard026.missing3328_3456 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3328_3392, h3392_3456]
    rfl
  have hs26 : maskChunk 3328 128 =
      StrongPackedBucketN12A2AlignedShard026.missing := h3328_3456
  have h3456_3488 : maskChunk 3456 32 =
      StrongPackedBucketN12A2AlignedShard027.missing3456_3488 := by decide
  have h3488_3520 : maskChunk 3488 32 =
      StrongPackedBucketN12A2AlignedShard027.missing3488_3520 := by decide
  have h3520_3552 : maskChunk 3520 32 =
      StrongPackedBucketN12A2AlignedShard027.missing3520_3552 := by decide
  have h3552_3584 : maskChunk 3552 32 =
      StrongPackedBucketN12A2AlignedShard027.missing3552_3584 := by decide
  have h3456_3520 : maskChunk 3456 64 =
      StrongPackedBucketN12A2AlignedShard027.missing3456_3520 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3456_3488, h3488_3520]
    rfl
  have h3520_3584 : maskChunk 3520 64 =
      StrongPackedBucketN12A2AlignedShard027.missing3520_3584 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3520_3552, h3552_3584]
    rfl
  have h3456_3584 : maskChunk 3456 128 =
      StrongPackedBucketN12A2AlignedShard027.missing3456_3584 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3456_3520, h3520_3584]
    rfl
  have hs27 : maskChunk 3456 128 =
      StrongPackedBucketN12A2AlignedShard027.missing := h3456_3584
  have h3584_3616 : maskChunk 3584 32 =
      StrongPackedBucketN12A2AlignedShard028.missing3584_3616 := by decide
  have h3616_3648 : maskChunk 3616 32 =
      StrongPackedBucketN12A2AlignedShard028.missing3616_3648 := by decide
  have h3648_3680 : maskChunk 3648 32 =
      StrongPackedBucketN12A2AlignedShard028.missing3648_3680 := by decide
  have h3680_3712 : maskChunk 3680 32 =
      StrongPackedBucketN12A2AlignedShard028.missing3680_3712 := by decide
  have h3584_3648 : maskChunk 3584 64 =
      StrongPackedBucketN12A2AlignedShard028.missing3584_3648 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3584_3616, h3616_3648]
    rfl
  have h3648_3712 : maskChunk 3648 64 =
      StrongPackedBucketN12A2AlignedShard028.missing3648_3712 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3648_3680, h3680_3712]
    rfl
  have h3584_3712 : maskChunk 3584 128 =
      StrongPackedBucketN12A2AlignedShard028.missing3584_3712 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3584_3648, h3648_3712]
    rfl
  have hs28 : maskChunk 3584 128 =
      StrongPackedBucketN12A2AlignedShard028.missing := h3584_3712
  have h3712_3744 : maskChunk 3712 32 =
      StrongPackedBucketN12A2AlignedShard029.missing3712_3744 := by decide
  have h3744_3776 : maskChunk 3744 32 =
      StrongPackedBucketN12A2AlignedShard029.missing3744_3776 := by decide
  have h3776_3808 : maskChunk 3776 32 =
      StrongPackedBucketN12A2AlignedShard029.missing3776_3808 := by decide
  have h3808_3840 : maskChunk 3808 32 =
      StrongPackedBucketN12A2AlignedShard029.missing3808_3840 := by decide
  have h3712_3776 : maskChunk 3712 64 =
      StrongPackedBucketN12A2AlignedShard029.missing3712_3776 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3712_3744, h3744_3776]
    rfl
  have h3776_3840 : maskChunk 3776 64 =
      StrongPackedBucketN12A2AlignedShard029.missing3776_3840 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3776_3808, h3808_3840]
    rfl
  have h3712_3840 : maskChunk 3712 128 =
      StrongPackedBucketN12A2AlignedShard029.missing3712_3840 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3712_3776, h3776_3840]
    rfl
  have hs29 : maskChunk 3712 128 =
      StrongPackedBucketN12A2AlignedShard029.missing := h3712_3840
  have h3840_3872 : maskChunk 3840 32 =
      StrongPackedBucketN12A2AlignedShard030.missing3840_3872 := by decide
  have h3872_3904 : maskChunk 3872 32 =
      StrongPackedBucketN12A2AlignedShard030.missing3872_3904 := by decide
  have h3904_3936 : maskChunk 3904 32 =
      StrongPackedBucketN12A2AlignedShard030.missing3904_3936 := by decide
  have h3936_3968 : maskChunk 3936 32 =
      StrongPackedBucketN12A2AlignedShard030.missing3936_3968 := by decide
  have h3840_3904 : maskChunk 3840 64 =
      StrongPackedBucketN12A2AlignedShard030.missing3840_3904 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3840_3872, h3872_3904]
    rfl
  have h3904_3968 : maskChunk 3904 64 =
      StrongPackedBucketN12A2AlignedShard030.missing3904_3968 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3904_3936, h3936_3968]
    rfl
  have h3840_3968 : maskChunk 3840 128 =
      StrongPackedBucketN12A2AlignedShard030.missing3840_3968 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3840_3904, h3904_3968]
    rfl
  have hs30 : maskChunk 3840 128 =
      StrongPackedBucketN12A2AlignedShard030.missing := h3840_3968
  have h3968_4000 : maskChunk 3968 32 =
      StrongPackedBucketN12A2AlignedShard031.missing3968_4000 := by decide
  have h4000_4032 : maskChunk 4000 32 =
      StrongPackedBucketN12A2AlignedShard031.missing4000_4032 := by decide
  have h4032_4064 : maskChunk 4032 32 =
      StrongPackedBucketN12A2AlignedShard031.missing4032_4064 := by decide
  have h4064_4096 : maskChunk 4064 32 =
      StrongPackedBucketN12A2AlignedShard031.missing4064_4096 := by decide
  have h3968_4032 : maskChunk 3968 64 =
      StrongPackedBucketN12A2AlignedShard031.missing3968_4032 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h3968_4000, h4000_4032]
    rfl
  have h4032_4096 : maskChunk 4032 64 =
      StrongPackedBucketN12A2AlignedShard031.missing4032_4096 := by
    rw [show 64 = 32 + 32 by omega,
      maskChunk_add, h4032_4064, h4064_4096]
    rfl
  have h3968_4096 : maskChunk 3968 128 =
      StrongPackedBucketN12A2AlignedShard031.missing3968_4096 := by
    rw [show 128 = 64 + 64 by omega,
      maskChunk_add, h3968_4032, h4032_4096]
    rfl
  have hs31 : maskChunk 3968 128 =
      StrongPackedBucketN12A2AlignedShard031.missing := h3968_4096
  have h4096_4119 : maskChunk 4096 23 =
      StrongPackedBucketN12A2AlignedShard032.missing4096_4119 := by decide
  have h4119_4143 : maskChunk 4119 24 =
      StrongPackedBucketN12A2AlignedShard032.missing4119_4143 := by decide
  have h4143_4167 : maskChunk 4143 24 =
      StrongPackedBucketN12A2AlignedShard032.missing4143_4167 := by decide
  have h4167_4191 : maskChunk 4167 24 =
      StrongPackedBucketN12A2AlignedShard032.missing4167_4191 := by decide
  have h4096_4143 : maskChunk 4096 47 =
      StrongPackedBucketN12A2AlignedShard032.missing4096_4143 := by
    rw [show 47 = 23 + 24 by omega,
      maskChunk_add, h4096_4119, h4119_4143]
    rfl
  have h4143_4191 : maskChunk 4143 48 =
      StrongPackedBucketN12A2AlignedShard032.missing4143_4191 := by
    rw [show 48 = 24 + 24 by omega,
      maskChunk_add, h4143_4167, h4167_4191]
    rfl
  have h4096_4191 : maskChunk 4096 95 =
      StrongPackedBucketN12A2AlignedShard032.missing4096_4191 := by
    rw [show 95 = 47 + 48 by omega,
      maskChunk_add, h4096_4143, h4143_4191]
    rfl
  have hs32 : maskChunk 4096 95 =
      StrongPackedBucketN12A2AlignedShard032.missing := h4096_4191
  have ha0_1 : maskChunk 0 128 =
      StrongPackedBucketN12A2Aligned.missing0_1 := by
    exact hs0
  have ha1_2 : maskChunk 128 128 =
      StrongPackedBucketN12A2Aligned.missing1_2 := by
    exact hs1
  have ha0_2 : maskChunk 0 256 =
      StrongPackedBucketN12A2Aligned.missing0_2 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha0_1, ha1_2]
    rfl
  have ha2_3 : maskChunk 256 128 =
      StrongPackedBucketN12A2Aligned.missing2_3 := by
    exact hs2
  have ha3_4 : maskChunk 384 128 =
      StrongPackedBucketN12A2Aligned.missing3_4 := by
    exact hs3
  have ha2_4 : maskChunk 256 256 =
      StrongPackedBucketN12A2Aligned.missing2_4 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha2_3, ha3_4]
    rfl
  have ha0_4 : maskChunk 0 512 =
      StrongPackedBucketN12A2Aligned.missing0_4 := by
    rw [show 512 = 256 + 256 by omega,
      maskChunk_add, ha0_2, ha2_4]
    rfl
  have ha4_5 : maskChunk 512 128 =
      StrongPackedBucketN12A2Aligned.missing4_5 := by
    exact hs4
  have ha5_6 : maskChunk 640 128 =
      StrongPackedBucketN12A2Aligned.missing5_6 := by
    exact hs5
  have ha4_6 : maskChunk 512 256 =
      StrongPackedBucketN12A2Aligned.missing4_6 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha4_5, ha5_6]
    rfl
  have ha6_7 : maskChunk 768 128 =
      StrongPackedBucketN12A2Aligned.missing6_7 := by
    exact hs6
  have ha7_8 : maskChunk 896 128 =
      StrongPackedBucketN12A2Aligned.missing7_8 := by
    exact hs7
  have ha6_8 : maskChunk 768 256 =
      StrongPackedBucketN12A2Aligned.missing6_8 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha6_7, ha7_8]
    rfl
  have ha4_8 : maskChunk 512 512 =
      StrongPackedBucketN12A2Aligned.missing4_8 := by
    rw [show 512 = 256 + 256 by omega,
      maskChunk_add, ha4_6, ha6_8]
    rfl
  have ha0_8 : maskChunk 0 1024 =
      StrongPackedBucketN12A2Aligned.missing0_8 := by
    rw [show 1024 = 512 + 512 by omega,
      maskChunk_add, ha0_4, ha4_8]
    rfl
  have ha8_9 : maskChunk 1024 128 =
      StrongPackedBucketN12A2Aligned.missing8_9 := by
    exact hs8
  have ha9_10 : maskChunk 1152 128 =
      StrongPackedBucketN12A2Aligned.missing9_10 := by
    exact hs9
  have ha8_10 : maskChunk 1024 256 =
      StrongPackedBucketN12A2Aligned.missing8_10 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha8_9, ha9_10]
    rfl
  have ha10_11 : maskChunk 1280 128 =
      StrongPackedBucketN12A2Aligned.missing10_11 := by
    exact hs10
  have ha11_12 : maskChunk 1408 128 =
      StrongPackedBucketN12A2Aligned.missing11_12 := by
    exact hs11
  have ha10_12 : maskChunk 1280 256 =
      StrongPackedBucketN12A2Aligned.missing10_12 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha10_11, ha11_12]
    rfl
  have ha8_12 : maskChunk 1024 512 =
      StrongPackedBucketN12A2Aligned.missing8_12 := by
    rw [show 512 = 256 + 256 by omega,
      maskChunk_add, ha8_10, ha10_12]
    rfl
  have ha12_13 : maskChunk 1536 128 =
      StrongPackedBucketN12A2Aligned.missing12_13 := by
    exact hs12
  have ha13_14 : maskChunk 1664 128 =
      StrongPackedBucketN12A2Aligned.missing13_14 := by
    exact hs13
  have ha12_14 : maskChunk 1536 256 =
      StrongPackedBucketN12A2Aligned.missing12_14 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha12_13, ha13_14]
    rfl
  have ha14_15 : maskChunk 1792 128 =
      StrongPackedBucketN12A2Aligned.missing14_15 := by
    exact hs14
  have ha15_16 : maskChunk 1920 128 =
      StrongPackedBucketN12A2Aligned.missing15_16 := by
    exact hs15
  have ha14_16 : maskChunk 1792 256 =
      StrongPackedBucketN12A2Aligned.missing14_16 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha14_15, ha15_16]
    rfl
  have ha12_16 : maskChunk 1536 512 =
      StrongPackedBucketN12A2Aligned.missing12_16 := by
    rw [show 512 = 256 + 256 by omega,
      maskChunk_add, ha12_14, ha14_16]
    rfl
  have ha8_16 : maskChunk 1024 1024 =
      StrongPackedBucketN12A2Aligned.missing8_16 := by
    rw [show 1024 = 512 + 512 by omega,
      maskChunk_add, ha8_12, ha12_16]
    rfl
  have ha0_16 : maskChunk 0 2048 =
      StrongPackedBucketN12A2Aligned.missing0_16 := by
    rw [show 2048 = 1024 + 1024 by omega,
      maskChunk_add, ha0_8, ha8_16]
    rfl
  have ha16_17 : maskChunk 2048 128 =
      StrongPackedBucketN12A2Aligned.missing16_17 := by
    exact hs16
  have ha17_18 : maskChunk 2176 128 =
      StrongPackedBucketN12A2Aligned.missing17_18 := by
    exact hs17
  have ha16_18 : maskChunk 2048 256 =
      StrongPackedBucketN12A2Aligned.missing16_18 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha16_17, ha17_18]
    rfl
  have ha18_19 : maskChunk 2304 128 =
      StrongPackedBucketN12A2Aligned.missing18_19 := by
    exact hs18
  have ha19_20 : maskChunk 2432 128 =
      StrongPackedBucketN12A2Aligned.missing19_20 := by
    exact hs19
  have ha18_20 : maskChunk 2304 256 =
      StrongPackedBucketN12A2Aligned.missing18_20 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha18_19, ha19_20]
    rfl
  have ha16_20 : maskChunk 2048 512 =
      StrongPackedBucketN12A2Aligned.missing16_20 := by
    rw [show 512 = 256 + 256 by omega,
      maskChunk_add, ha16_18, ha18_20]
    rfl
  have ha20_21 : maskChunk 2560 128 =
      StrongPackedBucketN12A2Aligned.missing20_21 := by
    exact hs20
  have ha21_22 : maskChunk 2688 128 =
      StrongPackedBucketN12A2Aligned.missing21_22 := by
    exact hs21
  have ha20_22 : maskChunk 2560 256 =
      StrongPackedBucketN12A2Aligned.missing20_22 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha20_21, ha21_22]
    rfl
  have ha22_23 : maskChunk 2816 128 =
      StrongPackedBucketN12A2Aligned.missing22_23 := by
    exact hs22
  have ha23_24 : maskChunk 2944 128 =
      StrongPackedBucketN12A2Aligned.missing23_24 := by
    exact hs23
  have ha22_24 : maskChunk 2816 256 =
      StrongPackedBucketN12A2Aligned.missing22_24 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha22_23, ha23_24]
    rfl
  have ha20_24 : maskChunk 2560 512 =
      StrongPackedBucketN12A2Aligned.missing20_24 := by
    rw [show 512 = 256 + 256 by omega,
      maskChunk_add, ha20_22, ha22_24]
    rfl
  have ha16_24 : maskChunk 2048 1024 =
      StrongPackedBucketN12A2Aligned.missing16_24 := by
    rw [show 1024 = 512 + 512 by omega,
      maskChunk_add, ha16_20, ha20_24]
    rfl
  have ha24_25 : maskChunk 3072 128 =
      StrongPackedBucketN12A2Aligned.missing24_25 := by
    exact hs24
  have ha25_26 : maskChunk 3200 128 =
      StrongPackedBucketN12A2Aligned.missing25_26 := by
    exact hs25
  have ha24_26 : maskChunk 3072 256 =
      StrongPackedBucketN12A2Aligned.missing24_26 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha24_25, ha25_26]
    rfl
  have ha26_27 : maskChunk 3328 128 =
      StrongPackedBucketN12A2Aligned.missing26_27 := by
    exact hs26
  have ha27_28 : maskChunk 3456 128 =
      StrongPackedBucketN12A2Aligned.missing27_28 := by
    exact hs27
  have ha26_28 : maskChunk 3328 256 =
      StrongPackedBucketN12A2Aligned.missing26_28 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha26_27, ha27_28]
    rfl
  have ha24_28 : maskChunk 3072 512 =
      StrongPackedBucketN12A2Aligned.missing24_28 := by
    rw [show 512 = 256 + 256 by omega,
      maskChunk_add, ha24_26, ha26_28]
    rfl
  have ha28_29 : maskChunk 3584 128 =
      StrongPackedBucketN12A2Aligned.missing28_29 := by
    exact hs28
  have ha29_30 : maskChunk 3712 128 =
      StrongPackedBucketN12A2Aligned.missing29_30 := by
    exact hs29
  have ha28_30 : maskChunk 3584 256 =
      StrongPackedBucketN12A2Aligned.missing28_30 := by
    rw [show 256 = 128 + 128 by omega,
      maskChunk_add, ha28_29, ha29_30]
    rfl
  have ha30_31 : maskChunk 3840 128 =
      StrongPackedBucketN12A2Aligned.missing30_31 := by
    exact hs30
  have ha31_32 : maskChunk 3968 128 =
      StrongPackedBucketN12A2Aligned.missing31_32 := by
    exact hs31
  have ha32_33 : maskChunk 4096 95 =
      StrongPackedBucketN12A2Aligned.missing32_33 := by
    exact hs32
  have ha31_33 : maskChunk 3968 223 =
      StrongPackedBucketN12A2Aligned.missing31_33 := by
    rw [show 223 = 128 + 95 by omega,
      maskChunk_add, ha31_32, ha32_33]
    rfl
  have ha30_33 : maskChunk 3840 351 =
      StrongPackedBucketN12A2Aligned.missing30_33 := by
    rw [show 351 = 128 + 223 by omega,
      maskChunk_add, ha30_31, ha31_33]
    rfl
  have ha28_33 : maskChunk 3584 607 =
      StrongPackedBucketN12A2Aligned.missing28_33 := by
    rw [show 607 = 256 + 351 by omega,
      maskChunk_add, ha28_30, ha30_33]
    rfl
  have ha24_33 : maskChunk 3072 1119 =
      StrongPackedBucketN12A2Aligned.missing24_33 := by
    rw [show 1119 = 512 + 607 by omega,
      maskChunk_add, ha24_28, ha28_33]
    rfl
  have ha16_33 : maskChunk 2048 2143 =
      StrongPackedBucketN12A2Aligned.missing16_33 := by
    rw [show 2143 = 1024 + 1119 by omega,
      maskChunk_add, ha16_24, ha24_33]
    rfl
  have ha0_33 : maskChunk 0 4191 =
      StrongPackedBucketN12A2Aligned.missing0_33 := by
    rw [show 4191 = 2048 + 2143 by omega,
      maskChunk_add, ha0_16, ha16_33]
    rfl
  calc
    PackedExhaustionN12.level10.toArray.toList =
        maskChunk 0 4191 := by
      exact level10_to_nativeMaskList.trans nativeMaskList_eq_maskChunk
    _ = StrongPackedBucketN12A2Aligned.missing := ha0_33

theorem alignedLevel10 :
    AlignedValid 12 2
      PackedExhaustionN12.level10.toArray.toList
      StrongPackedBucketN12A2Aligned.records := by
  rw [level10_toList_eq_missing]
  exact StrongPackedBucketN12A2Aligned.aligned

private lemma compl_edgeSet_ncard_eq_missingEdgeCount
    (G : SimpleGraph (Fin 12)) :
    Gᶜ.edgeSet.ncard = missingEdgeCount G := by
  classical
  exact Set.ncard_eq_toFinset_card' Gᶜ.edgeSet

theorem strongBase (G : SimpleGraph (Fin 12))
    (hmissing : missingEdgeCount G = 10) :
    HasStrongFractionalPacking G 2 := by
  have haligned :
      AlignedValid 12 2
        (PackedExhaustionN12Through10.data.level 10).toList
        StrongPackedBucketN12A2Aligned.records := by
    change AlignedValid 12 2
      PackedExhaustionN12.level10.toArray.toList
      StrongPackedBucketN12A2Aligned.records
    exact alignedLevel10
  have hcard : Gᶜ.edgeSet.ncard = 10 := by
    calc
      Gᶜ.edgeSet.ncard = missingEdgeCount G :=
        compl_edgeSet_ncard_eq_missingEdgeCount G
      _ = 10 := hmissing
  simpa using
    alignedValid_level_sound PackingCert.pairIndexValid_12
      PackedExhaustionN12Through10.valid (by decide) haligned G hcard

end Erdos76.CertificateChecker.Certificates.StrongBaseN12A2
