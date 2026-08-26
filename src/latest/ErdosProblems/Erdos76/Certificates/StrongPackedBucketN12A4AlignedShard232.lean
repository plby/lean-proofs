/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0.
-/
import ErdosProblems.Erdos76.PackedCertificateBridge
import ErdosProblems.Erdos76.Certificates.StrongPackedBucketN12A4Shard232

/-! Decode-only alignment checks for n=12, a=4, records 29696--29823. -/
namespace Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard232

open PackedBucketCertificate

def missing29696 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28392381589347106816
theorem maskCheck29696 :
    checkMaskFor missing29696 StrongPackedBucketN12A4Shard232.record29696 = true := by
  decide

def missing29697 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 29401187905878097920
theorem maskCheck29697 :
    checkMaskFor missing29697 StrongPackedBucketN12A4Shard232.record29697 = true := by
  decide

def missing29698 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30013677455200485376
theorem maskCheck29698 :
    checkMaskFor missing29698 StrongPackedBucketN12A4Shard232.record29698 = true := by
  decide

def missing29699 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30121763846257377280
theorem maskCheck29699 :
    checkMaskFor missing29699 StrongPackedBucketN12A4Shard232.record29699 = true := by
  decide

def missing29700 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 30554109410484944896
theorem maskCheck29700 :
    checkMaskFor missing29700 StrongPackedBucketN12A4Shard232.record29700 = true := by
  decide

def missing29701 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32319520464414179328
theorem maskCheck29701 :
    checkMaskFor missing29701 StrongPackedBucketN12A4Shard232.record29701 = true := by
  decide

def missing29702 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32427606855471071232
theorem maskCheck29702 :
    checkMaskFor missing29702 StrongPackedBucketN12A4Shard232.record29702 = true := by
  decide

def missing29703 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32859952419698638848
theorem maskCheck29703 :
    checkMaskFor missing29703 StrongPackedBucketN12A4Shard232.record29703 = true := by
  decide

def missing29704 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 34589334676608909312
theorem maskCheck29704 :
    checkMaskFor missing29704 StrongPackedBucketN12A4Shard232.record29704 = true := by
  decide

def missing29705 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37147379264955351040
theorem maskCheck29705 :
    checkMaskFor missing29705 StrongPackedBucketN12A4Shard232.record29705 = true := by
  decide

def missing29706 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37363552047069134848
theorem maskCheck29706 :
    checkMaskFor missing29706 StrongPackedBucketN12A4Shard232.record29706 = true := by
  decide

def missing29707 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37579724829182918656
theorem maskCheck29707 :
    checkMaskFor missing29707 StrongPackedBucketN12A4Shard232.record29707 = true := by
  decide

def missing29708 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37651782423220846592
theorem maskCheck29708 :
    checkMaskFor missing29708 StrongPackedBucketN12A4Shard232.record29708 = true := by
  decide

def missing29709 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37687811220239810560
theorem maskCheck29709 :
    checkMaskFor missing29709 StrongPackedBucketN12A4Shard232.record29709 = true := by
  decide

def missing29710 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 37903984002353594368
theorem maskCheck29710 :
    checkMaskFor missing29710 StrongPackedBucketN12A4Shard232.record29710 = true := by
  decide

def missing29711 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38660588739751837696
theorem maskCheck29711 :
    checkMaskFor missing29711 StrongPackedBucketN12A4Shard232.record29711 = true := by
  decide

def missing29712 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 38768675130808729600
theorem maskCheck29712 :
    checkMaskFor missing29712 StrongPackedBucketN12A4Shard232.record29712 = true := by
  decide

def missing29713 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39309107086093189120
theorem maskCheck29713 :
    checkMaskFor missing29713 StrongPackedBucketN12A4Shard232.record29713 = true := by
  decide

def missing29714 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39381164680131117056
theorem maskCheck29714 :
    checkMaskFor missing29714 StrongPackedBucketN12A4Shard232.record29714 = true := by
  decide

def missing29715 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39417193477150081024
theorem maskCheck29715 :
    checkMaskFor missing29715 StrongPackedBucketN12A4Shard232.record29715 = true := by
  decide

def missing29716 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39633366259263864832
theorem maskCheck29716 :
    checkMaskFor missing29716 StrongPackedBucketN12A4Shard232.record29716 = true := by
  decide

def missing29717 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39813510244358684672
theorem maskCheck29717 :
    checkMaskFor missing29717 StrongPackedBucketN12A4Shard232.record29717 = true := by
  decide

def missing29718 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 39921596635415576576
theorem maskCheck29718 :
    checkMaskFor missing29718 StrongPackedBucketN12A4Shard232.record29718 = true := by
  decide

def missing29719 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 40930402951946567680
theorem maskCheck29719 :
    checkMaskFor missing29719 StrongPackedBucketN12A4Shard232.record29719 = true := by
  decide

def missing29720 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41614950095306883072
theorem maskCheck29720 :
    checkMaskFor missing29720 StrongPackedBucketN12A4Shard232.record29720 = true := by
  decide

def missing29721 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41687007689344811008
theorem maskCheck29721 :
    checkMaskFor missing29721 StrongPackedBucketN12A4Shard232.record29721 = true := by
  decide

def missing29722 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41723036486363774976
theorem maskCheck29722 :
    checkMaskFor missing29722 StrongPackedBucketN12A4Shard232.record29722 = true := by
  decide

def missing29723 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 41939209268477558784
theorem maskCheck29723 :
    checkMaskFor missing29723 StrongPackedBucketN12A4Shard232.record29723 = true := by
  decide

def missing29724 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42119353253572378624
theorem maskCheck29724 :
    checkMaskFor missing29724 StrongPackedBucketN12A4Shard232.record29724 = true := by
  decide

def missing29725 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 42227439644629270528
theorem maskCheck29725 :
    checkMaskFor missing29725 StrongPackedBucketN12A4Shard232.record29725 = true := by
  decide

def missing29726 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43236245961160261632
theorem maskCheck29726 :
    checkMaskFor missing29726 StrongPackedBucketN12A4Shard232.record29726 = true := by
  decide

def missing29727 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43848735510482649088
theorem maskCheck29727 :
    checkMaskFor missing29727 StrongPackedBucketN12A4Shard232.record29727 = true := by
  decide

def missing29728 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 43956821901539540992
theorem maskCheck29728 :
    checkMaskFor missing29728 StrongPackedBucketN12A4Shard232.record29728 = true := by
  decide

def missing29729 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 44389167465767108608
theorem maskCheck29729 :
    checkMaskFor missing29729 StrongPackedBucketN12A4Shard232.record29729 = true := by
  decide

def missing29730 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46226636113734270976
theorem maskCheck29730 :
    checkMaskFor missing29730 StrongPackedBucketN12A4Shard232.record29730 = true := by
  decide

def missing29731 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46298693707772198912
theorem maskCheck29731 :
    checkMaskFor missing29731 StrongPackedBucketN12A4Shard232.record29731 = true := by
  decide

def missing29732 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46334722504791162880
theorem maskCheck29732 :
    checkMaskFor missing29732 StrongPackedBucketN12A4Shard232.record29732 = true := by
  decide

def missing29733 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46442808895848054784
theorem maskCheck29733 :
    checkMaskFor missing29733 StrongPackedBucketN12A4Shard232.record29733 = true := by
  decide

def missing29734 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46478837692867018752
theorem maskCheck29734 :
    checkMaskFor missing29734 StrongPackedBucketN12A4Shard232.record29734 = true := by
  decide

def missing29735 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46550895286904946688
theorem maskCheck29735 :
    checkMaskFor missing29735 StrongPackedBucketN12A4Shard232.record29735 = true := by
  decide

def missing29736 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46731039271999766528
theorem maskCheck29736 :
    checkMaskFor missing29736 StrongPackedBucketN12A4Shard232.record29736 = true := by
  decide

def missing29737 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46767068069018730496
theorem maskCheck29737 :
    checkMaskFor missing29737 StrongPackedBucketN12A4Shard232.record29737 = true := by
  decide

def missing29738 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46839125663056658432
theorem maskCheck29738 :
    checkMaskFor missing29738 StrongPackedBucketN12A4Shard232.record29738 = true := by
  decide

def missing29739 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 46983240851132514304
theorem maskCheck29739 :
    checkMaskFor missing29739 StrongPackedBucketN12A4Shard232.record29739 = true := by
  decide

def missing29740 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 47847931979587649536
theorem maskCheck29740 :
    checkMaskFor missing29740 StrongPackedBucketN12A4Shard232.record29740 = true := by
  decide

def missing29741 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48460421528910036992
theorem maskCheck29741 :
    checkMaskFor missing29741 StrongPackedBucketN12A4Shard232.record29741 = true := by
  decide

def missing29742 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48496450325929000960
theorem maskCheck29742 :
    checkMaskFor missing29742 StrongPackedBucketN12A4Shard232.record29742 = true := by
  decide

def missing29743 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48568507919966928896
theorem maskCheck29743 :
    checkMaskFor missing29743 StrongPackedBucketN12A4Shard232.record29743 = true := by
  decide

def missing29744 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 48712623108042784768
theorem maskCheck29744 :
    checkMaskFor missing29744 StrongPackedBucketN12A4Shard232.record29744 = true := by
  decide

def missing29745 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 49000853484194496512
theorem maskCheck29745 :
    checkMaskFor missing29745 StrongPackedBucketN12A4Shard232.record29745 = true := by
  decide

def missing29746 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50766264538123730944
theorem maskCheck29746 :
    checkMaskFor missing29746 StrongPackedBucketN12A4Shard232.record29746 = true := by
  decide

def missing29747 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50802293335142694912
theorem maskCheck29747 :
    checkMaskFor missing29747 StrongPackedBucketN12A4Shard232.record29747 = true := by
  decide

def missing29748 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 50874350929180622848
theorem maskCheck29748 :
    checkMaskFor missing29748 StrongPackedBucketN12A4Shard232.record29748 = true := by
  decide

def missing29749 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51018466117256478720
theorem maskCheck29749 :
    checkMaskFor missing29749 StrongPackedBucketN12A4Shard232.record29749 = true := by
  decide

def missing29750 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 51306696493408190464
theorem maskCheck29750 :
    checkMaskFor missing29750 StrongPackedBucketN12A4Shard232.record29750 = true := by
  decide

def missing29751 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 53036078750318460928
theorem maskCheck29751 :
    checkMaskFor missing29751 StrongPackedBucketN12A4Shard232.record29751 = true := by
  decide

def missing29752 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64601322593405894656
theorem maskCheck29752 :
    checkMaskFor missing29752 StrongPackedBucketN12A4Shard232.record29752 = true := by
  decide

def missing29753 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 64709408984462786560
theorem maskCheck29753 :
    checkMaskFor missing29753 StrongPackedBucketN12A4Shard232.record29753 = true := by
  decide

def missing29754 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 65141754548690354176
theorem maskCheck29754 :
    checkMaskFor missing29754 StrongPackedBucketN12A4Shard232.record29754 = true := by
  decide

def missing29755 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 66871136805600624640
theorem maskCheck29755 :
    checkMaskFor missing29755 StrongPackedBucketN12A4Shard232.record29755 = true := by
  decide

def missing29756 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 69176979814814318592
theorem maskCheck29756 :
    checkMaskFor missing29756 StrongPackedBucketN12A4Shard232.record29756 = true := by
  decide

def missing29757 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 504861243645886464
theorem maskCheck29757 :
    checkMaskFor missing29757 StrongPackedBucketN12A4Shard232.record29757 = true := by
  decide

def missing29758 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4828316885921562624
theorem maskCheck29758 :
    checkMaskFor missing29758 StrongPackedBucketN12A4Shard232.record29758 = true := by
  decide

def missing29759 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4972432073997418496
theorem maskCheck29759 :
    checkMaskFor missing29759 StrongPackedBucketN12A4Shard232.record29759 = true := by
  decide

def missing29760 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9440002904348950528
theorem maskCheck29760 :
    checkMaskFor missing29760 StrongPackedBucketN12A4Shard232.record29760 = true := by
  decide

def missing29761 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9584118092424806400
theorem maskCheck29761 :
    checkMaskFor missing29761 StrongPackedBucketN12A4Shard232.record29761 = true := by
  decide

def missing29762 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18663374941203726336
theorem maskCheck29762 :
    checkMaskFor missing29762 StrongPackedBucketN12A4Shard232.record29762 = true := by
  decide

def missing29763 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 253187430094471168
theorem maskCheck29763 :
    checkMaskFor missing29763 StrongPackedBucketN12A4Shard232.record29763 = true := by
  decide

def missing29764 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 469360212208254976
theorem maskCheck29764 :
    checkMaskFor missing29764 StrongPackedBucketN12A4Shard232.record29764 = true := by
  decide

def missing29765 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 685532994322038784
theorem maskCheck29765 :
    checkMaskFor missing29765 StrongPackedBucketN12A4Shard232.record29765 = true := by
  decide

def missing29766 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 757590588359966720
theorem maskCheck29766 :
    checkMaskFor missing29766 StrongPackedBucketN12A4Shard232.record29766 = true := by
  decide

def missing29767 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 1261993746625462272
theorem maskCheck29767 :
    checkMaskFor missing29767 StrongPackedBucketN12A4Shard232.record29767 = true := by
  decide

def missing29768 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4720758260446003200
theorem maskCheck29768 :
    checkMaskFor missing29768 StrongPackedBucketN12A4Shard232.record29768 = true := by
  decide

def missing29769 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4792815854483931136
theorem maskCheck29769 :
    checkMaskFor missing29769 StrongPackedBucketN12A4Shard232.record29769 = true := by
  decide

def missing29770 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4828844651502895104
theorem maskCheck29770 :
    checkMaskFor missing29770 StrongPackedBucketN12A4Shard232.record29770 = true := by
  decide

def missing29771 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 5045017433616678912
theorem maskCheck29771 :
    checkMaskFor missing29771 StrongPackedBucketN12A4Shard232.record29771 = true := by
  decide

def missing29772 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9332444278873391104
theorem maskCheck29772 :
    checkMaskFor missing29772 StrongPackedBucketN12A4Shard232.record29772 = true := by
  decide

def missing29773 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9440530669930283008
theorem maskCheck29773 :
    checkMaskFor missing29773 StrongPackedBucketN12A4Shard232.record29773 = true := by
  decide

def missing29774 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9548617060987174912
theorem maskCheck29774 :
    checkMaskFor missing29774 StrongPackedBucketN12A4Shard232.record29774 = true := by
  decide

def missing29775 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9584645858006138880
theorem maskCheck29775 :
    checkMaskFor missing29775 StrongPackedBucketN12A4Shard232.record29775 = true := by
  decide

def missing29776 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9656703452044066816
theorem maskCheck29776 :
    checkMaskFor missing29776 StrongPackedBucketN12A4Shard232.record29776 = true := by
  decide

def missing29777 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9872876234157850624
theorem maskCheck29777 :
    checkMaskFor missing29777 StrongPackedBucketN12A4Shard232.record29777 = true := by
  decide

def missing29778 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10449336986461274112
theorem maskCheck29778 :
    checkMaskFor missing29778 StrongPackedBucketN12A4Shard232.record29778 = true := by
  decide

def missing29779 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13872072703262851072
theorem maskCheck29779 :
    checkMaskFor missing29779 StrongPackedBucketN12A4Shard232.record29779 = true := by
  decide

def missing29780 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13908101500281815040
theorem maskCheck29780 :
    checkMaskFor missing29780 StrongPackedBucketN12A4Shard232.record29780 = true := by
  decide

def missing29781 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14124274282395598848
theorem maskCheck29781 :
    checkMaskFor missing29781 StrongPackedBucketN12A4Shard232.record29781 = true := by
  decide

def missing29782 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14412504658547310592
theorem maskCheck29782 :
    checkMaskFor missing29782 StrongPackedBucketN12A4Shard232.record29782 = true := by
  decide

def missing29783 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14988965410850734080
theorem maskCheck29783 :
    checkMaskFor missing29783 StrongPackedBucketN12A4Shard232.record29783 = true := by
  decide

def missing29784 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27707130758545014784
theorem maskCheck29784 :
    checkMaskFor missing29784 StrongPackedBucketN12A4Shard232.record29784 = true := by
  decide

def missing29785 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 27815217149601906688
theorem maskCheck29785 :
    checkMaskFor missing29785 StrongPackedBucketN12A4Shard232.record29785 = true := by
  decide

def missing29786 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28247562713829474304
theorem maskCheck29786 :
    checkMaskFor missing29786 StrongPackedBucketN12A4Shard232.record29786 = true := by
  decide

def missing29787 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 28824023466132897792
theorem maskCheck29787 :
    checkMaskFor missing29787 StrongPackedBucketN12A4Shard232.record29787 = true := by
  decide

def missing29788 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 32282787979953438720
theorem maskCheck29788 :
    checkMaskFor missing29788 StrongPackedBucketN12A4Shard232.record29788 = true := by
  decide

def missing29789 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 254031855024603136
theorem maskCheck29789 :
    checkMaskFor missing29789 StrongPackedBucketN12A4Shard232.record29789 = true := by
  decide

def missing29790 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 398147043100459008
theorem maskCheck29790 :
    checkMaskFor missing29790 StrongPackedBucketN12A4Shard232.record29790 = true := by
  decide

def missing29791 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 470204637138386944
theorem maskCheck29791 :
    checkMaskFor missing29791 StrongPackedBucketN12A4Shard232.record29791 = true := by
  decide

def missing29792 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 506233434157350912
theorem maskCheck29792 :
    checkMaskFor missing29792 StrongPackedBucketN12A4Shard232.record29792 = true := by
  decide

def missing29793 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 686377419252170752
theorem maskCheck29793 :
    checkMaskFor missing29793 StrongPackedBucketN12A4Shard232.record29793 = true := by
  decide

def missing29794 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 758435013290098688
theorem maskCheck29794 :
    checkMaskFor missing29794 StrongPackedBucketN12A4Shard232.record29794 = true := by
  decide

def missing29795 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2019442908953837568
theorem maskCheck29795 :
    checkMaskFor missing29795 StrongPackedBucketN12A4Shard232.record29795 = true := by
  decide

def missing29796 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2415759676162441216
theorem maskCheck29796 :
    checkMaskFor missing29796 StrongPackedBucketN12A4Shard232.record29796 = true := by
  decide

def missing29797 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 2487817270200369152
theorem maskCheck29797 :
    checkMaskFor missing29797 StrongPackedBucketN12A4Shard232.record29797 = true := by
  decide

def missing29798 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 3172364413560684544
theorem maskCheck29798 :
    checkMaskFor missing29798 StrongPackedBucketN12A4Shard232.record29798 = true := by
  decide

def missing29799 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4721602685376135168
theorem maskCheck29799 :
    checkMaskFor missing29799 StrongPackedBucketN12A4Shard232.record29799 = true := by
  decide

def missing29800 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4793660279414063104
theorem maskCheck29800 :
    checkMaskFor missing29800 StrongPackedBucketN12A4Shard232.record29800 = true := by
  decide

def missing29801 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4829689076433027072
theorem maskCheck29801 :
    checkMaskFor missing29801 StrongPackedBucketN12A4Shard232.record29801 = true := by
  decide

def missing29802 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 4973804264508882944
theorem maskCheck29802 :
    checkMaskFor missing29802 StrongPackedBucketN12A4Shard232.record29802 = true := by
  decide

def missing29803 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9333288703803523072
theorem maskCheck29803 :
    checkMaskFor missing29803 StrongPackedBucketN12A4Shard232.record29803 = true := by
  decide

def missing29804 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9441375094860414976
theorem maskCheck29804 :
    checkMaskFor missing29804 StrongPackedBucketN12A4Shard232.record29804 = true := by
  decide

def missing29805 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9549461485917306880
theorem maskCheck29805 :
    checkMaskFor missing29805 StrongPackedBucketN12A4Shard232.record29805 = true := by
  decide

def missing29806 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9585490282936270848
theorem maskCheck29806 :
    checkMaskFor missing29806 StrongPackedBucketN12A4Shard232.record29806 = true := by
  decide

def missing29807 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 9873720659087982592
theorem maskCheck29807 :
    checkMaskFor missing29807 StrongPackedBucketN12A4Shard232.record29807 = true := by
  decide

def missing29808 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 10089893441201766400
theorem maskCheck29808 :
    checkMaskFor missing29808 StrongPackedBucketN12A4Shard232.record29808 = true := by
  decide

def missing29809 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 11603102915998253056
theorem maskCheck29809 :
    checkMaskFor missing29809 StrongPackedBucketN12A4Shard232.record29809 = true := by
  decide

def missing29810 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13872917128192983040
theorem maskCheck29810 :
    checkMaskFor missing29810 StrongPackedBucketN12A4Shard232.record29810 = true := by
  decide

def missing29811 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13908945925211947008
theorem maskCheck29811 :
    checkMaskFor missing29811 StrongPackedBucketN12A4Shard232.record29811 = true := by
  decide

def missing29812 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 13981003519249874944
theorem maskCheck29812 :
    checkMaskFor missing29812 StrongPackedBucketN12A4Shard232.record29812 = true := by
  decide

def missing29813 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14125118707325730816
theorem maskCheck29813 :
    checkMaskFor missing29813 StrongPackedBucketN12A4Shard232.record29813 = true := by
  decide

def missing29814 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 14413349083477442560
theorem maskCheck29814 :
    checkMaskFor missing29814 StrongPackedBucketN12A4Shard232.record29814 = true := by
  decide

def missing29815 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 16142731340387713024
theorem maskCheck29815 :
    checkMaskFor missing29815 StrongPackedBucketN12A4Shard232.record29815 = true := by
  decide

def missing29816 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18556660740658298880
theorem maskCheck29816 :
    checkMaskFor missing29816 StrongPackedBucketN12A4Shard232.record29816 = true := by
  decide

def missing29817 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18628718334696226816
theorem maskCheck29817 :
    checkMaskFor missing29817 StrongPackedBucketN12A4Shard232.record29817 = true := by
  decide

def missing29818 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18664747131715190784
theorem maskCheck29818 :
    checkMaskFor missing29818 StrongPackedBucketN12A4Shard232.record29818 = true := by
  decide

def missing29819 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 18772833522772082688
theorem maskCheck29819 :
    checkMaskFor missing29819 StrongPackedBucketN12A4Shard232.record29819 = true := by
  decide

def missing29820 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 19061063898923794432
theorem maskCheck29820 :
    checkMaskFor missing29820 StrongPackedBucketN12A4Shard232.record29820 = true := by
  decide

def missing29821 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 20790446155834064896
theorem maskCheck29821 :
    checkMaskFor missing29821 StrongPackedBucketN12A4Shard232.record29821 = true := by
  decide

def missing29822 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23096289165047758848
theorem maskCheck29822 :
    checkMaskFor missing29822 StrongPackedBucketN12A4Shard232.record29822 = true := by
  decide

def missing29823 : BitVec (edgeCount 12) :=
  BitVec.ofNat (edgeCount 12) 23132317962066722816
theorem maskCheck29823 :
    checkMaskFor missing29823 StrongPackedBucketN12A4Shard232.record29823 = true := by
  decide

def missing29696_29697 : List (BitVec (edgeCount 12)) :=
  [missing29696]
abbrev records29696_29697 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29696]
theorem aligned29696_29697 :
    AlignedValid 12 4 missing29696_29697 records29696_29697 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29696
    maskCheck29696 AlignedValid.nil

def missing29697_29698 : List (BitVec (edgeCount 12)) :=
  [missing29697]
abbrev records29697_29698 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29697]
theorem aligned29697_29698 :
    AlignedValid 12 4 missing29697_29698 records29697_29698 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29697
    maskCheck29697 AlignedValid.nil

def missing29696_29698 : List (BitVec (edgeCount 12)) :=
  missing29696_29697 ++ missing29697_29698
abbrev records29696_29698 : List Blob :=
  records29696_29697 ++ records29697_29698
theorem aligned29696_29698 :
    AlignedValid 12 4 missing29696_29698 records29696_29698 :=
  aligned29696_29697.append aligned29697_29698

def missing29698_29699 : List (BitVec (edgeCount 12)) :=
  [missing29698]
abbrev records29698_29699 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29698]
theorem aligned29698_29699 :
    AlignedValid 12 4 missing29698_29699 records29698_29699 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29698
    maskCheck29698 AlignedValid.nil

def missing29699_29700 : List (BitVec (edgeCount 12)) :=
  [missing29699]
abbrev records29699_29700 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29699]
theorem aligned29699_29700 :
    AlignedValid 12 4 missing29699_29700 records29699_29700 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29699
    maskCheck29699 AlignedValid.nil

def missing29698_29700 : List (BitVec (edgeCount 12)) :=
  missing29698_29699 ++ missing29699_29700
abbrev records29698_29700 : List Blob :=
  records29698_29699 ++ records29699_29700
theorem aligned29698_29700 :
    AlignedValid 12 4 missing29698_29700 records29698_29700 :=
  aligned29698_29699.append aligned29699_29700

def missing29696_29700 : List (BitVec (edgeCount 12)) :=
  missing29696_29698 ++ missing29698_29700
abbrev records29696_29700 : List Blob :=
  records29696_29698 ++ records29698_29700
theorem aligned29696_29700 :
    AlignedValid 12 4 missing29696_29700 records29696_29700 :=
  aligned29696_29698.append aligned29698_29700

def missing29700_29701 : List (BitVec (edgeCount 12)) :=
  [missing29700]
abbrev records29700_29701 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29700]
theorem aligned29700_29701 :
    AlignedValid 12 4 missing29700_29701 records29700_29701 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29700
    maskCheck29700 AlignedValid.nil

def missing29701_29702 : List (BitVec (edgeCount 12)) :=
  [missing29701]
abbrev records29701_29702 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29701]
theorem aligned29701_29702 :
    AlignedValid 12 4 missing29701_29702 records29701_29702 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29701
    maskCheck29701 AlignedValid.nil

def missing29700_29702 : List (BitVec (edgeCount 12)) :=
  missing29700_29701 ++ missing29701_29702
abbrev records29700_29702 : List Blob :=
  records29700_29701 ++ records29701_29702
theorem aligned29700_29702 :
    AlignedValid 12 4 missing29700_29702 records29700_29702 :=
  aligned29700_29701.append aligned29701_29702

def missing29702_29703 : List (BitVec (edgeCount 12)) :=
  [missing29702]
abbrev records29702_29703 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29702]
theorem aligned29702_29703 :
    AlignedValid 12 4 missing29702_29703 records29702_29703 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29702
    maskCheck29702 AlignedValid.nil

def missing29703_29704 : List (BitVec (edgeCount 12)) :=
  [missing29703]
abbrev records29703_29704 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29703]
theorem aligned29703_29704 :
    AlignedValid 12 4 missing29703_29704 records29703_29704 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29703
    maskCheck29703 AlignedValid.nil

def missing29702_29704 : List (BitVec (edgeCount 12)) :=
  missing29702_29703 ++ missing29703_29704
abbrev records29702_29704 : List Blob :=
  records29702_29703 ++ records29703_29704
theorem aligned29702_29704 :
    AlignedValid 12 4 missing29702_29704 records29702_29704 :=
  aligned29702_29703.append aligned29703_29704

def missing29700_29704 : List (BitVec (edgeCount 12)) :=
  missing29700_29702 ++ missing29702_29704
abbrev records29700_29704 : List Blob :=
  records29700_29702 ++ records29702_29704
theorem aligned29700_29704 :
    AlignedValid 12 4 missing29700_29704 records29700_29704 :=
  aligned29700_29702.append aligned29702_29704

def missing29696_29704 : List (BitVec (edgeCount 12)) :=
  missing29696_29700 ++ missing29700_29704
abbrev records29696_29704 : List Blob :=
  records29696_29700 ++ records29700_29704
theorem aligned29696_29704 :
    AlignedValid 12 4 missing29696_29704 records29696_29704 :=
  aligned29696_29700.append aligned29700_29704

def missing29704_29705 : List (BitVec (edgeCount 12)) :=
  [missing29704]
abbrev records29704_29705 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29704]
theorem aligned29704_29705 :
    AlignedValid 12 4 missing29704_29705 records29704_29705 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29704
    maskCheck29704 AlignedValid.nil

def missing29705_29706 : List (BitVec (edgeCount 12)) :=
  [missing29705]
abbrev records29705_29706 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29705]
theorem aligned29705_29706 :
    AlignedValid 12 4 missing29705_29706 records29705_29706 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29705
    maskCheck29705 AlignedValid.nil

def missing29704_29706 : List (BitVec (edgeCount 12)) :=
  missing29704_29705 ++ missing29705_29706
abbrev records29704_29706 : List Blob :=
  records29704_29705 ++ records29705_29706
theorem aligned29704_29706 :
    AlignedValid 12 4 missing29704_29706 records29704_29706 :=
  aligned29704_29705.append aligned29705_29706

def missing29706_29707 : List (BitVec (edgeCount 12)) :=
  [missing29706]
abbrev records29706_29707 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29706]
theorem aligned29706_29707 :
    AlignedValid 12 4 missing29706_29707 records29706_29707 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29706
    maskCheck29706 AlignedValid.nil

def missing29707_29708 : List (BitVec (edgeCount 12)) :=
  [missing29707]
abbrev records29707_29708 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29707]
theorem aligned29707_29708 :
    AlignedValid 12 4 missing29707_29708 records29707_29708 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29707
    maskCheck29707 AlignedValid.nil

def missing29706_29708 : List (BitVec (edgeCount 12)) :=
  missing29706_29707 ++ missing29707_29708
abbrev records29706_29708 : List Blob :=
  records29706_29707 ++ records29707_29708
theorem aligned29706_29708 :
    AlignedValid 12 4 missing29706_29708 records29706_29708 :=
  aligned29706_29707.append aligned29707_29708

def missing29704_29708 : List (BitVec (edgeCount 12)) :=
  missing29704_29706 ++ missing29706_29708
abbrev records29704_29708 : List Blob :=
  records29704_29706 ++ records29706_29708
theorem aligned29704_29708 :
    AlignedValid 12 4 missing29704_29708 records29704_29708 :=
  aligned29704_29706.append aligned29706_29708

def missing29708_29709 : List (BitVec (edgeCount 12)) :=
  [missing29708]
abbrev records29708_29709 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29708]
theorem aligned29708_29709 :
    AlignedValid 12 4 missing29708_29709 records29708_29709 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29708
    maskCheck29708 AlignedValid.nil

def missing29709_29710 : List (BitVec (edgeCount 12)) :=
  [missing29709]
abbrev records29709_29710 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29709]
theorem aligned29709_29710 :
    AlignedValid 12 4 missing29709_29710 records29709_29710 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29709
    maskCheck29709 AlignedValid.nil

def missing29708_29710 : List (BitVec (edgeCount 12)) :=
  missing29708_29709 ++ missing29709_29710
abbrev records29708_29710 : List Blob :=
  records29708_29709 ++ records29709_29710
theorem aligned29708_29710 :
    AlignedValid 12 4 missing29708_29710 records29708_29710 :=
  aligned29708_29709.append aligned29709_29710

def missing29710_29711 : List (BitVec (edgeCount 12)) :=
  [missing29710]
abbrev records29710_29711 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29710]
theorem aligned29710_29711 :
    AlignedValid 12 4 missing29710_29711 records29710_29711 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29710
    maskCheck29710 AlignedValid.nil

def missing29711_29712 : List (BitVec (edgeCount 12)) :=
  [missing29711]
abbrev records29711_29712 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29711]
theorem aligned29711_29712 :
    AlignedValid 12 4 missing29711_29712 records29711_29712 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29711
    maskCheck29711 AlignedValid.nil

def missing29710_29712 : List (BitVec (edgeCount 12)) :=
  missing29710_29711 ++ missing29711_29712
abbrev records29710_29712 : List Blob :=
  records29710_29711 ++ records29711_29712
theorem aligned29710_29712 :
    AlignedValid 12 4 missing29710_29712 records29710_29712 :=
  aligned29710_29711.append aligned29711_29712

def missing29708_29712 : List (BitVec (edgeCount 12)) :=
  missing29708_29710 ++ missing29710_29712
abbrev records29708_29712 : List Blob :=
  records29708_29710 ++ records29710_29712
theorem aligned29708_29712 :
    AlignedValid 12 4 missing29708_29712 records29708_29712 :=
  aligned29708_29710.append aligned29710_29712

def missing29704_29712 : List (BitVec (edgeCount 12)) :=
  missing29704_29708 ++ missing29708_29712
abbrev records29704_29712 : List Blob :=
  records29704_29708 ++ records29708_29712
theorem aligned29704_29712 :
    AlignedValid 12 4 missing29704_29712 records29704_29712 :=
  aligned29704_29708.append aligned29708_29712

def missing29696_29712 : List (BitVec (edgeCount 12)) :=
  missing29696_29704 ++ missing29704_29712
abbrev records29696_29712 : List Blob :=
  records29696_29704 ++ records29704_29712
theorem aligned29696_29712 :
    AlignedValid 12 4 missing29696_29712 records29696_29712 :=
  aligned29696_29704.append aligned29704_29712

def missing29712_29713 : List (BitVec (edgeCount 12)) :=
  [missing29712]
abbrev records29712_29713 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29712]
theorem aligned29712_29713 :
    AlignedValid 12 4 missing29712_29713 records29712_29713 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29712
    maskCheck29712 AlignedValid.nil

def missing29713_29714 : List (BitVec (edgeCount 12)) :=
  [missing29713]
abbrev records29713_29714 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29713]
theorem aligned29713_29714 :
    AlignedValid 12 4 missing29713_29714 records29713_29714 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29713
    maskCheck29713 AlignedValid.nil

def missing29712_29714 : List (BitVec (edgeCount 12)) :=
  missing29712_29713 ++ missing29713_29714
abbrev records29712_29714 : List Blob :=
  records29712_29713 ++ records29713_29714
theorem aligned29712_29714 :
    AlignedValid 12 4 missing29712_29714 records29712_29714 :=
  aligned29712_29713.append aligned29713_29714

def missing29714_29715 : List (BitVec (edgeCount 12)) :=
  [missing29714]
abbrev records29714_29715 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29714]
theorem aligned29714_29715 :
    AlignedValid 12 4 missing29714_29715 records29714_29715 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29714
    maskCheck29714 AlignedValid.nil

def missing29715_29716 : List (BitVec (edgeCount 12)) :=
  [missing29715]
abbrev records29715_29716 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29715]
theorem aligned29715_29716 :
    AlignedValid 12 4 missing29715_29716 records29715_29716 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29715
    maskCheck29715 AlignedValid.nil

def missing29714_29716 : List (BitVec (edgeCount 12)) :=
  missing29714_29715 ++ missing29715_29716
abbrev records29714_29716 : List Blob :=
  records29714_29715 ++ records29715_29716
theorem aligned29714_29716 :
    AlignedValid 12 4 missing29714_29716 records29714_29716 :=
  aligned29714_29715.append aligned29715_29716

def missing29712_29716 : List (BitVec (edgeCount 12)) :=
  missing29712_29714 ++ missing29714_29716
abbrev records29712_29716 : List Blob :=
  records29712_29714 ++ records29714_29716
theorem aligned29712_29716 :
    AlignedValid 12 4 missing29712_29716 records29712_29716 :=
  aligned29712_29714.append aligned29714_29716

def missing29716_29717 : List (BitVec (edgeCount 12)) :=
  [missing29716]
abbrev records29716_29717 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29716]
theorem aligned29716_29717 :
    AlignedValid 12 4 missing29716_29717 records29716_29717 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29716
    maskCheck29716 AlignedValid.nil

def missing29717_29718 : List (BitVec (edgeCount 12)) :=
  [missing29717]
abbrev records29717_29718 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29717]
theorem aligned29717_29718 :
    AlignedValid 12 4 missing29717_29718 records29717_29718 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29717
    maskCheck29717 AlignedValid.nil

def missing29716_29718 : List (BitVec (edgeCount 12)) :=
  missing29716_29717 ++ missing29717_29718
abbrev records29716_29718 : List Blob :=
  records29716_29717 ++ records29717_29718
theorem aligned29716_29718 :
    AlignedValid 12 4 missing29716_29718 records29716_29718 :=
  aligned29716_29717.append aligned29717_29718

def missing29718_29719 : List (BitVec (edgeCount 12)) :=
  [missing29718]
abbrev records29718_29719 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29718]
theorem aligned29718_29719 :
    AlignedValid 12 4 missing29718_29719 records29718_29719 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29718
    maskCheck29718 AlignedValid.nil

def missing29719_29720 : List (BitVec (edgeCount 12)) :=
  [missing29719]
abbrev records29719_29720 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29719]
theorem aligned29719_29720 :
    AlignedValid 12 4 missing29719_29720 records29719_29720 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29719
    maskCheck29719 AlignedValid.nil

def missing29718_29720 : List (BitVec (edgeCount 12)) :=
  missing29718_29719 ++ missing29719_29720
abbrev records29718_29720 : List Blob :=
  records29718_29719 ++ records29719_29720
theorem aligned29718_29720 :
    AlignedValid 12 4 missing29718_29720 records29718_29720 :=
  aligned29718_29719.append aligned29719_29720

def missing29716_29720 : List (BitVec (edgeCount 12)) :=
  missing29716_29718 ++ missing29718_29720
abbrev records29716_29720 : List Blob :=
  records29716_29718 ++ records29718_29720
theorem aligned29716_29720 :
    AlignedValid 12 4 missing29716_29720 records29716_29720 :=
  aligned29716_29718.append aligned29718_29720

def missing29712_29720 : List (BitVec (edgeCount 12)) :=
  missing29712_29716 ++ missing29716_29720
abbrev records29712_29720 : List Blob :=
  records29712_29716 ++ records29716_29720
theorem aligned29712_29720 :
    AlignedValid 12 4 missing29712_29720 records29712_29720 :=
  aligned29712_29716.append aligned29716_29720

def missing29720_29721 : List (BitVec (edgeCount 12)) :=
  [missing29720]
abbrev records29720_29721 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29720]
theorem aligned29720_29721 :
    AlignedValid 12 4 missing29720_29721 records29720_29721 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29720
    maskCheck29720 AlignedValid.nil

def missing29721_29722 : List (BitVec (edgeCount 12)) :=
  [missing29721]
abbrev records29721_29722 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29721]
theorem aligned29721_29722 :
    AlignedValid 12 4 missing29721_29722 records29721_29722 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29721
    maskCheck29721 AlignedValid.nil

def missing29720_29722 : List (BitVec (edgeCount 12)) :=
  missing29720_29721 ++ missing29721_29722
abbrev records29720_29722 : List Blob :=
  records29720_29721 ++ records29721_29722
theorem aligned29720_29722 :
    AlignedValid 12 4 missing29720_29722 records29720_29722 :=
  aligned29720_29721.append aligned29721_29722

def missing29722_29723 : List (BitVec (edgeCount 12)) :=
  [missing29722]
abbrev records29722_29723 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29722]
theorem aligned29722_29723 :
    AlignedValid 12 4 missing29722_29723 records29722_29723 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29722
    maskCheck29722 AlignedValid.nil

def missing29723_29724 : List (BitVec (edgeCount 12)) :=
  [missing29723]
abbrev records29723_29724 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29723]
theorem aligned29723_29724 :
    AlignedValid 12 4 missing29723_29724 records29723_29724 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29723
    maskCheck29723 AlignedValid.nil

def missing29722_29724 : List (BitVec (edgeCount 12)) :=
  missing29722_29723 ++ missing29723_29724
abbrev records29722_29724 : List Blob :=
  records29722_29723 ++ records29723_29724
theorem aligned29722_29724 :
    AlignedValid 12 4 missing29722_29724 records29722_29724 :=
  aligned29722_29723.append aligned29723_29724

def missing29720_29724 : List (BitVec (edgeCount 12)) :=
  missing29720_29722 ++ missing29722_29724
abbrev records29720_29724 : List Blob :=
  records29720_29722 ++ records29722_29724
theorem aligned29720_29724 :
    AlignedValid 12 4 missing29720_29724 records29720_29724 :=
  aligned29720_29722.append aligned29722_29724

def missing29724_29725 : List (BitVec (edgeCount 12)) :=
  [missing29724]
abbrev records29724_29725 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29724]
theorem aligned29724_29725 :
    AlignedValid 12 4 missing29724_29725 records29724_29725 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29724
    maskCheck29724 AlignedValid.nil

def missing29725_29726 : List (BitVec (edgeCount 12)) :=
  [missing29725]
abbrev records29725_29726 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29725]
theorem aligned29725_29726 :
    AlignedValid 12 4 missing29725_29726 records29725_29726 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29725
    maskCheck29725 AlignedValid.nil

def missing29724_29726 : List (BitVec (edgeCount 12)) :=
  missing29724_29725 ++ missing29725_29726
abbrev records29724_29726 : List Blob :=
  records29724_29725 ++ records29725_29726
theorem aligned29724_29726 :
    AlignedValid 12 4 missing29724_29726 records29724_29726 :=
  aligned29724_29725.append aligned29725_29726

def missing29726_29727 : List (BitVec (edgeCount 12)) :=
  [missing29726]
abbrev records29726_29727 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29726]
theorem aligned29726_29727 :
    AlignedValid 12 4 missing29726_29727 records29726_29727 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29726
    maskCheck29726 AlignedValid.nil

def missing29727_29728 : List (BitVec (edgeCount 12)) :=
  [missing29727]
abbrev records29727_29728 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29727]
theorem aligned29727_29728 :
    AlignedValid 12 4 missing29727_29728 records29727_29728 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29727
    maskCheck29727 AlignedValid.nil

def missing29726_29728 : List (BitVec (edgeCount 12)) :=
  missing29726_29727 ++ missing29727_29728
abbrev records29726_29728 : List Blob :=
  records29726_29727 ++ records29727_29728
theorem aligned29726_29728 :
    AlignedValid 12 4 missing29726_29728 records29726_29728 :=
  aligned29726_29727.append aligned29727_29728

def missing29724_29728 : List (BitVec (edgeCount 12)) :=
  missing29724_29726 ++ missing29726_29728
abbrev records29724_29728 : List Blob :=
  records29724_29726 ++ records29726_29728
theorem aligned29724_29728 :
    AlignedValid 12 4 missing29724_29728 records29724_29728 :=
  aligned29724_29726.append aligned29726_29728

def missing29720_29728 : List (BitVec (edgeCount 12)) :=
  missing29720_29724 ++ missing29724_29728
abbrev records29720_29728 : List Blob :=
  records29720_29724 ++ records29724_29728
theorem aligned29720_29728 :
    AlignedValid 12 4 missing29720_29728 records29720_29728 :=
  aligned29720_29724.append aligned29724_29728

def missing29712_29728 : List (BitVec (edgeCount 12)) :=
  missing29712_29720 ++ missing29720_29728
abbrev records29712_29728 : List Blob :=
  records29712_29720 ++ records29720_29728
theorem aligned29712_29728 :
    AlignedValid 12 4 missing29712_29728 records29712_29728 :=
  aligned29712_29720.append aligned29720_29728

def missing29696_29728 : List (BitVec (edgeCount 12)) :=
  missing29696_29712 ++ missing29712_29728
abbrev records29696_29728 : List Blob :=
  records29696_29712 ++ records29712_29728
theorem aligned29696_29728 :
    AlignedValid 12 4 missing29696_29728 records29696_29728 :=
  aligned29696_29712.append aligned29712_29728

def missing29728_29729 : List (BitVec (edgeCount 12)) :=
  [missing29728]
abbrev records29728_29729 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29728]
theorem aligned29728_29729 :
    AlignedValid 12 4 missing29728_29729 records29728_29729 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29728
    maskCheck29728 AlignedValid.nil

def missing29729_29730 : List (BitVec (edgeCount 12)) :=
  [missing29729]
abbrev records29729_29730 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29729]
theorem aligned29729_29730 :
    AlignedValid 12 4 missing29729_29730 records29729_29730 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29729
    maskCheck29729 AlignedValid.nil

def missing29728_29730 : List (BitVec (edgeCount 12)) :=
  missing29728_29729 ++ missing29729_29730
abbrev records29728_29730 : List Blob :=
  records29728_29729 ++ records29729_29730
theorem aligned29728_29730 :
    AlignedValid 12 4 missing29728_29730 records29728_29730 :=
  aligned29728_29729.append aligned29729_29730

def missing29730_29731 : List (BitVec (edgeCount 12)) :=
  [missing29730]
abbrev records29730_29731 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29730]
theorem aligned29730_29731 :
    AlignedValid 12 4 missing29730_29731 records29730_29731 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29730
    maskCheck29730 AlignedValid.nil

def missing29731_29732 : List (BitVec (edgeCount 12)) :=
  [missing29731]
abbrev records29731_29732 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29731]
theorem aligned29731_29732 :
    AlignedValid 12 4 missing29731_29732 records29731_29732 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29731
    maskCheck29731 AlignedValid.nil

def missing29730_29732 : List (BitVec (edgeCount 12)) :=
  missing29730_29731 ++ missing29731_29732
abbrev records29730_29732 : List Blob :=
  records29730_29731 ++ records29731_29732
theorem aligned29730_29732 :
    AlignedValid 12 4 missing29730_29732 records29730_29732 :=
  aligned29730_29731.append aligned29731_29732

def missing29728_29732 : List (BitVec (edgeCount 12)) :=
  missing29728_29730 ++ missing29730_29732
abbrev records29728_29732 : List Blob :=
  records29728_29730 ++ records29730_29732
theorem aligned29728_29732 :
    AlignedValid 12 4 missing29728_29732 records29728_29732 :=
  aligned29728_29730.append aligned29730_29732

def missing29732_29733 : List (BitVec (edgeCount 12)) :=
  [missing29732]
abbrev records29732_29733 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29732]
theorem aligned29732_29733 :
    AlignedValid 12 4 missing29732_29733 records29732_29733 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29732
    maskCheck29732 AlignedValid.nil

def missing29733_29734 : List (BitVec (edgeCount 12)) :=
  [missing29733]
abbrev records29733_29734 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29733]
theorem aligned29733_29734 :
    AlignedValid 12 4 missing29733_29734 records29733_29734 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29733
    maskCheck29733 AlignedValid.nil

def missing29732_29734 : List (BitVec (edgeCount 12)) :=
  missing29732_29733 ++ missing29733_29734
abbrev records29732_29734 : List Blob :=
  records29732_29733 ++ records29733_29734
theorem aligned29732_29734 :
    AlignedValid 12 4 missing29732_29734 records29732_29734 :=
  aligned29732_29733.append aligned29733_29734

def missing29734_29735 : List (BitVec (edgeCount 12)) :=
  [missing29734]
abbrev records29734_29735 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29734]
theorem aligned29734_29735 :
    AlignedValid 12 4 missing29734_29735 records29734_29735 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29734
    maskCheck29734 AlignedValid.nil

def missing29735_29736 : List (BitVec (edgeCount 12)) :=
  [missing29735]
abbrev records29735_29736 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29735]
theorem aligned29735_29736 :
    AlignedValid 12 4 missing29735_29736 records29735_29736 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29735
    maskCheck29735 AlignedValid.nil

def missing29734_29736 : List (BitVec (edgeCount 12)) :=
  missing29734_29735 ++ missing29735_29736
abbrev records29734_29736 : List Blob :=
  records29734_29735 ++ records29735_29736
theorem aligned29734_29736 :
    AlignedValid 12 4 missing29734_29736 records29734_29736 :=
  aligned29734_29735.append aligned29735_29736

def missing29732_29736 : List (BitVec (edgeCount 12)) :=
  missing29732_29734 ++ missing29734_29736
abbrev records29732_29736 : List Blob :=
  records29732_29734 ++ records29734_29736
theorem aligned29732_29736 :
    AlignedValid 12 4 missing29732_29736 records29732_29736 :=
  aligned29732_29734.append aligned29734_29736

def missing29728_29736 : List (BitVec (edgeCount 12)) :=
  missing29728_29732 ++ missing29732_29736
abbrev records29728_29736 : List Blob :=
  records29728_29732 ++ records29732_29736
theorem aligned29728_29736 :
    AlignedValid 12 4 missing29728_29736 records29728_29736 :=
  aligned29728_29732.append aligned29732_29736

def missing29736_29737 : List (BitVec (edgeCount 12)) :=
  [missing29736]
abbrev records29736_29737 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29736]
theorem aligned29736_29737 :
    AlignedValid 12 4 missing29736_29737 records29736_29737 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29736
    maskCheck29736 AlignedValid.nil

def missing29737_29738 : List (BitVec (edgeCount 12)) :=
  [missing29737]
abbrev records29737_29738 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29737]
theorem aligned29737_29738 :
    AlignedValid 12 4 missing29737_29738 records29737_29738 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29737
    maskCheck29737 AlignedValid.nil

def missing29736_29738 : List (BitVec (edgeCount 12)) :=
  missing29736_29737 ++ missing29737_29738
abbrev records29736_29738 : List Blob :=
  records29736_29737 ++ records29737_29738
theorem aligned29736_29738 :
    AlignedValid 12 4 missing29736_29738 records29736_29738 :=
  aligned29736_29737.append aligned29737_29738

def missing29738_29739 : List (BitVec (edgeCount 12)) :=
  [missing29738]
abbrev records29738_29739 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29738]
theorem aligned29738_29739 :
    AlignedValid 12 4 missing29738_29739 records29738_29739 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29738
    maskCheck29738 AlignedValid.nil

def missing29739_29740 : List (BitVec (edgeCount 12)) :=
  [missing29739]
abbrev records29739_29740 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29739]
theorem aligned29739_29740 :
    AlignedValid 12 4 missing29739_29740 records29739_29740 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29739
    maskCheck29739 AlignedValid.nil

def missing29738_29740 : List (BitVec (edgeCount 12)) :=
  missing29738_29739 ++ missing29739_29740
abbrev records29738_29740 : List Blob :=
  records29738_29739 ++ records29739_29740
theorem aligned29738_29740 :
    AlignedValid 12 4 missing29738_29740 records29738_29740 :=
  aligned29738_29739.append aligned29739_29740

def missing29736_29740 : List (BitVec (edgeCount 12)) :=
  missing29736_29738 ++ missing29738_29740
abbrev records29736_29740 : List Blob :=
  records29736_29738 ++ records29738_29740
theorem aligned29736_29740 :
    AlignedValid 12 4 missing29736_29740 records29736_29740 :=
  aligned29736_29738.append aligned29738_29740

def missing29740_29741 : List (BitVec (edgeCount 12)) :=
  [missing29740]
abbrev records29740_29741 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29740]
theorem aligned29740_29741 :
    AlignedValid 12 4 missing29740_29741 records29740_29741 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29740
    maskCheck29740 AlignedValid.nil

def missing29741_29742 : List (BitVec (edgeCount 12)) :=
  [missing29741]
abbrev records29741_29742 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29741]
theorem aligned29741_29742 :
    AlignedValid 12 4 missing29741_29742 records29741_29742 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29741
    maskCheck29741 AlignedValid.nil

def missing29740_29742 : List (BitVec (edgeCount 12)) :=
  missing29740_29741 ++ missing29741_29742
abbrev records29740_29742 : List Blob :=
  records29740_29741 ++ records29741_29742
theorem aligned29740_29742 :
    AlignedValid 12 4 missing29740_29742 records29740_29742 :=
  aligned29740_29741.append aligned29741_29742

def missing29742_29743 : List (BitVec (edgeCount 12)) :=
  [missing29742]
abbrev records29742_29743 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29742]
theorem aligned29742_29743 :
    AlignedValid 12 4 missing29742_29743 records29742_29743 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29742
    maskCheck29742 AlignedValid.nil

def missing29743_29744 : List (BitVec (edgeCount 12)) :=
  [missing29743]
abbrev records29743_29744 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29743]
theorem aligned29743_29744 :
    AlignedValid 12 4 missing29743_29744 records29743_29744 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29743
    maskCheck29743 AlignedValid.nil

def missing29742_29744 : List (BitVec (edgeCount 12)) :=
  missing29742_29743 ++ missing29743_29744
abbrev records29742_29744 : List Blob :=
  records29742_29743 ++ records29743_29744
theorem aligned29742_29744 :
    AlignedValid 12 4 missing29742_29744 records29742_29744 :=
  aligned29742_29743.append aligned29743_29744

def missing29740_29744 : List (BitVec (edgeCount 12)) :=
  missing29740_29742 ++ missing29742_29744
abbrev records29740_29744 : List Blob :=
  records29740_29742 ++ records29742_29744
theorem aligned29740_29744 :
    AlignedValid 12 4 missing29740_29744 records29740_29744 :=
  aligned29740_29742.append aligned29742_29744

def missing29736_29744 : List (BitVec (edgeCount 12)) :=
  missing29736_29740 ++ missing29740_29744
abbrev records29736_29744 : List Blob :=
  records29736_29740 ++ records29740_29744
theorem aligned29736_29744 :
    AlignedValid 12 4 missing29736_29744 records29736_29744 :=
  aligned29736_29740.append aligned29740_29744

def missing29728_29744 : List (BitVec (edgeCount 12)) :=
  missing29728_29736 ++ missing29736_29744
abbrev records29728_29744 : List Blob :=
  records29728_29736 ++ records29736_29744
theorem aligned29728_29744 :
    AlignedValid 12 4 missing29728_29744 records29728_29744 :=
  aligned29728_29736.append aligned29736_29744

def missing29744_29745 : List (BitVec (edgeCount 12)) :=
  [missing29744]
abbrev records29744_29745 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29744]
theorem aligned29744_29745 :
    AlignedValid 12 4 missing29744_29745 records29744_29745 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29744
    maskCheck29744 AlignedValid.nil

def missing29745_29746 : List (BitVec (edgeCount 12)) :=
  [missing29745]
abbrev records29745_29746 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29745]
theorem aligned29745_29746 :
    AlignedValid 12 4 missing29745_29746 records29745_29746 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29745
    maskCheck29745 AlignedValid.nil

def missing29744_29746 : List (BitVec (edgeCount 12)) :=
  missing29744_29745 ++ missing29745_29746
abbrev records29744_29746 : List Blob :=
  records29744_29745 ++ records29745_29746
theorem aligned29744_29746 :
    AlignedValid 12 4 missing29744_29746 records29744_29746 :=
  aligned29744_29745.append aligned29745_29746

def missing29746_29747 : List (BitVec (edgeCount 12)) :=
  [missing29746]
abbrev records29746_29747 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29746]
theorem aligned29746_29747 :
    AlignedValid 12 4 missing29746_29747 records29746_29747 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29746
    maskCheck29746 AlignedValid.nil

def missing29747_29748 : List (BitVec (edgeCount 12)) :=
  [missing29747]
abbrev records29747_29748 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29747]
theorem aligned29747_29748 :
    AlignedValid 12 4 missing29747_29748 records29747_29748 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29747
    maskCheck29747 AlignedValid.nil

def missing29746_29748 : List (BitVec (edgeCount 12)) :=
  missing29746_29747 ++ missing29747_29748
abbrev records29746_29748 : List Blob :=
  records29746_29747 ++ records29747_29748
theorem aligned29746_29748 :
    AlignedValid 12 4 missing29746_29748 records29746_29748 :=
  aligned29746_29747.append aligned29747_29748

def missing29744_29748 : List (BitVec (edgeCount 12)) :=
  missing29744_29746 ++ missing29746_29748
abbrev records29744_29748 : List Blob :=
  records29744_29746 ++ records29746_29748
theorem aligned29744_29748 :
    AlignedValid 12 4 missing29744_29748 records29744_29748 :=
  aligned29744_29746.append aligned29746_29748

def missing29748_29749 : List (BitVec (edgeCount 12)) :=
  [missing29748]
abbrev records29748_29749 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29748]
theorem aligned29748_29749 :
    AlignedValid 12 4 missing29748_29749 records29748_29749 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29748
    maskCheck29748 AlignedValid.nil

def missing29749_29750 : List (BitVec (edgeCount 12)) :=
  [missing29749]
abbrev records29749_29750 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29749]
theorem aligned29749_29750 :
    AlignedValid 12 4 missing29749_29750 records29749_29750 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29749
    maskCheck29749 AlignedValid.nil

def missing29748_29750 : List (BitVec (edgeCount 12)) :=
  missing29748_29749 ++ missing29749_29750
abbrev records29748_29750 : List Blob :=
  records29748_29749 ++ records29749_29750
theorem aligned29748_29750 :
    AlignedValid 12 4 missing29748_29750 records29748_29750 :=
  aligned29748_29749.append aligned29749_29750

def missing29750_29751 : List (BitVec (edgeCount 12)) :=
  [missing29750]
abbrev records29750_29751 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29750]
theorem aligned29750_29751 :
    AlignedValid 12 4 missing29750_29751 records29750_29751 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29750
    maskCheck29750 AlignedValid.nil

def missing29751_29752 : List (BitVec (edgeCount 12)) :=
  [missing29751]
abbrev records29751_29752 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29751]
theorem aligned29751_29752 :
    AlignedValid 12 4 missing29751_29752 records29751_29752 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29751
    maskCheck29751 AlignedValid.nil

def missing29750_29752 : List (BitVec (edgeCount 12)) :=
  missing29750_29751 ++ missing29751_29752
abbrev records29750_29752 : List Blob :=
  records29750_29751 ++ records29751_29752
theorem aligned29750_29752 :
    AlignedValid 12 4 missing29750_29752 records29750_29752 :=
  aligned29750_29751.append aligned29751_29752

def missing29748_29752 : List (BitVec (edgeCount 12)) :=
  missing29748_29750 ++ missing29750_29752
abbrev records29748_29752 : List Blob :=
  records29748_29750 ++ records29750_29752
theorem aligned29748_29752 :
    AlignedValid 12 4 missing29748_29752 records29748_29752 :=
  aligned29748_29750.append aligned29750_29752

def missing29744_29752 : List (BitVec (edgeCount 12)) :=
  missing29744_29748 ++ missing29748_29752
abbrev records29744_29752 : List Blob :=
  records29744_29748 ++ records29748_29752
theorem aligned29744_29752 :
    AlignedValid 12 4 missing29744_29752 records29744_29752 :=
  aligned29744_29748.append aligned29748_29752

def missing29752_29753 : List (BitVec (edgeCount 12)) :=
  [missing29752]
abbrev records29752_29753 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29752]
theorem aligned29752_29753 :
    AlignedValid 12 4 missing29752_29753 records29752_29753 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29752
    maskCheck29752 AlignedValid.nil

def missing29753_29754 : List (BitVec (edgeCount 12)) :=
  [missing29753]
abbrev records29753_29754 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29753]
theorem aligned29753_29754 :
    AlignedValid 12 4 missing29753_29754 records29753_29754 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29753
    maskCheck29753 AlignedValid.nil

def missing29752_29754 : List (BitVec (edgeCount 12)) :=
  missing29752_29753 ++ missing29753_29754
abbrev records29752_29754 : List Blob :=
  records29752_29753 ++ records29753_29754
theorem aligned29752_29754 :
    AlignedValid 12 4 missing29752_29754 records29752_29754 :=
  aligned29752_29753.append aligned29753_29754

def missing29754_29755 : List (BitVec (edgeCount 12)) :=
  [missing29754]
abbrev records29754_29755 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29754]
theorem aligned29754_29755 :
    AlignedValid 12 4 missing29754_29755 records29754_29755 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29754
    maskCheck29754 AlignedValid.nil

def missing29755_29756 : List (BitVec (edgeCount 12)) :=
  [missing29755]
abbrev records29755_29756 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29755]
theorem aligned29755_29756 :
    AlignedValid 12 4 missing29755_29756 records29755_29756 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29755
    maskCheck29755 AlignedValid.nil

def missing29754_29756 : List (BitVec (edgeCount 12)) :=
  missing29754_29755 ++ missing29755_29756
abbrev records29754_29756 : List Blob :=
  records29754_29755 ++ records29755_29756
theorem aligned29754_29756 :
    AlignedValid 12 4 missing29754_29756 records29754_29756 :=
  aligned29754_29755.append aligned29755_29756

def missing29752_29756 : List (BitVec (edgeCount 12)) :=
  missing29752_29754 ++ missing29754_29756
abbrev records29752_29756 : List Blob :=
  records29752_29754 ++ records29754_29756
theorem aligned29752_29756 :
    AlignedValid 12 4 missing29752_29756 records29752_29756 :=
  aligned29752_29754.append aligned29754_29756

def missing29756_29757 : List (BitVec (edgeCount 12)) :=
  [missing29756]
abbrev records29756_29757 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29756]
theorem aligned29756_29757 :
    AlignedValid 12 4 missing29756_29757 records29756_29757 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29756
    maskCheck29756 AlignedValid.nil

def missing29757_29758 : List (BitVec (edgeCount 12)) :=
  [missing29757]
abbrev records29757_29758 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29757]
theorem aligned29757_29758 :
    AlignedValid 12 4 missing29757_29758 records29757_29758 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29757
    maskCheck29757 AlignedValid.nil

def missing29756_29758 : List (BitVec (edgeCount 12)) :=
  missing29756_29757 ++ missing29757_29758
abbrev records29756_29758 : List Blob :=
  records29756_29757 ++ records29757_29758
theorem aligned29756_29758 :
    AlignedValid 12 4 missing29756_29758 records29756_29758 :=
  aligned29756_29757.append aligned29757_29758

def missing29758_29759 : List (BitVec (edgeCount 12)) :=
  [missing29758]
abbrev records29758_29759 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29758]
theorem aligned29758_29759 :
    AlignedValid 12 4 missing29758_29759 records29758_29759 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29758
    maskCheck29758 AlignedValid.nil

def missing29759_29760 : List (BitVec (edgeCount 12)) :=
  [missing29759]
abbrev records29759_29760 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29759]
theorem aligned29759_29760 :
    AlignedValid 12 4 missing29759_29760 records29759_29760 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29759
    maskCheck29759 AlignedValid.nil

def missing29758_29760 : List (BitVec (edgeCount 12)) :=
  missing29758_29759 ++ missing29759_29760
abbrev records29758_29760 : List Blob :=
  records29758_29759 ++ records29759_29760
theorem aligned29758_29760 :
    AlignedValid 12 4 missing29758_29760 records29758_29760 :=
  aligned29758_29759.append aligned29759_29760

def missing29756_29760 : List (BitVec (edgeCount 12)) :=
  missing29756_29758 ++ missing29758_29760
abbrev records29756_29760 : List Blob :=
  records29756_29758 ++ records29758_29760
theorem aligned29756_29760 :
    AlignedValid 12 4 missing29756_29760 records29756_29760 :=
  aligned29756_29758.append aligned29758_29760

def missing29752_29760 : List (BitVec (edgeCount 12)) :=
  missing29752_29756 ++ missing29756_29760
abbrev records29752_29760 : List Blob :=
  records29752_29756 ++ records29756_29760
theorem aligned29752_29760 :
    AlignedValid 12 4 missing29752_29760 records29752_29760 :=
  aligned29752_29756.append aligned29756_29760

def missing29744_29760 : List (BitVec (edgeCount 12)) :=
  missing29744_29752 ++ missing29752_29760
abbrev records29744_29760 : List Blob :=
  records29744_29752 ++ records29752_29760
theorem aligned29744_29760 :
    AlignedValid 12 4 missing29744_29760 records29744_29760 :=
  aligned29744_29752.append aligned29752_29760

def missing29728_29760 : List (BitVec (edgeCount 12)) :=
  missing29728_29744 ++ missing29744_29760
abbrev records29728_29760 : List Blob :=
  records29728_29744 ++ records29744_29760
theorem aligned29728_29760 :
    AlignedValid 12 4 missing29728_29760 records29728_29760 :=
  aligned29728_29744.append aligned29744_29760

def missing29696_29760 : List (BitVec (edgeCount 12)) :=
  missing29696_29728 ++ missing29728_29760
abbrev records29696_29760 : List Blob :=
  records29696_29728 ++ records29728_29760
theorem aligned29696_29760 :
    AlignedValid 12 4 missing29696_29760 records29696_29760 :=
  aligned29696_29728.append aligned29728_29760

def missing29760_29761 : List (BitVec (edgeCount 12)) :=
  [missing29760]
abbrev records29760_29761 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29760]
theorem aligned29760_29761 :
    AlignedValid 12 4 missing29760_29761 records29760_29761 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29760
    maskCheck29760 AlignedValid.nil

def missing29761_29762 : List (BitVec (edgeCount 12)) :=
  [missing29761]
abbrev records29761_29762 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29761]
theorem aligned29761_29762 :
    AlignedValid 12 4 missing29761_29762 records29761_29762 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29761
    maskCheck29761 AlignedValid.nil

def missing29760_29762 : List (BitVec (edgeCount 12)) :=
  missing29760_29761 ++ missing29761_29762
abbrev records29760_29762 : List Blob :=
  records29760_29761 ++ records29761_29762
theorem aligned29760_29762 :
    AlignedValid 12 4 missing29760_29762 records29760_29762 :=
  aligned29760_29761.append aligned29761_29762

def missing29762_29763 : List (BitVec (edgeCount 12)) :=
  [missing29762]
abbrev records29762_29763 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29762]
theorem aligned29762_29763 :
    AlignedValid 12 4 missing29762_29763 records29762_29763 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29762
    maskCheck29762 AlignedValid.nil

def missing29763_29764 : List (BitVec (edgeCount 12)) :=
  [missing29763]
abbrev records29763_29764 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29763]
theorem aligned29763_29764 :
    AlignedValid 12 4 missing29763_29764 records29763_29764 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29763
    maskCheck29763 AlignedValid.nil

def missing29762_29764 : List (BitVec (edgeCount 12)) :=
  missing29762_29763 ++ missing29763_29764
abbrev records29762_29764 : List Blob :=
  records29762_29763 ++ records29763_29764
theorem aligned29762_29764 :
    AlignedValid 12 4 missing29762_29764 records29762_29764 :=
  aligned29762_29763.append aligned29763_29764

def missing29760_29764 : List (BitVec (edgeCount 12)) :=
  missing29760_29762 ++ missing29762_29764
abbrev records29760_29764 : List Blob :=
  records29760_29762 ++ records29762_29764
theorem aligned29760_29764 :
    AlignedValid 12 4 missing29760_29764 records29760_29764 :=
  aligned29760_29762.append aligned29762_29764

def missing29764_29765 : List (BitVec (edgeCount 12)) :=
  [missing29764]
abbrev records29764_29765 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29764]
theorem aligned29764_29765 :
    AlignedValid 12 4 missing29764_29765 records29764_29765 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29764
    maskCheck29764 AlignedValid.nil

def missing29765_29766 : List (BitVec (edgeCount 12)) :=
  [missing29765]
abbrev records29765_29766 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29765]
theorem aligned29765_29766 :
    AlignedValid 12 4 missing29765_29766 records29765_29766 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29765
    maskCheck29765 AlignedValid.nil

def missing29764_29766 : List (BitVec (edgeCount 12)) :=
  missing29764_29765 ++ missing29765_29766
abbrev records29764_29766 : List Blob :=
  records29764_29765 ++ records29765_29766
theorem aligned29764_29766 :
    AlignedValid 12 4 missing29764_29766 records29764_29766 :=
  aligned29764_29765.append aligned29765_29766

def missing29766_29767 : List (BitVec (edgeCount 12)) :=
  [missing29766]
abbrev records29766_29767 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29766]
theorem aligned29766_29767 :
    AlignedValid 12 4 missing29766_29767 records29766_29767 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29766
    maskCheck29766 AlignedValid.nil

def missing29767_29768 : List (BitVec (edgeCount 12)) :=
  [missing29767]
abbrev records29767_29768 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29767]
theorem aligned29767_29768 :
    AlignedValid 12 4 missing29767_29768 records29767_29768 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29767
    maskCheck29767 AlignedValid.nil

def missing29766_29768 : List (BitVec (edgeCount 12)) :=
  missing29766_29767 ++ missing29767_29768
abbrev records29766_29768 : List Blob :=
  records29766_29767 ++ records29767_29768
theorem aligned29766_29768 :
    AlignedValid 12 4 missing29766_29768 records29766_29768 :=
  aligned29766_29767.append aligned29767_29768

def missing29764_29768 : List (BitVec (edgeCount 12)) :=
  missing29764_29766 ++ missing29766_29768
abbrev records29764_29768 : List Blob :=
  records29764_29766 ++ records29766_29768
theorem aligned29764_29768 :
    AlignedValid 12 4 missing29764_29768 records29764_29768 :=
  aligned29764_29766.append aligned29766_29768

def missing29760_29768 : List (BitVec (edgeCount 12)) :=
  missing29760_29764 ++ missing29764_29768
abbrev records29760_29768 : List Blob :=
  records29760_29764 ++ records29764_29768
theorem aligned29760_29768 :
    AlignedValid 12 4 missing29760_29768 records29760_29768 :=
  aligned29760_29764.append aligned29764_29768

def missing29768_29769 : List (BitVec (edgeCount 12)) :=
  [missing29768]
abbrev records29768_29769 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29768]
theorem aligned29768_29769 :
    AlignedValid 12 4 missing29768_29769 records29768_29769 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29768
    maskCheck29768 AlignedValid.nil

def missing29769_29770 : List (BitVec (edgeCount 12)) :=
  [missing29769]
abbrev records29769_29770 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29769]
theorem aligned29769_29770 :
    AlignedValid 12 4 missing29769_29770 records29769_29770 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29769
    maskCheck29769 AlignedValid.nil

def missing29768_29770 : List (BitVec (edgeCount 12)) :=
  missing29768_29769 ++ missing29769_29770
abbrev records29768_29770 : List Blob :=
  records29768_29769 ++ records29769_29770
theorem aligned29768_29770 :
    AlignedValid 12 4 missing29768_29770 records29768_29770 :=
  aligned29768_29769.append aligned29769_29770

def missing29770_29771 : List (BitVec (edgeCount 12)) :=
  [missing29770]
abbrev records29770_29771 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29770]
theorem aligned29770_29771 :
    AlignedValid 12 4 missing29770_29771 records29770_29771 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29770
    maskCheck29770 AlignedValid.nil

def missing29771_29772 : List (BitVec (edgeCount 12)) :=
  [missing29771]
abbrev records29771_29772 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29771]
theorem aligned29771_29772 :
    AlignedValid 12 4 missing29771_29772 records29771_29772 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29771
    maskCheck29771 AlignedValid.nil

def missing29770_29772 : List (BitVec (edgeCount 12)) :=
  missing29770_29771 ++ missing29771_29772
abbrev records29770_29772 : List Blob :=
  records29770_29771 ++ records29771_29772
theorem aligned29770_29772 :
    AlignedValid 12 4 missing29770_29772 records29770_29772 :=
  aligned29770_29771.append aligned29771_29772

def missing29768_29772 : List (BitVec (edgeCount 12)) :=
  missing29768_29770 ++ missing29770_29772
abbrev records29768_29772 : List Blob :=
  records29768_29770 ++ records29770_29772
theorem aligned29768_29772 :
    AlignedValid 12 4 missing29768_29772 records29768_29772 :=
  aligned29768_29770.append aligned29770_29772

def missing29772_29773 : List (BitVec (edgeCount 12)) :=
  [missing29772]
abbrev records29772_29773 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29772]
theorem aligned29772_29773 :
    AlignedValid 12 4 missing29772_29773 records29772_29773 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29772
    maskCheck29772 AlignedValid.nil

def missing29773_29774 : List (BitVec (edgeCount 12)) :=
  [missing29773]
abbrev records29773_29774 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29773]
theorem aligned29773_29774 :
    AlignedValid 12 4 missing29773_29774 records29773_29774 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29773
    maskCheck29773 AlignedValid.nil

def missing29772_29774 : List (BitVec (edgeCount 12)) :=
  missing29772_29773 ++ missing29773_29774
abbrev records29772_29774 : List Blob :=
  records29772_29773 ++ records29773_29774
theorem aligned29772_29774 :
    AlignedValid 12 4 missing29772_29774 records29772_29774 :=
  aligned29772_29773.append aligned29773_29774

def missing29774_29775 : List (BitVec (edgeCount 12)) :=
  [missing29774]
abbrev records29774_29775 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29774]
theorem aligned29774_29775 :
    AlignedValid 12 4 missing29774_29775 records29774_29775 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29774
    maskCheck29774 AlignedValid.nil

def missing29775_29776 : List (BitVec (edgeCount 12)) :=
  [missing29775]
abbrev records29775_29776 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29775]
theorem aligned29775_29776 :
    AlignedValid 12 4 missing29775_29776 records29775_29776 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29775
    maskCheck29775 AlignedValid.nil

def missing29774_29776 : List (BitVec (edgeCount 12)) :=
  missing29774_29775 ++ missing29775_29776
abbrev records29774_29776 : List Blob :=
  records29774_29775 ++ records29775_29776
theorem aligned29774_29776 :
    AlignedValid 12 4 missing29774_29776 records29774_29776 :=
  aligned29774_29775.append aligned29775_29776

def missing29772_29776 : List (BitVec (edgeCount 12)) :=
  missing29772_29774 ++ missing29774_29776
abbrev records29772_29776 : List Blob :=
  records29772_29774 ++ records29774_29776
theorem aligned29772_29776 :
    AlignedValid 12 4 missing29772_29776 records29772_29776 :=
  aligned29772_29774.append aligned29774_29776

def missing29768_29776 : List (BitVec (edgeCount 12)) :=
  missing29768_29772 ++ missing29772_29776
abbrev records29768_29776 : List Blob :=
  records29768_29772 ++ records29772_29776
theorem aligned29768_29776 :
    AlignedValid 12 4 missing29768_29776 records29768_29776 :=
  aligned29768_29772.append aligned29772_29776

def missing29760_29776 : List (BitVec (edgeCount 12)) :=
  missing29760_29768 ++ missing29768_29776
abbrev records29760_29776 : List Blob :=
  records29760_29768 ++ records29768_29776
theorem aligned29760_29776 :
    AlignedValid 12 4 missing29760_29776 records29760_29776 :=
  aligned29760_29768.append aligned29768_29776

def missing29776_29777 : List (BitVec (edgeCount 12)) :=
  [missing29776]
abbrev records29776_29777 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29776]
theorem aligned29776_29777 :
    AlignedValid 12 4 missing29776_29777 records29776_29777 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29776
    maskCheck29776 AlignedValid.nil

def missing29777_29778 : List (BitVec (edgeCount 12)) :=
  [missing29777]
abbrev records29777_29778 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29777]
theorem aligned29777_29778 :
    AlignedValid 12 4 missing29777_29778 records29777_29778 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29777
    maskCheck29777 AlignedValid.nil

def missing29776_29778 : List (BitVec (edgeCount 12)) :=
  missing29776_29777 ++ missing29777_29778
abbrev records29776_29778 : List Blob :=
  records29776_29777 ++ records29777_29778
theorem aligned29776_29778 :
    AlignedValid 12 4 missing29776_29778 records29776_29778 :=
  aligned29776_29777.append aligned29777_29778

def missing29778_29779 : List (BitVec (edgeCount 12)) :=
  [missing29778]
abbrev records29778_29779 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29778]
theorem aligned29778_29779 :
    AlignedValid 12 4 missing29778_29779 records29778_29779 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29778
    maskCheck29778 AlignedValid.nil

def missing29779_29780 : List (BitVec (edgeCount 12)) :=
  [missing29779]
abbrev records29779_29780 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29779]
theorem aligned29779_29780 :
    AlignedValid 12 4 missing29779_29780 records29779_29780 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29779
    maskCheck29779 AlignedValid.nil

def missing29778_29780 : List (BitVec (edgeCount 12)) :=
  missing29778_29779 ++ missing29779_29780
abbrev records29778_29780 : List Blob :=
  records29778_29779 ++ records29779_29780
theorem aligned29778_29780 :
    AlignedValid 12 4 missing29778_29780 records29778_29780 :=
  aligned29778_29779.append aligned29779_29780

def missing29776_29780 : List (BitVec (edgeCount 12)) :=
  missing29776_29778 ++ missing29778_29780
abbrev records29776_29780 : List Blob :=
  records29776_29778 ++ records29778_29780
theorem aligned29776_29780 :
    AlignedValid 12 4 missing29776_29780 records29776_29780 :=
  aligned29776_29778.append aligned29778_29780

def missing29780_29781 : List (BitVec (edgeCount 12)) :=
  [missing29780]
abbrev records29780_29781 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29780]
theorem aligned29780_29781 :
    AlignedValid 12 4 missing29780_29781 records29780_29781 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29780
    maskCheck29780 AlignedValid.nil

def missing29781_29782 : List (BitVec (edgeCount 12)) :=
  [missing29781]
abbrev records29781_29782 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29781]
theorem aligned29781_29782 :
    AlignedValid 12 4 missing29781_29782 records29781_29782 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29781
    maskCheck29781 AlignedValid.nil

def missing29780_29782 : List (BitVec (edgeCount 12)) :=
  missing29780_29781 ++ missing29781_29782
abbrev records29780_29782 : List Blob :=
  records29780_29781 ++ records29781_29782
theorem aligned29780_29782 :
    AlignedValid 12 4 missing29780_29782 records29780_29782 :=
  aligned29780_29781.append aligned29781_29782

def missing29782_29783 : List (BitVec (edgeCount 12)) :=
  [missing29782]
abbrev records29782_29783 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29782]
theorem aligned29782_29783 :
    AlignedValid 12 4 missing29782_29783 records29782_29783 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29782
    maskCheck29782 AlignedValid.nil

def missing29783_29784 : List (BitVec (edgeCount 12)) :=
  [missing29783]
abbrev records29783_29784 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29783]
theorem aligned29783_29784 :
    AlignedValid 12 4 missing29783_29784 records29783_29784 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29783
    maskCheck29783 AlignedValid.nil

def missing29782_29784 : List (BitVec (edgeCount 12)) :=
  missing29782_29783 ++ missing29783_29784
abbrev records29782_29784 : List Blob :=
  records29782_29783 ++ records29783_29784
theorem aligned29782_29784 :
    AlignedValid 12 4 missing29782_29784 records29782_29784 :=
  aligned29782_29783.append aligned29783_29784

def missing29780_29784 : List (BitVec (edgeCount 12)) :=
  missing29780_29782 ++ missing29782_29784
abbrev records29780_29784 : List Blob :=
  records29780_29782 ++ records29782_29784
theorem aligned29780_29784 :
    AlignedValid 12 4 missing29780_29784 records29780_29784 :=
  aligned29780_29782.append aligned29782_29784

def missing29776_29784 : List (BitVec (edgeCount 12)) :=
  missing29776_29780 ++ missing29780_29784
abbrev records29776_29784 : List Blob :=
  records29776_29780 ++ records29780_29784
theorem aligned29776_29784 :
    AlignedValid 12 4 missing29776_29784 records29776_29784 :=
  aligned29776_29780.append aligned29780_29784

def missing29784_29785 : List (BitVec (edgeCount 12)) :=
  [missing29784]
abbrev records29784_29785 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29784]
theorem aligned29784_29785 :
    AlignedValid 12 4 missing29784_29785 records29784_29785 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29784
    maskCheck29784 AlignedValid.nil

def missing29785_29786 : List (BitVec (edgeCount 12)) :=
  [missing29785]
abbrev records29785_29786 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29785]
theorem aligned29785_29786 :
    AlignedValid 12 4 missing29785_29786 records29785_29786 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29785
    maskCheck29785 AlignedValid.nil

def missing29784_29786 : List (BitVec (edgeCount 12)) :=
  missing29784_29785 ++ missing29785_29786
abbrev records29784_29786 : List Blob :=
  records29784_29785 ++ records29785_29786
theorem aligned29784_29786 :
    AlignedValid 12 4 missing29784_29786 records29784_29786 :=
  aligned29784_29785.append aligned29785_29786

def missing29786_29787 : List (BitVec (edgeCount 12)) :=
  [missing29786]
abbrev records29786_29787 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29786]
theorem aligned29786_29787 :
    AlignedValid 12 4 missing29786_29787 records29786_29787 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29786
    maskCheck29786 AlignedValid.nil

def missing29787_29788 : List (BitVec (edgeCount 12)) :=
  [missing29787]
abbrev records29787_29788 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29787]
theorem aligned29787_29788 :
    AlignedValid 12 4 missing29787_29788 records29787_29788 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29787
    maskCheck29787 AlignedValid.nil

def missing29786_29788 : List (BitVec (edgeCount 12)) :=
  missing29786_29787 ++ missing29787_29788
abbrev records29786_29788 : List Blob :=
  records29786_29787 ++ records29787_29788
theorem aligned29786_29788 :
    AlignedValid 12 4 missing29786_29788 records29786_29788 :=
  aligned29786_29787.append aligned29787_29788

def missing29784_29788 : List (BitVec (edgeCount 12)) :=
  missing29784_29786 ++ missing29786_29788
abbrev records29784_29788 : List Blob :=
  records29784_29786 ++ records29786_29788
theorem aligned29784_29788 :
    AlignedValid 12 4 missing29784_29788 records29784_29788 :=
  aligned29784_29786.append aligned29786_29788

def missing29788_29789 : List (BitVec (edgeCount 12)) :=
  [missing29788]
abbrev records29788_29789 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29788]
theorem aligned29788_29789 :
    AlignedValid 12 4 missing29788_29789 records29788_29789 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29788
    maskCheck29788 AlignedValid.nil

def missing29789_29790 : List (BitVec (edgeCount 12)) :=
  [missing29789]
abbrev records29789_29790 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29789]
theorem aligned29789_29790 :
    AlignedValid 12 4 missing29789_29790 records29789_29790 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29789
    maskCheck29789 AlignedValid.nil

def missing29788_29790 : List (BitVec (edgeCount 12)) :=
  missing29788_29789 ++ missing29789_29790
abbrev records29788_29790 : List Blob :=
  records29788_29789 ++ records29789_29790
theorem aligned29788_29790 :
    AlignedValid 12 4 missing29788_29790 records29788_29790 :=
  aligned29788_29789.append aligned29789_29790

def missing29790_29791 : List (BitVec (edgeCount 12)) :=
  [missing29790]
abbrev records29790_29791 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29790]
theorem aligned29790_29791 :
    AlignedValid 12 4 missing29790_29791 records29790_29791 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29790
    maskCheck29790 AlignedValid.nil

def missing29791_29792 : List (BitVec (edgeCount 12)) :=
  [missing29791]
abbrev records29791_29792 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29791]
theorem aligned29791_29792 :
    AlignedValid 12 4 missing29791_29792 records29791_29792 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29791
    maskCheck29791 AlignedValid.nil

def missing29790_29792 : List (BitVec (edgeCount 12)) :=
  missing29790_29791 ++ missing29791_29792
abbrev records29790_29792 : List Blob :=
  records29790_29791 ++ records29791_29792
theorem aligned29790_29792 :
    AlignedValid 12 4 missing29790_29792 records29790_29792 :=
  aligned29790_29791.append aligned29791_29792

def missing29788_29792 : List (BitVec (edgeCount 12)) :=
  missing29788_29790 ++ missing29790_29792
abbrev records29788_29792 : List Blob :=
  records29788_29790 ++ records29790_29792
theorem aligned29788_29792 :
    AlignedValid 12 4 missing29788_29792 records29788_29792 :=
  aligned29788_29790.append aligned29790_29792

def missing29784_29792 : List (BitVec (edgeCount 12)) :=
  missing29784_29788 ++ missing29788_29792
abbrev records29784_29792 : List Blob :=
  records29784_29788 ++ records29788_29792
theorem aligned29784_29792 :
    AlignedValid 12 4 missing29784_29792 records29784_29792 :=
  aligned29784_29788.append aligned29788_29792

def missing29776_29792 : List (BitVec (edgeCount 12)) :=
  missing29776_29784 ++ missing29784_29792
abbrev records29776_29792 : List Blob :=
  records29776_29784 ++ records29784_29792
theorem aligned29776_29792 :
    AlignedValid 12 4 missing29776_29792 records29776_29792 :=
  aligned29776_29784.append aligned29784_29792

def missing29760_29792 : List (BitVec (edgeCount 12)) :=
  missing29760_29776 ++ missing29776_29792
abbrev records29760_29792 : List Blob :=
  records29760_29776 ++ records29776_29792
theorem aligned29760_29792 :
    AlignedValid 12 4 missing29760_29792 records29760_29792 :=
  aligned29760_29776.append aligned29776_29792

def missing29792_29793 : List (BitVec (edgeCount 12)) :=
  [missing29792]
abbrev records29792_29793 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29792]
theorem aligned29792_29793 :
    AlignedValid 12 4 missing29792_29793 records29792_29793 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29792
    maskCheck29792 AlignedValid.nil

def missing29793_29794 : List (BitVec (edgeCount 12)) :=
  [missing29793]
abbrev records29793_29794 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29793]
theorem aligned29793_29794 :
    AlignedValid 12 4 missing29793_29794 records29793_29794 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29793
    maskCheck29793 AlignedValid.nil

def missing29792_29794 : List (BitVec (edgeCount 12)) :=
  missing29792_29793 ++ missing29793_29794
abbrev records29792_29794 : List Blob :=
  records29792_29793 ++ records29793_29794
theorem aligned29792_29794 :
    AlignedValid 12 4 missing29792_29794 records29792_29794 :=
  aligned29792_29793.append aligned29793_29794

def missing29794_29795 : List (BitVec (edgeCount 12)) :=
  [missing29794]
abbrev records29794_29795 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29794]
theorem aligned29794_29795 :
    AlignedValid 12 4 missing29794_29795 records29794_29795 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29794
    maskCheck29794 AlignedValid.nil

def missing29795_29796 : List (BitVec (edgeCount 12)) :=
  [missing29795]
abbrev records29795_29796 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29795]
theorem aligned29795_29796 :
    AlignedValid 12 4 missing29795_29796 records29795_29796 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29795
    maskCheck29795 AlignedValid.nil

def missing29794_29796 : List (BitVec (edgeCount 12)) :=
  missing29794_29795 ++ missing29795_29796
abbrev records29794_29796 : List Blob :=
  records29794_29795 ++ records29795_29796
theorem aligned29794_29796 :
    AlignedValid 12 4 missing29794_29796 records29794_29796 :=
  aligned29794_29795.append aligned29795_29796

def missing29792_29796 : List (BitVec (edgeCount 12)) :=
  missing29792_29794 ++ missing29794_29796
abbrev records29792_29796 : List Blob :=
  records29792_29794 ++ records29794_29796
theorem aligned29792_29796 :
    AlignedValid 12 4 missing29792_29796 records29792_29796 :=
  aligned29792_29794.append aligned29794_29796

def missing29796_29797 : List (BitVec (edgeCount 12)) :=
  [missing29796]
abbrev records29796_29797 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29796]
theorem aligned29796_29797 :
    AlignedValid 12 4 missing29796_29797 records29796_29797 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29796
    maskCheck29796 AlignedValid.nil

def missing29797_29798 : List (BitVec (edgeCount 12)) :=
  [missing29797]
abbrev records29797_29798 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29797]
theorem aligned29797_29798 :
    AlignedValid 12 4 missing29797_29798 records29797_29798 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29797
    maskCheck29797 AlignedValid.nil

def missing29796_29798 : List (BitVec (edgeCount 12)) :=
  missing29796_29797 ++ missing29797_29798
abbrev records29796_29798 : List Blob :=
  records29796_29797 ++ records29797_29798
theorem aligned29796_29798 :
    AlignedValid 12 4 missing29796_29798 records29796_29798 :=
  aligned29796_29797.append aligned29797_29798

def missing29798_29799 : List (BitVec (edgeCount 12)) :=
  [missing29798]
abbrev records29798_29799 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29798]
theorem aligned29798_29799 :
    AlignedValid 12 4 missing29798_29799 records29798_29799 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29798
    maskCheck29798 AlignedValid.nil

def missing29799_29800 : List (BitVec (edgeCount 12)) :=
  [missing29799]
abbrev records29799_29800 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29799]
theorem aligned29799_29800 :
    AlignedValid 12 4 missing29799_29800 records29799_29800 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29799
    maskCheck29799 AlignedValid.nil

def missing29798_29800 : List (BitVec (edgeCount 12)) :=
  missing29798_29799 ++ missing29799_29800
abbrev records29798_29800 : List Blob :=
  records29798_29799 ++ records29799_29800
theorem aligned29798_29800 :
    AlignedValid 12 4 missing29798_29800 records29798_29800 :=
  aligned29798_29799.append aligned29799_29800

def missing29796_29800 : List (BitVec (edgeCount 12)) :=
  missing29796_29798 ++ missing29798_29800
abbrev records29796_29800 : List Blob :=
  records29796_29798 ++ records29798_29800
theorem aligned29796_29800 :
    AlignedValid 12 4 missing29796_29800 records29796_29800 :=
  aligned29796_29798.append aligned29798_29800

def missing29792_29800 : List (BitVec (edgeCount 12)) :=
  missing29792_29796 ++ missing29796_29800
abbrev records29792_29800 : List Blob :=
  records29792_29796 ++ records29796_29800
theorem aligned29792_29800 :
    AlignedValid 12 4 missing29792_29800 records29792_29800 :=
  aligned29792_29796.append aligned29796_29800

def missing29800_29801 : List (BitVec (edgeCount 12)) :=
  [missing29800]
abbrev records29800_29801 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29800]
theorem aligned29800_29801 :
    AlignedValid 12 4 missing29800_29801 records29800_29801 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29800
    maskCheck29800 AlignedValid.nil

def missing29801_29802 : List (BitVec (edgeCount 12)) :=
  [missing29801]
abbrev records29801_29802 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29801]
theorem aligned29801_29802 :
    AlignedValid 12 4 missing29801_29802 records29801_29802 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29801
    maskCheck29801 AlignedValid.nil

def missing29800_29802 : List (BitVec (edgeCount 12)) :=
  missing29800_29801 ++ missing29801_29802
abbrev records29800_29802 : List Blob :=
  records29800_29801 ++ records29801_29802
theorem aligned29800_29802 :
    AlignedValid 12 4 missing29800_29802 records29800_29802 :=
  aligned29800_29801.append aligned29801_29802

def missing29802_29803 : List (BitVec (edgeCount 12)) :=
  [missing29802]
abbrev records29802_29803 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29802]
theorem aligned29802_29803 :
    AlignedValid 12 4 missing29802_29803 records29802_29803 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29802
    maskCheck29802 AlignedValid.nil

def missing29803_29804 : List (BitVec (edgeCount 12)) :=
  [missing29803]
abbrev records29803_29804 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29803]
theorem aligned29803_29804 :
    AlignedValid 12 4 missing29803_29804 records29803_29804 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29803
    maskCheck29803 AlignedValid.nil

def missing29802_29804 : List (BitVec (edgeCount 12)) :=
  missing29802_29803 ++ missing29803_29804
abbrev records29802_29804 : List Blob :=
  records29802_29803 ++ records29803_29804
theorem aligned29802_29804 :
    AlignedValid 12 4 missing29802_29804 records29802_29804 :=
  aligned29802_29803.append aligned29803_29804

def missing29800_29804 : List (BitVec (edgeCount 12)) :=
  missing29800_29802 ++ missing29802_29804
abbrev records29800_29804 : List Blob :=
  records29800_29802 ++ records29802_29804
theorem aligned29800_29804 :
    AlignedValid 12 4 missing29800_29804 records29800_29804 :=
  aligned29800_29802.append aligned29802_29804

def missing29804_29805 : List (BitVec (edgeCount 12)) :=
  [missing29804]
abbrev records29804_29805 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29804]
theorem aligned29804_29805 :
    AlignedValid 12 4 missing29804_29805 records29804_29805 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29804
    maskCheck29804 AlignedValid.nil

def missing29805_29806 : List (BitVec (edgeCount 12)) :=
  [missing29805]
abbrev records29805_29806 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29805]
theorem aligned29805_29806 :
    AlignedValid 12 4 missing29805_29806 records29805_29806 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29805
    maskCheck29805 AlignedValid.nil

def missing29804_29806 : List (BitVec (edgeCount 12)) :=
  missing29804_29805 ++ missing29805_29806
abbrev records29804_29806 : List Blob :=
  records29804_29805 ++ records29805_29806
theorem aligned29804_29806 :
    AlignedValid 12 4 missing29804_29806 records29804_29806 :=
  aligned29804_29805.append aligned29805_29806

def missing29806_29807 : List (BitVec (edgeCount 12)) :=
  [missing29806]
abbrev records29806_29807 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29806]
theorem aligned29806_29807 :
    AlignedValid 12 4 missing29806_29807 records29806_29807 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29806
    maskCheck29806 AlignedValid.nil

def missing29807_29808 : List (BitVec (edgeCount 12)) :=
  [missing29807]
abbrev records29807_29808 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29807]
theorem aligned29807_29808 :
    AlignedValid 12 4 missing29807_29808 records29807_29808 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29807
    maskCheck29807 AlignedValid.nil

def missing29806_29808 : List (BitVec (edgeCount 12)) :=
  missing29806_29807 ++ missing29807_29808
abbrev records29806_29808 : List Blob :=
  records29806_29807 ++ records29807_29808
theorem aligned29806_29808 :
    AlignedValid 12 4 missing29806_29808 records29806_29808 :=
  aligned29806_29807.append aligned29807_29808

def missing29804_29808 : List (BitVec (edgeCount 12)) :=
  missing29804_29806 ++ missing29806_29808
abbrev records29804_29808 : List Blob :=
  records29804_29806 ++ records29806_29808
theorem aligned29804_29808 :
    AlignedValid 12 4 missing29804_29808 records29804_29808 :=
  aligned29804_29806.append aligned29806_29808

def missing29800_29808 : List (BitVec (edgeCount 12)) :=
  missing29800_29804 ++ missing29804_29808
abbrev records29800_29808 : List Blob :=
  records29800_29804 ++ records29804_29808
theorem aligned29800_29808 :
    AlignedValid 12 4 missing29800_29808 records29800_29808 :=
  aligned29800_29804.append aligned29804_29808

def missing29792_29808 : List (BitVec (edgeCount 12)) :=
  missing29792_29800 ++ missing29800_29808
abbrev records29792_29808 : List Blob :=
  records29792_29800 ++ records29800_29808
theorem aligned29792_29808 :
    AlignedValid 12 4 missing29792_29808 records29792_29808 :=
  aligned29792_29800.append aligned29800_29808

def missing29808_29809 : List (BitVec (edgeCount 12)) :=
  [missing29808]
abbrev records29808_29809 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29808]
theorem aligned29808_29809 :
    AlignedValid 12 4 missing29808_29809 records29808_29809 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29808
    maskCheck29808 AlignedValid.nil

def missing29809_29810 : List (BitVec (edgeCount 12)) :=
  [missing29809]
abbrev records29809_29810 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29809]
theorem aligned29809_29810 :
    AlignedValid 12 4 missing29809_29810 records29809_29810 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29809
    maskCheck29809 AlignedValid.nil

def missing29808_29810 : List (BitVec (edgeCount 12)) :=
  missing29808_29809 ++ missing29809_29810
abbrev records29808_29810 : List Blob :=
  records29808_29809 ++ records29809_29810
theorem aligned29808_29810 :
    AlignedValid 12 4 missing29808_29810 records29808_29810 :=
  aligned29808_29809.append aligned29809_29810

def missing29810_29811 : List (BitVec (edgeCount 12)) :=
  [missing29810]
abbrev records29810_29811 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29810]
theorem aligned29810_29811 :
    AlignedValid 12 4 missing29810_29811 records29810_29811 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29810
    maskCheck29810 AlignedValid.nil

def missing29811_29812 : List (BitVec (edgeCount 12)) :=
  [missing29811]
abbrev records29811_29812 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29811]
theorem aligned29811_29812 :
    AlignedValid 12 4 missing29811_29812 records29811_29812 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29811
    maskCheck29811 AlignedValid.nil

def missing29810_29812 : List (BitVec (edgeCount 12)) :=
  missing29810_29811 ++ missing29811_29812
abbrev records29810_29812 : List Blob :=
  records29810_29811 ++ records29811_29812
theorem aligned29810_29812 :
    AlignedValid 12 4 missing29810_29812 records29810_29812 :=
  aligned29810_29811.append aligned29811_29812

def missing29808_29812 : List (BitVec (edgeCount 12)) :=
  missing29808_29810 ++ missing29810_29812
abbrev records29808_29812 : List Blob :=
  records29808_29810 ++ records29810_29812
theorem aligned29808_29812 :
    AlignedValid 12 4 missing29808_29812 records29808_29812 :=
  aligned29808_29810.append aligned29810_29812

def missing29812_29813 : List (BitVec (edgeCount 12)) :=
  [missing29812]
abbrev records29812_29813 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29812]
theorem aligned29812_29813 :
    AlignedValid 12 4 missing29812_29813 records29812_29813 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29812
    maskCheck29812 AlignedValid.nil

def missing29813_29814 : List (BitVec (edgeCount 12)) :=
  [missing29813]
abbrev records29813_29814 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29813]
theorem aligned29813_29814 :
    AlignedValid 12 4 missing29813_29814 records29813_29814 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29813
    maskCheck29813 AlignedValid.nil

def missing29812_29814 : List (BitVec (edgeCount 12)) :=
  missing29812_29813 ++ missing29813_29814
abbrev records29812_29814 : List Blob :=
  records29812_29813 ++ records29813_29814
theorem aligned29812_29814 :
    AlignedValid 12 4 missing29812_29814 records29812_29814 :=
  aligned29812_29813.append aligned29813_29814

def missing29814_29815 : List (BitVec (edgeCount 12)) :=
  [missing29814]
abbrev records29814_29815 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29814]
theorem aligned29814_29815 :
    AlignedValid 12 4 missing29814_29815 records29814_29815 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29814
    maskCheck29814 AlignedValid.nil

def missing29815_29816 : List (BitVec (edgeCount 12)) :=
  [missing29815]
abbrev records29815_29816 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29815]
theorem aligned29815_29816 :
    AlignedValid 12 4 missing29815_29816 records29815_29816 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29815
    maskCheck29815 AlignedValid.nil

def missing29814_29816 : List (BitVec (edgeCount 12)) :=
  missing29814_29815 ++ missing29815_29816
abbrev records29814_29816 : List Blob :=
  records29814_29815 ++ records29815_29816
theorem aligned29814_29816 :
    AlignedValid 12 4 missing29814_29816 records29814_29816 :=
  aligned29814_29815.append aligned29815_29816

def missing29812_29816 : List (BitVec (edgeCount 12)) :=
  missing29812_29814 ++ missing29814_29816
abbrev records29812_29816 : List Blob :=
  records29812_29814 ++ records29814_29816
theorem aligned29812_29816 :
    AlignedValid 12 4 missing29812_29816 records29812_29816 :=
  aligned29812_29814.append aligned29814_29816

def missing29808_29816 : List (BitVec (edgeCount 12)) :=
  missing29808_29812 ++ missing29812_29816
abbrev records29808_29816 : List Blob :=
  records29808_29812 ++ records29812_29816
theorem aligned29808_29816 :
    AlignedValid 12 4 missing29808_29816 records29808_29816 :=
  aligned29808_29812.append aligned29812_29816

def missing29816_29817 : List (BitVec (edgeCount 12)) :=
  [missing29816]
abbrev records29816_29817 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29816]
theorem aligned29816_29817 :
    AlignedValid 12 4 missing29816_29817 records29816_29817 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29816
    maskCheck29816 AlignedValid.nil

def missing29817_29818 : List (BitVec (edgeCount 12)) :=
  [missing29817]
abbrev records29817_29818 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29817]
theorem aligned29817_29818 :
    AlignedValid 12 4 missing29817_29818 records29817_29818 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29817
    maskCheck29817 AlignedValid.nil

def missing29816_29818 : List (BitVec (edgeCount 12)) :=
  missing29816_29817 ++ missing29817_29818
abbrev records29816_29818 : List Blob :=
  records29816_29817 ++ records29817_29818
theorem aligned29816_29818 :
    AlignedValid 12 4 missing29816_29818 records29816_29818 :=
  aligned29816_29817.append aligned29817_29818

def missing29818_29819 : List (BitVec (edgeCount 12)) :=
  [missing29818]
abbrev records29818_29819 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29818]
theorem aligned29818_29819 :
    AlignedValid 12 4 missing29818_29819 records29818_29819 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29818
    maskCheck29818 AlignedValid.nil

def missing29819_29820 : List (BitVec (edgeCount 12)) :=
  [missing29819]
abbrev records29819_29820 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29819]
theorem aligned29819_29820 :
    AlignedValid 12 4 missing29819_29820 records29819_29820 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29819
    maskCheck29819 AlignedValid.nil

def missing29818_29820 : List (BitVec (edgeCount 12)) :=
  missing29818_29819 ++ missing29819_29820
abbrev records29818_29820 : List Blob :=
  records29818_29819 ++ records29819_29820
theorem aligned29818_29820 :
    AlignedValid 12 4 missing29818_29820 records29818_29820 :=
  aligned29818_29819.append aligned29819_29820

def missing29816_29820 : List (BitVec (edgeCount 12)) :=
  missing29816_29818 ++ missing29818_29820
abbrev records29816_29820 : List Blob :=
  records29816_29818 ++ records29818_29820
theorem aligned29816_29820 :
    AlignedValid 12 4 missing29816_29820 records29816_29820 :=
  aligned29816_29818.append aligned29818_29820

def missing29820_29821 : List (BitVec (edgeCount 12)) :=
  [missing29820]
abbrev records29820_29821 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29820]
theorem aligned29820_29821 :
    AlignedValid 12 4 missing29820_29821 records29820_29821 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29820
    maskCheck29820 AlignedValid.nil

def missing29821_29822 : List (BitVec (edgeCount 12)) :=
  [missing29821]
abbrev records29821_29822 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29821]
theorem aligned29821_29822 :
    AlignedValid 12 4 missing29821_29822 records29821_29822 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29821
    maskCheck29821 AlignedValid.nil

def missing29820_29822 : List (BitVec (edgeCount 12)) :=
  missing29820_29821 ++ missing29821_29822
abbrev records29820_29822 : List Blob :=
  records29820_29821 ++ records29821_29822
theorem aligned29820_29822 :
    AlignedValid 12 4 missing29820_29822 records29820_29822 :=
  aligned29820_29821.append aligned29821_29822

def missing29822_29823 : List (BitVec (edgeCount 12)) :=
  [missing29822]
abbrev records29822_29823 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29822]
theorem aligned29822_29823 :
    AlignedValid 12 4 missing29822_29823 records29822_29823 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29822
    maskCheck29822 AlignedValid.nil

def missing29823_29824 : List (BitVec (edgeCount 12)) :=
  [missing29823]
abbrev records29823_29824 : List Blob :=
  [StrongPackedBucketN12A4Shard232.record29823]
theorem aligned29823_29824 :
    AlignedValid 12 4 missing29823_29824 records29823_29824 := by
  exact AlignedValid.cons_of_checks StrongPackedBucketN12A4Shard232.check29823
    maskCheck29823 AlignedValid.nil

def missing29822_29824 : List (BitVec (edgeCount 12)) :=
  missing29822_29823 ++ missing29823_29824
abbrev records29822_29824 : List Blob :=
  records29822_29823 ++ records29823_29824
theorem aligned29822_29824 :
    AlignedValid 12 4 missing29822_29824 records29822_29824 :=
  aligned29822_29823.append aligned29823_29824

def missing29820_29824 : List (BitVec (edgeCount 12)) :=
  missing29820_29822 ++ missing29822_29824
abbrev records29820_29824 : List Blob :=
  records29820_29822 ++ records29822_29824
theorem aligned29820_29824 :
    AlignedValid 12 4 missing29820_29824 records29820_29824 :=
  aligned29820_29822.append aligned29822_29824

def missing29816_29824 : List (BitVec (edgeCount 12)) :=
  missing29816_29820 ++ missing29820_29824
abbrev records29816_29824 : List Blob :=
  records29816_29820 ++ records29820_29824
theorem aligned29816_29824 :
    AlignedValid 12 4 missing29816_29824 records29816_29824 :=
  aligned29816_29820.append aligned29820_29824

def missing29808_29824 : List (BitVec (edgeCount 12)) :=
  missing29808_29816 ++ missing29816_29824
abbrev records29808_29824 : List Blob :=
  records29808_29816 ++ records29816_29824
theorem aligned29808_29824 :
    AlignedValid 12 4 missing29808_29824 records29808_29824 :=
  aligned29808_29816.append aligned29816_29824

def missing29792_29824 : List (BitVec (edgeCount 12)) :=
  missing29792_29808 ++ missing29808_29824
abbrev records29792_29824 : List Blob :=
  records29792_29808 ++ records29808_29824
theorem aligned29792_29824 :
    AlignedValid 12 4 missing29792_29824 records29792_29824 :=
  aligned29792_29808.append aligned29808_29824

def missing29760_29824 : List (BitVec (edgeCount 12)) :=
  missing29760_29792 ++ missing29792_29824
abbrev records29760_29824 : List Blob :=
  records29760_29792 ++ records29792_29824
theorem aligned29760_29824 :
    AlignedValid 12 4 missing29760_29824 records29760_29824 :=
  aligned29760_29792.append aligned29792_29824

def missing29696_29824 : List (BitVec (edgeCount 12)) :=
  missing29696_29760 ++ missing29760_29824
abbrev records29696_29824 : List Blob :=
  records29696_29760 ++ records29760_29824
theorem aligned29696_29824 :
    AlignedValid 12 4 missing29696_29824 records29696_29824 :=
  aligned29696_29760.append aligned29760_29824

abbrev missing : List (BitVec (edgeCount 12)) := missing29696_29824
abbrev records : List Blob := records29696_29824
theorem aligned : AlignedValid 12 4 missing records := aligned29696_29824

end Erdos76.CertificateChecker.Certificates.StrongPackedBucketN12A4AlignedShard232
